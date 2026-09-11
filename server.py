#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LAN Chat — локальный чат для работы в локальной сети.

Особенности:
  - Чистый Python 3.5.3+, только стандартная библиотека.
  - Веб-интерфейс и API с одного порта.
  - Обновления в реальном времени через long-polling.
  - Общий чат, приватные сообщения, группы, список онлайн,
    отправка файлов и изображений.
  - Авторизация по логину/паролю (10 пар генерируются при первом
    запуске, на диск пишутся только хэши).
  - Возможность задать собственный ник в чате.

Запуск:
    python3 server.py                # 0.0.0.0:8000
    python3 server.py 0.0.0.0 8080
"""

import binascii
import hashlib
import hmac
import json
import mimetypes
import os
import random
import re
import socket
import socketserver
import string
import sys
import threading
import time
import uuid
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import urlparse, parse_qs, quote

# ---------------------------------------------------------------------------
# Настройки
# ---------------------------------------------------------------------------

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
STATIC_DIR = os.path.join(BASE_DIR, 'static')
UPLOADS_DIR = os.path.join(BASE_DIR, 'uploads')
AUTH_FILE = os.path.join(BASE_DIR, 'auth_users.json')

OFFLINE_TIMEOUT = 30            # сек без пинга -> считаем пользователя оффлайн
POLL_TIMEOUT = 25               # сек максимального ожидания в long-poll
POLL_INTERVAL = 0.3             # сек между проверками внутри poll
MAX_UPLOAD_SIZE = 200 * 1024 * 1024   # 200 MB на файл
MAX_MESSAGES = 5000             # сколько последних сообщений держим в памяти
IMAGE_EXT = ('.jpg', '.jpeg', '.png', '.gif', '.bmp', '.webp', '.svg')

# Логин аккаунта — латиница/цифры/_/- (без пробелов, чтобы не путать
# с ником и не ломать клавиатурный ввод на чужих машинах).
USERNAME_RE = re.compile(r'^[A-Za-z0-9_\-]{2,24}$')
# Ник в чате — можно кириллицу и пробелы.
NAME_RE = re.compile(r'^[A-Za-zА-Яа-яЁё0-9_\-\s]{2,32}$')
GROUP_RE = re.compile(r'^[A-Za-zА-Яа-яЁё0-9_\-\s]{2,32}$')

PBKDF2_ITERATIONS = 200000
ACCOUNT_COUNT = 10
LOGIN_MAX_ATTEMPTS = 5
LOGIN_ATTEMPT_WINDOW = 60

if not os.path.isdir(UPLOADS_DIR):
    os.makedirs(UPLOADS_DIR)

# Заполняется в main() через bootstrap_auth().
AUTH_USERS = {}

# Модуль `secrets` появился только в Python 3.6, а сервер должен работать
# начиная с 3.5.3, поэтому криптографически стойкую случайность берём
# напрямую из os.urandom() через random.SystemRandom (доступен с Python 2.4).
_SYSRAND = random.SystemRandom()


def token_hex(nbytes):
    """Замена secrets.token_hex() для Python < 3.6."""
    return binascii.hexlify(os.urandom(nbytes)).decode('ascii')


def secure_choice(seq):
    """Замена secrets.choice() для Python < 3.6."""
    return _SYSRAND.choice(seq)

# ---------------------------------------------------------------------------
# Общее состояние в памяти.
# ---------------------------------------------------------------------------

STATE_LOCK = threading.RLock()

SESSIONS = {}            # token(str) -> username(str)
USERS = {}               # username -> {'last_seen': float, 'nickname': str}
GROUPS = {}              # groupname -> {'members': set(username), 'owner': username}
MESSAGES = []            # список сообщений по возрастанию id
FILES_META = {}          # stored_filename -> {'type','to','from','original_name'}
_NEXT_ID = [1]


def now():
    return time.time()


def touch_user(username):
    with STATE_LOCK:
        info = USERS.setdefault(username, {'last_seen': 0.0, 'nickname': username})
        info['last_seen'] = now()
        if not info.get('nickname'):
            info['nickname'] = username


def online_usernames():
    cutoff = now() - OFFLINE_TIMEOUT
    with STATE_LOCK:
        return sorted([u for u, info in USERS.items() if info['last_seen'] >= cutoff])


def nicknames_snapshot():
    """username -> nickname для всех известных пользователей. Не только
    онлайн — чтобы клиент мог отображать ник даже в истории."""
    with STATE_LOCK:
        return {u: info.get('nickname', u) for u, info in USERS.items()}


def groups_snapshot(username):
    with STATE_LOCK:
        result = []
        for name, g in GROUPS.items():
            result.append({
                'name': name,
                'owner': g['owner'],
                'members': sorted(g['members']),
                'joined': username in g['members'],
            })
        return sorted(result, key=lambda x: x['name'].lower())


def visible_to(msg, username):
    if msg['type'] == 'broadcast':
        return True
    if msg['type'] == 'private':
        return username in (msg['from'], msg['to'])
    if msg['type'] == 'group':
        g = GROUPS.get(msg['to'])
        return bool(g) and username in g['members']
    return False


def add_message(msg_type, sender, to, text, file_info=None):
    # id и append() — в одном захвате блокировки, чтобы порядок в MESSAGES
    # всегда соответствовал возрастанию id.
    with STATE_LOCK:
        msg_id = _NEXT_ID[0]
        _NEXT_ID[0] += 1
        sender_nick = USERS.get(sender, {}).get('nickname') or sender
        msg = {
            'id': msg_id,
            'type': msg_type,
            'from': sender,
            'from_nick': sender_nick,
            'to': to,
            'text': text or '',
            'file': file_info,
            'ts': now(),
        }
        MESSAGES.append(msg)
        if len(MESSAGES) > MAX_MESSAGES:
            del MESSAGES[:len(MESSAGES) - MAX_MESSAGES]
    return msg


# ---------------------------------------------------------------------------
# Аутентификация
# ---------------------------------------------------------------------------

def hash_password(password, salt_hex):
    salt = bytes.fromhex(salt_hex)
    dk = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), salt, PBKDF2_ITERATIONS)
    return dk.hex()


def make_credential(password):
    salt_hex = token_hex(16)
    return {'salt': salt_hex, 'hash': hash_password(password, salt_hex)}


def verify_password(password, credential):
    if not credential or not password:
        return False
    salt = credential.get('salt', '')
    expected = credential.get('hash', '')
    if not salt or not expected:
        return False
    calculated = hash_password(password, salt)
    return hmac.compare_digest(calculated, expected)


def gen_random_password(length=6):
    """Простой пароль вида «5 цифр + 1 буква»: например 48312k.
    Первый символ не 0, буква — строчная латиница, чтобы не путать
    регистр при вводе с экрана."""
    digits_count = length - 1.
    first = secure_choice(string.digits[1:])           # '1'..'9'
    rest  = ''.join(secure_choice(string.digits) for _ in range(int(digits_count) - 1))
    letter = secure_choice(string.ascii_lowercase)     # 'a'..'z'
    return first + rest + letter


def bootstrap_auth():
    """Загружает учётные записи из AUTH_FILE. Если файла нет — генерирует
    ACCOUNT_COUNT пар логин:пароль, печатает их в консоль ОДИН РАЗ,
    сохраняет на диск только хэши и перезапускает процесс по Enter."""
    if os.path.isfile(AUTH_FILE):
        try:
            with open(AUTH_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if isinstance(data, dict) and data:
                return data
            print('Файл {0} пуст или повреждён, генерирую заново.'.format(AUTH_FILE))
        except (ValueError, OSError) as exc:
            print('Не удалось прочитать {0} ({1}), генерирую заново.'.format(AUTH_FILE, exc))

    creds = {}
    pairs = []
    for i in range(1, ACCOUNT_COUNT + 1):
        username = 'user{0:02d}'.format(i)
        password = gen_random_password()
        creds[username] = make_credential(password)
        pairs.append((username, password))

    with open(AUTH_FILE, 'w', encoding='utf-8') as f:
        json.dump(creds, f, ensure_ascii=False, indent=2)

    print('=' * 60)
    print('Первый запуск: сгенерированы учётные записи для входа в чат.')
    print('Сохраните их прямо сейчас — повторно они не выводятся,')
    print('на диске (в {0}) хранятся только хэши паролей.'.format(AUTH_FILE))
    print('-' * 60)
    for username, password in pairs:
        print('  логин: {0:<10} пароль: {1}'.format(username, password))
    print('-' * 60)
    try:
        input('Нажмите Enter, чтобы перезапустить сервер и начать работу...\n')
    except EOFError:
        pass

    python = sys.executable
    os.execv(python, [python] + sys.argv)


_FAILED_LOGIN_LOCK = threading.Lock()
_FAILED_LOGINS = {}   # ip -> [timestamps]


def register_failed_login(ip):
    with _FAILED_LOGIN_LOCK:
        cutoff = now() - LOGIN_ATTEMPT_WINDOW
        arr = [t for t in _FAILED_LOGINS.get(ip, []) if t >= cutoff]
        arr.append(now())
        _FAILED_LOGINS[ip] = arr
        return len(arr)


def too_many_failed(ip):
    with _FAILED_LOGIN_LOCK:
        cutoff = now() - LOGIN_ATTEMPT_WINDOW
        arr = [t for t in _FAILED_LOGINS.get(ip, []) if t >= cutoff]
        _FAILED_LOGINS[ip] = arr
        return len(arr) >= LOGIN_MAX_ATTEMPTS


# ---------------------------------------------------------------------------
# Разбор multipart/form-data без внешних зависимостей.
# ---------------------------------------------------------------------------

def parse_multipart_formdata(raw, content_type):
    m = re.search(r'boundary="?([^";]+)"?', content_type)
    if not m:
        raise ValueError('no boundary in Content-Type')
    delimiter = b'--' + m.group(1).encode('utf-8')

    fields = {}
    files = {}

    parts = raw.split(delimiter)
    # parts[0] — преамбула, parts[-1] — эпилог (обычно " --\r\n")
    for part in parts[1:-1]:
        if part.startswith(b'\r\n'):
            part = part[2:]
        if part.endswith(b'\r\n'):
            part = part[:-2]
        if b'\r\n\r\n' not in part:
            continue
        header_blob, body = part.split(b'\r\n\r\n', 1)
        headers = header_blob.decode('utf-8', errors='replace')

        disp = re.search(r'Content-Disposition:\s*form-data;([^\r\n]*)', headers, re.IGNORECASE)
        if not disp:
            continue
        params = disp.group(1)
        name_m = re.search(r'name="([^"]*)"', params)
        if not name_m:
            continue
        field_name = name_m.group(1)
        filename_m = re.search(r'filename="([^"]*)"', params)

        if filename_m:
            ctype_m = re.search(r'Content-Type:\s*([^\r\n]+)', headers, re.IGNORECASE)
            files[field_name] = {
                'filename': filename_m.group(1),
                'content_type': ctype_m.group(1).strip() if ctype_m else 'application/octet-stream',
                'data': body,
            }
        else:
            fields[field_name] = body.decode('utf-8', errors='replace')

    return fields, files


# ---------------------------------------------------------------------------
# HTTP-обработчик
# ---------------------------------------------------------------------------

class ChatHandler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'
    server_version = 'LANChat/1.1'

    # ---- вспомогательные методы ---------------------------------------------

    def log_message(self, fmt, *args):
        pass

    def handle(self):
        """Тихо глотаем обрыв соединения клиентом.
        Это норма: браузер/телефон закрывает long-poll запрос раньше,
        чем сервер успевает ответить (перезагрузка вкладки, блокировка
        экрана, уход на другую страницу). Без этой перегрузки
        BaseHTTPRequestHandler печатает огромный traceback на каждый
        такой случай."""
        try:
            super().handle()
        except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
            self.close_connection = True

    def send_json(self, obj, status=200):
        body = json.dumps(obj, ensure_ascii=False).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def read_json(self):
        try:
            length = int(self.headers.get('Content-Length', 0))
        except (TypeError, ValueError):
            length = 0
        raw = self.rfile.read(length) if length else b''
        if not raw:
            return {}
        try:
            return json.loads(raw.decode('utf-8'))
        except ValueError:
            return {}

    def authenticate(self, query=None):
        token = self.headers.get('X-Auth-Token')
        if not token and query:
            vals = query.get('token')
            if vals:
                token = vals[0]
        if not token:
            return None
        with STATE_LOCK:
            username = SESSIONS.get(token)
        if username:
            touch_user(username)
        return username

    # ---- маршрутизация ------------------------------------------------------

    def do_GET(self):
        try:
            self._route_get()
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:
            self._safe_error(exc)

    def do_POST(self):
        try:
            self._route_post()
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:
            self._safe_error(exc)

    def _safe_error(self, exc):
        try:
            self.send_json({'error': 'server_error', 'detail': str(exc)}, 500)
        except Exception:
            pass

    def _route_get(self):
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query)

        if path == '/' or path == '':
            return self.serve_static('index.html')
        if path.startswith('/static/'):
            return self.serve_static(path[len('/static/'):])
        if path.startswith('/files/'):
            return self.serve_uploaded_file(path[len('/files/'):], query)
        if path == '/api/poll':
            return self.handle_poll(query)

        self.send_error(404, 'Not Found')

    def _route_post(self):
        parsed = urlparse(self.path)
        routes = {
            '/api/login': self.handle_login,
            '/api/logout': self.handle_logout,
            '/api/send': self.handle_send,
            '/api/upload': self.handle_upload,
            '/api/nickname': self.handle_set_nickname,
            '/api/groups/create': self.handle_group_create,
            '/api/groups/join': self.handle_group_join,
            '/api/groups/leave': self.handle_group_leave,
        }
        handler = routes.get(parsed.path)
        if handler is None:
            return self.send_error(404, 'Not Found')
        handler()

    # ---- статика --------------------------------------------------------

    def serve_static(self, rel_path):
        rel_path = rel_path or 'index.html'
        full = os.path.normpath(os.path.join(STATIC_DIR, rel_path))
        if not (full == STATIC_DIR or full.startswith(STATIC_DIR + os.sep)):
            return self.send_error(403, 'Forbidden')
        if not os.path.isfile(full):
            return self.send_error(404, 'Not Found')
        ctype, _ = mimetypes.guess_type(full)
        ctype = ctype or 'application/octet-stream'
        with open(full, 'rb') as f:
            data = f.read()
        self.send_response(200)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def serve_uploaded_file(self, stored_name, query):
        stored_name = stored_name.split('?')[0]
        if '/' in stored_name or '\\' in stored_name or '..' in stored_name:
            return self.send_error(400, 'Bad filename')

        username = self.authenticate(query)
        if not username:
            return self.send_error(401, 'Unauthorized')

        # Забираем метаданные и сразу отпускаем блокировку — дальше идёт
        # потенциально долгая отдача файла, под локом ей делать нечего.
        with STATE_LOCK:
            meta = FILES_META.get(stored_name)
            if not meta:
                meta = None
            else:
                pseudo_msg = {'type': meta['type'], 'from': meta['from'], 'to': meta['to']}
                allowed = visible_to(pseudo_msg, username)

        if meta is None:
            return self.send_error(404, 'Not Found')
        if not allowed:
            return self.send_error(403, 'Forbidden')

        full = os.path.join(UPLOADS_DIR, stored_name)
        if not os.path.isfile(full):
            return self.send_error(404, 'Not Found')

        ctype, _ = mimetypes.guess_type(full)
        ctype = ctype or 'application/octet-stream'
        size = os.path.getsize(full)

        self.send_response(200)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(size))
        orig = meta.get('original_name') or stored_name
        ascii_fallback = orig.encode('ascii', 'ignore').decode('ascii').strip() or 'file'
        self.send_header(
            'Content-Disposition',
            'inline; filename="{0}"; filename*=UTF-8\'\'{1}'.format(
                ascii_fallback, quote(orig)
            )
        )
        self.end_headers()
        with open(full, 'rb') as f:
            while True:
                chunk = f.read(65536)
                if not chunk:
                    break
                self.wfile.write(chunk)

    # ---- long-poll --------------------------------------------------------

    def handle_poll(self, query):
        username = self.authenticate(query)
        if not username:
            return self.send_json({'error': 'unauthorized'}, 401)
        try:
            since = int(query.get('since', ['0'])[0])
        except (TypeError, ValueError):
            since = 0

        def state_signature():
            with STATE_LOCK:
                cutoff = now() - OFFLINE_TIMEOUT
                users_sig = tuple(sorted(
                    (u, info.get('nickname', u))
                    for u, info in USERS.items()
                    if info['last_seen'] >= cutoff
                ))
                groups_sig = tuple(sorted(
                    (name, tuple(sorted(g['members'])), g['owner'])
                    for name, g in GROUPS.items()
                ))
            return (users_sig, groups_sig)

        start_sig = state_signature()
        deadline = now() + POLL_TIMEOUT
        payload = None
        while payload is None:
            with STATE_LOCK:
                new_msgs = [m for m in MESSAGES if m['id'] > since and visible_to(m, username)]
                changed = state_signature() != start_sig
                if new_msgs or changed or now() >= deadline:
                    payload = {
                        'messages': new_msgs,
                        'users': online_usernames(),
                        'nicknames': nicknames_snapshot(),
                        'groups': groups_snapshot(username),
                        'you': username,
                    }
            if payload is None:
                time.sleep(POLL_INTERVAL)
        self.send_json(payload)

    # ---- аутентификация -----------------------------------------------------

    def handle_login(self):
        ip = self.client_address[0]
        if too_many_failed(ip):
            return self.send_json(
                {'error': 'too_many_attempts',
                 'message': 'Слишком много неудачных попыток. Попробуйте позже.'}, 429)

        data = self.read_json()
        username = (data.get('username') or '').strip()
        password = data.get('password') or ''
        nickname = (data.get('nickname') or '').strip()

        if not username or not password:
            return self.send_json(
                {'error': 'bad_credentials',
                 'message': 'Укажите логин и пароль'}, 400)

        if not USERNAME_RE.match(username):
            register_failed_login(ip)
            return self.send_json(
                {'error': 'bad_credentials',
                 'message': 'Неверный логин или пароль'}, 401)

        cred = AUTH_USERS.get(username)
        if not cred or not verify_password(password, cred):
            register_failed_login(ip)
            return self.send_json(
                {'error': 'bad_credentials',
                 'message': 'Неверный логин или пароль'}, 401)

        # Если ник не задан — по умолчанию совпадает с логином.
        if not nickname or not NAME_RE.match(nickname):
            nickname = username

        with STATE_LOCK:
            # Уникальность ника среди тех, кто сейчас онлайн.
            for u, info in USERS.items():
                if u == username:
                    continue
                if info['last_seen'] >= now() - OFFLINE_TIMEOUT and info.get('nickname') == nickname:
                    return self.send_json(
                        {'error': 'nickname_taken',
                         'message': 'Этот ник уже занят. Выберите другой.'}, 409)

            token = uuid.uuid4().hex
            SESSIONS[token] = username
            USERS[username] = {'last_seen': now(), 'nickname': nickname}

            payload = {
                'token': token,
                'username': username,
                'nickname': nickname,
                'users': online_usernames(),
                'nicknames': nicknames_snapshot(),
                'groups': groups_snapshot(username),
            }

        self.send_json(payload)

    def handle_logout(self):
        token = self.headers.get('X-Auth-Token')
        with STATE_LOCK:
            username = SESSIONS.pop(token, None)
            # Если у того же аккаунта есть другая активная сессия —
            # не выкидываем его из онлайна.
            if username and username not in SESSIONS.values():
                USERS.pop(username, None)
        self.send_json({'ok': True})

    def handle_set_nickname(self):
        username = self.authenticate()
        if not username:
            return self.send_json({'error': 'unauthorized'}, 401)

        data = self.read_json()
        nickname = (data.get('nickname') or '').strip()
        if not nickname or not NAME_RE.match(nickname):
            return self.send_json(
                {'error': 'bad_nickname',
                 'message': 'Ник: 2-32 символа, буквы/цифры/пробел/_/-'}, 400)

        with STATE_LOCK:
            for u, info in USERS.items():
                if u == username:
                    continue
                if info['last_seen'] >= now() - OFFLINE_TIMEOUT and info.get('nickname') == nickname:
                    return self.send_json(
                        {'error': 'nickname_taken',
                         'message': 'Этот ник уже занят. Выберите другой.'}, 409)
            info = USERS.setdefault(username, {'last_seen': now(), 'nickname': username})
            info['nickname'] = nickname
            info['last_seen'] = now()

        self.send_json({'ok': True, 'nickname': nickname})

    # ---- сообщения ----------------------------------------------------------

    def handle_send(self):
        username = self.authenticate()
        if not username:
            return self.send_json({'error': 'unauthorized'}, 401)

        data = self.read_json()
        msg_type = data.get('type', 'broadcast')
        to = data.get('to')
        text = (data.get('text') or '').strip()

        if not text:
            return self.send_json({'error': 'empty_text'}, 400)
        if len(text) > 4000:
            text = text[:4000]

        err = self._check_target(msg_type, to, username)
        if err:
            return self.send_json({'error': err}, 400)

        msg = add_message(msg_type, username, to, text)
        self.send_json({'ok': True, 'id': msg['id']})

    def _check_target(self, msg_type, to, username):
        if msg_type == 'broadcast':
            return None
        if msg_type == 'private':
            with STATE_LOCK:
                known = to in USERS
            if not to or not known:
                return 'unknown_user'
            return None
        if msg_type == 'group':
            with STATE_LOCK:
                g = GROUPS.get(to)
                member = bool(g) and username in g['members']
            if not member:
                return 'not_group_member'
            return None
        return 'bad_type'

    def handle_upload(self):
        username = self.authenticate()
        if not username:
            return self.send_json({'error': 'unauthorized'}, 401)

        ctype = self.headers.get('Content-Type', '')
        if not ctype.startswith('multipart/form-data'):
            return self.send_json({'error': 'expected_multipart'}, 400)

        try:
            length = int(self.headers.get('Content-Length', 0))
        except (TypeError, ValueError):
            length = 0
        if length > MAX_UPLOAD_SIZE:
            return self.send_json({'error': 'file_too_large'}, 413)
        if length <= 0:
            return self.send_json({'error': 'empty_body'}, 400)

        raw = self.rfile.read(length)
        try:
            fields, files = parse_multipart_formdata(raw, ctype)
        except ValueError:
            return self.send_json({'error': 'bad_multipart'}, 400)

        msg_type = fields.get('type') or 'broadcast'
        to = fields.get('to') or None
        caption = (fields.get('caption') or '').strip()

        err = self._check_target(msg_type, to, username)
        if err:
            return self.send_json({'error': err}, 400)

        if 'file' not in files or not files['file']['filename']:
            return self.send_json({'error': 'no_file'}, 400)

        file_in = files['file']
        original_name = os.path.basename(file_in['filename']) or 'file'
        ext = os.path.splitext(original_name)[1].lower()
        stored_name = uuid.uuid4().hex + ext
        dest_path = os.path.join(UPLOADS_DIR, stored_name)

        with open(dest_path, 'wb') as out:
            out.write(file_in['data'])

        file_info = {
            'stored': stored_name,
            'original_name': original_name,
            'is_image': ext in IMAGE_EXT,
            'size': os.path.getsize(dest_path),
            'url': '/files/' + stored_name,
        }

        with STATE_LOCK:
            FILES_META[stored_name] = {
                'type': msg_type, 'to': to, 'from': username,
                'original_name': original_name,
            }

        msg = add_message(msg_type, username, to, caption, file_info)
        self.send_json({'ok': True, 'id': msg['id']})

    # ---- группы --------------------------------------------------------------

    def handle_group_create(self):
        username = self.authenticate()
        if not username:
            return self.send_json({'error': 'unauthorized'}, 401)
        data = self.read_json()
        name = (data.get('name') or '').strip()
        if not name or not GROUP_RE.match(name):
            return self.send_json({'error': 'bad_name'}, 400)
        with STATE_LOCK:
            if name in GROUPS:
                return self.send_json({'error': 'group_exists'}, 409)
            GROUPS[name] = {'members': set([username]), 'owner': username}
        self.send_json({'ok': True, 'groups': groups_snapshot(username)})

    def handle_group_join(self):
        username = self.authenticate()
        if not username:
            return self.send_json({'error': 'unauthorized'}, 401)
        data = self.read_json()
        name = data.get('name')
        with STATE_LOCK:
            if name not in GROUPS:
                return self.send_json({'error': 'no_such_group'}, 404)
            GROUPS[name]['members'].add(username)
        self.send_json({'ok': True, 'groups': groups_snapshot(username)})

    def handle_group_leave(self):
        username = self.authenticate()
        if not username:
            return self.send_json({'error': 'unauthorized'}, 401)
        data = self.read_json()
        name = data.get('name')
        with STATE_LOCK:
            g = GROUPS.get(name)
            if g:
                g['members'].discard(username)
        self.send_json({'ok': True, 'groups': groups_snapshot(username)})


# ---------------------------------------------------------------------------
# Запуск сервера
# ---------------------------------------------------------------------------

class ThreadingHTTPServer(socketserver.ThreadingMixIn, HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


# --- вместо get_lan_ip() ---

def get_all_local_ips():
    """Возвращает все локальные IPv4 (кроме 127.*). Полезно, когда у ПК
    несколько интерфейсов (Wi-Fi + Ethernet + VPN + Hyper-V) и надо
    показать пользователю все адреса, чтобы он выбрал подходящий."""
    ips = set()

    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(('8.8.8.8', 80))
        ips.add(s.getsockname()[0])
    except OSError:
        pass
    finally:
        s.close()

    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.add(info[4][0])
    except OSError:
        pass

    return sorted(ip for ip in ips if not ip.startswith('127.'))


def main():
    # Заполняем AUTH_USERS до старта сервера. При первом запуске
    # bootstrap_auth() сам сделает os.execv() и до этой точки мы не дойдём.
    AUTH_USERS.update(bootstrap_auth())

    host = sys.argv[1] if len(sys.argv) > 1 else '0.0.0.0'
    port = int(sys.argv[2]) if len(sys.argv) > 2 else 8000

    # --- в main(), замените блок печати ---

    server = ThreadingHTTPServer((host, port), ChatHandler)

    print('=' * 60)
    print('LAN Chat запущен')
    print('На этом компьютере:  http://127.0.0.1:{0}/'.format(port))
    ips = get_all_local_ips()
    if ips:
        print('Из локальной сети (попробуйте по очереди):')
        for ip in ips:
            print('    http://{0}:{1}/'.format(ip, port))
    else:
        print('Локальные IP не найдены — проверьте сетевые подключения.')
    print('Зарегистрировано аккаунтов: {0}'.format(len(AUTH_USERS)))
    print('-' * 60)
    print('Если телефон не подключается:')
    print('  1. Телефон и ПК должны быть в ОДНОЙ Wi-Fi сети,')
    print('     без мобильного интернета и гостевых сетей.')
    print('  2. Разрешите python.exe в брандмауэре Windows')
    print('     (сеть "Частная").')
    print('  3. Убедитесь, что порт {0} не блокируется антивирусом.'.format(port))
    print('-' * 60)
    print('Остановить: Ctrl+C')
    print('=' * 60)

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nОстановка сервера...')
        server.shutdown()


if __name__ == '__main__':
    main()
