"""
بوت تحميل فيديوهات متطور — أزرار ملونة + دعم واسع للمواقع
المحركات: yt-dlp (1700+ موقع) ← تقليد متصفح للمواقع المحمية ← gallery-dl (صور/ألبومات) ← كاشف فيديو في أي صفحة
"""
import os, sys, re, time, uuid, shutil, asyncio, tempfile, sqlite3, threading, logging, json, base64, html
from concurrent.futures import ThreadPoolExecutor
import socket, ipaddress, hashlib, subprocess, urllib.request, urllib.error, copy, inspect
from collections import Counter
from dataclasses import dataclass, field, replace as dc_replace
from urllib.parse import urlparse, urljoin

import yt_dlp
from yt_dlp.extractor import list_extractor_classes
from pyrogram import Client, filters, idle
from pyrogram.errors import MessageNotModified, FloodWait, BadRequest
from pyrogram.enums import MessageEntityType, ParseMode, ChatMemberStatus
from pyrogram.types import InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto
try:
    from pyrogram.enums import ChatAction
except ImportError:
    ChatAction = None
from datetime import datetime as _dt
try:
    from zoneinfo import ZoneInfo
    _TZ = ZoneInfo(os.getenv("BOT_TZ", "Africa/Cairo"))
except Exception:      # مفيش tzdata في الصورة: نستخدم UTC+2 تقريبيًا
    _TZ = None
try:
    from pyrogram.types import BotCommand, BotCommandScopeChat
except ImportError:      # إصدار مكتبة قديم: قائمة الأوامر / بتتخطى بدل ما البوت يقع
    BotCommand = BotCommandScopeChat = None
import fastio

try:
    from pyrogram.enums import ButtonStyle as S
    COLORS = True
except ImportError:
    COLORS = False
    class S: PRIMARY = SUCCESS = DANGER = None

try:
    import gallery_dl.extractor as gdx
    HAS_GALLERY = shutil.which("gallery-dl") is not None
except ImportError:
    gdx, HAS_GALLERY = None, False

IMPERSONATE = None   # تقليد متصفح Chrome لتخطي حماية Cloudflare وأخواتها
try:
    import curl_cffi  # noqa: F401
    from yt_dlp.networking.impersonate import ImpersonateTarget
    IMPERSONATE = ImpersonateTarget.from_str("chrome")
except Exception:
    pass

# yt-dlp بيحاول يكتب الكوكيز تاني في الملف عند كل تحميل؛ مع تحميلات متزامنة ده بيبوّظ الملف، فنمنع الكتابة.
try:
    from yt_dlp.cookies import YoutubeDLCookieJar as _CJ
    _CJ.save = lambda self, *a, **k: None
except Exception:
    pass

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("vidbot")
PROCESS_STARTED_AT = time.monotonic()

try:    # event loop أسرع (لازم يتفعّل قبل إنشاء الـ Client)
    import uvloop
    asyncio.set_event_loop_policy(uvloop.EventLoopPolicy())
    HAS_UVLOOP = True
except Exception:
    HAS_UVLOOP = False

# ───────────── الإعدادات ─────────────
_missing = [k for k in ("API_ID", "API_HASH", "BOT_TOKEN") if not os.environ.get(k, "").strip()]
if _missing:
    raise SystemExit("❌ متغيرات ناقصة: " + ", ".join(_missing) + " — ضيفها في Variables وأعد النشر.")
API_ID = int(os.environ["API_ID"])
API_HASH = os.environ["API_HASH"]
BOT_TOKEN = os.environ["BOT_TOKEN"]
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip()}
# مفيش حدود تطبيقية للتحميل: الدفعات والقوائم والروابط والتزامن بلا سقف.
MAX_PLAYLIST = MAX_GALLERY = 0
TRANSFER_PROFILE = os.getenv("TRANSFER_PROFILE", "fast").strip().lower()
CONN = int(os.getenv("CONNECTIONS", "28"))
FRAGMENTS = int(os.getenv("FRAGMENTS", "28"))
UPLOAD_WORKERS = int(os.getenv("UPLOAD_WORKERS", "20"))
UPLOAD_SESSIONS = int(os.getenv("UPLOAD_SESSIONS", "6"))      # جلسات Media منفصلة للرفع المتوازي
DEV_USERNAME = os.getenv("DEV_USERNAME", "A7med19_7").strip().lstrip("@")
DEV_LABEL = "𝐷𝑒𝑣: @" + DEV_USERNAME
COBALT_API_URL = os.getenv("COBALT_API_URL", "").strip().rstrip("/")   # اختياري: سيرفر تحميل خارجي (cobalt)
COBALT_API_KEY = os.getenv("COBALT_API_KEY", "").strip()
VIDKRAKEN_API_KEY = os.getenv("VIDKRAKEN_API_KEY", "").strip()   # اختياري: خدمة vidkraken.com (يوتيوب بس) كاحتياطي
VIDKRAKEN_URL = "https://vidkraken.com/api/v2"
if TRANSFER_PROFILE == "fast":
    # يضمن تطبيق السرعة الجديدة حتى لو كانت متغيرات Railway القديمة أقل.
    CONN, FRAGMENTS, UPLOAD_WORKERS = max(CONN, 24), max(FRAGMENTS, 24), max(UPLOAD_WORKERS, 16)
def _mem_limit_mb():
    """حد الرام للحاوية (cgroup) بالميجا، أو None لو مش معروف."""
    for path in ("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"):
        try:
            raw = open(path, encoding="ascii").read().strip()
            if raw and raw != "max" and 0 < int(raw) < (1 << 60): return int(raw) // 1048576
        except (OSError, ValueError): pass
    return None

# ضبط تلقائي للاستضافات الصغيرة (الباقة المجانية): اتصالات أقل = ثبات أعلى وسرعة فعلية أحسن بدل كراش/خنق.
# يتعطّل بـ AUTO_TUNE=0 أو لو حددت القيم بنفسك مع TRANSFER_PROFILE=custom.
MEM_MB = _mem_limit_mb()
SMALL_HOST = os.getenv("AUTO_TUNE", "1") != "0" and MEM_MB is not None and MEM_MB <= 1100
if SMALL_HOST:
    UPLOAD_WORKERS, UPLOAD_SESSIONS = min(UPLOAD_WORKERS, 12), min(UPLOAD_SESSIONS, 4)
    CONN, FRAGMENTS = min(CONN, 16), min(FRAGMENTS, 16)
DEFAULT_THREADS = 32 if SMALL_HOST else 128
# البوت عام افتراضيًا؛ لا حصة أو حد لطول الفيديو المسجل.
def _env_int(name, default):
    """رقم صحيح من متغير بيئة (فاضي/غلط = الافتراضي). 0 في حدود التزامن معناها بلا سقف."""
    try: return max(0, int(float((os.getenv(name) or "").strip() or default)))
    except ValueError: return default

# ── حدود التزامن (v12): بدل "بلا سقف" اللي كان بيسقّط البوت لما ناس كتير تبعت مع بعض ──
# بتتظبط تلقائيًا حسب رام الحاوية، وتقدر تغيّرها من Variables. 0 = بلا سقف (زي v11).
MAX_DL = _env_int("MAX_DOWNLOADS", 3 if SMALL_HOST else 8)           # تنزيلات على السيرفر في نفس اللحظة
MAX_UP = _env_int("MAX_UPLOADS", 3 if SMALL_HOST else 6)            # رفع/بث مباشر لتليجرام في نفس اللحظة
MAX_PER_USER = _env_int("MAX_PER_USER", 2 if SMALL_HOST else 4)      # عناصر شغّالة لنفس المستخدم
MAX_PROBES = _env_int("MAX_PROBES", 4 if SMALL_HOST else 12)         # فحوصات روابط (yt-dlp) متزامنة
PROBE_TTL = _env_int("PROBE_TTL", 600)                               # ثواني كاش نتيجة الفحص (0 = إيقاف)
PROBE_CACHE_MAX = 48 if SMALL_HOST else 128
MIN_FREE_MB = _env_int("MIN_FREE_MB", 300)                           # أقل مساحة فاضية قبل بدء تنزيل جديد
ALLOWED_IDS = {int(x) for x in os.getenv("ALLOWED_USERS", "").split(",") if x.strip()}
MAX_SIZE = 2000 * 1024 * 1024
DB_PATH = os.getenv("DB_PATH") or ("/data/bot.db" if os.path.isdir("/data") else "bot.db")
# مواقع محجوبة (محتوى مخالف لقواعد تليجرام). القايمة الأساسية ثابتة في الكود،
# ومتغير BLOCKED_DOMAINS (فاصلة) بيضيف عليها بس — مينفعش يتلغي الحجب بمتغير.
_DEFAULT_BLOCK = ("pornhub.com,xvideos.com,xnxx.com,xhamster.com,redtube.com,youporn.com,"
                  "spankbang.com,tube8.com,eporner.com,motherless.com")
BLOCKED = tuple(dict.fromkeys(
    x.strip().lower() for x in (_DEFAULT_BLOCK + "," + os.getenv("BLOCKED_DOMAINS", "")).split(",") if x.strip()))
VALID_PREFS = {"ask", "best", "1080", "720", "480", "360", "audio"}
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/124.0.0.0 Safari/537.36")

HAS_ARIA2 = shutil.which("aria2c") is not None
SITE_COUNT = sum(1 for _ in list_extractor_classes())

def tune_upload(workers):
    """يرفع عدد طلبات الرفع المتوازية للملف الكبير (المكتبة ثابتة على 4) — أكبر تأثير على سرعة الرفع."""
    try:
        import pyrogram.methods.advanced.save_file as sf
        src, old = inspect.getsource(sf), "workers_count = 4 if is_big else 1"
        if old not in src:
            log.warning("upload tuning skipped: pattern not found (library version changed)")
            return False
        ns = {"__name__": sf.__name__ + "_tuned", "__file__": sf.__file__}
        exec(compile(src.replace(old, f"workers_count = {int(workers)} if is_big else 1"), sf.__file__, "exec"), ns)
        Client.save_file = ns["SaveFile"].save_file
        return True
    except Exception as e:
        log.warning("upload tuning failed: %s", e)
        return False

UPLOAD_TUNED = tune_upload(UPLOAD_WORKERS) if UPLOAD_WORKERS > 4 else False
# رفع متوازي على عدة جلسات + بث مباشر من المصدر (fastio.py). بيتعطّل من لوحة الأدمن (cfg "fast_up").
fastio.configure(workers=UPLOAD_WORKERS, sessions=UPLOAD_SESSIONS)
fastio.install(Client, lambda: cfg("fast_up") == "1")

class UnlimitedSemaphore:
    """واجهة semaphore بلا سقف؛ تمرير acquire لا ينتظر ولا يحجز موردًا."""
    async def acquire(self): return True
    def release(self): pass
    def locked(self): return False
    async def __aenter__(self): return self
    async def __aexit__(self, exc_type, exc, tb): return False

UNLIMITED = UnlimitedSemaphore()

# نستبدل semaphores الداخلية للمكتبة أيضًا حتى لا يبقى سقف تزامن مخفي.
app = Client("vidbot", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN,
             in_memory=True, workers=32, max_concurrent_transmissions=1)
app.save_file_semaphore = UNLIMITED
app.get_file_semaphore = UNLIMITED

class Gate:
    """semaphore حقيقي بسقف (n>0)، أو بلا سقف (n=0). بيعدّ الشغّال والمنتظر عشان التنضيف والمراقبة."""
    def __init__(self, n):
        self.n = int(n)
        self._sem = asyncio.Semaphore(self.n) if self.n > 0 else None
        self.active = 0
        self.waiting = 0
    async def __aenter__(self):
        if self._sem is not None:
            self.waiting += 1
            try: await self._sem.acquire()
            finally: self.waiting -= 1
        self.active += 1
        return self
    async def __aexit__(self, exc_type, exc, tb):
        self.active -= 1
        if self._sem is not None: self._sem.release()
        return False
    def locked(self): return self._sem is not None and self.active >= self.n

DL_SEM, UP_SEM, PROBE_SEM = Gate(MAX_DL), Gate(MAX_UP), Gate(MAX_PROBES)
_USER_GATES = {}

def user_sem(uid):
    """سقف لكل مستخدم عشان واحد مايستهلكش السيرفر لوحده."""
    if MAX_PER_USER <= 0: return UNLIMITED
    g = _USER_GATES.get(uid)
    if g is None: g = _USER_GATES[uid] = Gate(MAX_PER_USER)
    return g

def prune_user_gates():
    for uid, g in list(_USER_GATES.items()):
        if g.active == 0 and g.waiting == 0: _USER_GATES.pop(uid, None)
URL_RE = re.compile(r"https?://[^\s<>\"']+")
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")

# ───────────── قاعدة البيانات ─────────────
try: os.makedirs(os.path.dirname(os.path.abspath(DB_PATH)), exist_ok=True)
except OSError as _e: log.warning("cannot create DB dir: %s", _e)
COOKIE_FILE = os.path.join(os.path.dirname(os.path.abspath(DB_PATH)), "cookies.txt")
PROXY = os.getenv("PROXY", "").strip()

def has_cookies():
    try: return os.path.getsize(COOKIE_FILE) > 50
    except OSError: return False

def cookies_info(path):
    """(إجمالي الكوكيز, كوكيز يوتيوب/جوجل, فيها جلسة دخول؟)"""
    from yt_dlp.cookies import YoutubeDLCookieJar
    jar = YoutubeDLCookieJar(path)
    jar.load(ignore_discard=True, ignore_expires=True)
    total = yt = 0; login = False
    for c in jar:
        total += 1
        if "youtube.com" in c.domain or "google.com" in c.domain:
            yt += 1
            if c.name in ("SID", "__Secure-1PSID", "__Secure-3PSID", "LOGIN_INFO", "SAPISID"): login = True
    return total, yt, login

def save_cookies_text(raw):
    """بيتحقق من ملف الكوكيز (Netscape) ويحفظه. بيرجّع (نجاح, رسالة)."""
    raw = (raw or "").replace("\r\n", "\n").replace("\r", "\n").strip()
    if not raw: return False, "الملف فاضي"
    if not raw.lstrip().startswith("# Netscape") and not raw.lstrip().startswith("# HTTP Cookie File"):
        raw = "# Netscape HTTP Cookie File\n" + raw
    tmp = COOKIE_FILE + ".new"
    try:
        with open(tmp, "w", encoding="utf-8") as f: f.write(raw + "\n")
        total, yt, login = cookies_info(tmp)
        if total == 0:
            os.remove(tmp); return False, "مقدرتش أقرا أي كوكيز — لازم الملف يكون بصيغة Netscape (cookies.txt)"
        os.replace(tmp, COOKIE_FILE)
        try: os.chmod(COOKIE_FILE, 0o600)
        except OSError: pass
        try: PROBE_CACHE.clear()          # الكوكيز اتغيّرت: نتايج الفحص القديمة ممكن تبقى غلط
        except NameError: pass
        return True, f"{total} كوكي ({yt} ليوتيوب/جوجل)" + ("" if login else " ⚠️ مفيش جلسة تسجيل دخول جواهم")
    except Exception as e:
        try: os.remove(tmp)
        except OSError: pass
        return False, f"ملف غير صالح: {str(e)[:80]}"

def seed_cookies_from_env():
    """COOKIES_B64 (أو COOKIES_TXT) من Variables بتتكتب مرة لما قيمتها تتغير؛ رفع الأدمن من البوت بيفضل شغال بعدها."""
    try:
        b64, txt = os.getenv("COOKIES_B64", "").strip(), os.getenv("COOKIES_TXT", "")
        data = base64.b64decode(b64).decode("utf-8", "ignore") if b64 else txt.replace("\\n", "\n")
        if not data.strip(): return
        sig = hashlib.sha1(data.encode()).hexdigest()
        marker = COOKIE_FILE + ".envsig"
        if os.path.exists(marker) and open(marker).read().strip() == sig and has_cookies(): return
        ok, msg = save_cookies_text(data)
        log.info("cookies from env: %s", msg if ok else "rejected - " + msg)
        if ok:
            with open(marker, "w") as f: f.write(sig)
    except Exception as e:
        log.warning("cookies env ignored: %s", e)

seed_cookies_from_env()
db = sqlite3.connect(DB_PATH, check_same_thread=False)
db_lock = threading.Lock()
for _pragma in ("PRAGMA journal_mode=WAL", "PRAGMA synchronous=NORMAL", "PRAGMA busy_timeout=5000",
                "PRAGMA temp_store=MEMORY"):
    try: db.execute(_pragma)
    except sqlite3.DatabaseError: pass
db.executescript("""
CREATE TABLE IF NOT EXISTS cache(key TEXT, mode TEXT, file_id TEXT, PRIMARY KEY(key, mode));
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, first_seen INTEGER,
                                 downloads INTEGER DEFAULT 0, quality TEXT DEFAULT 'ask');
CREATE TABLE IF NOT EXISTS history(user_id INTEGER, title TEXT, mode TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS banned(id INTEGER PRIMARY KEY);
CREATE TABLE IF NOT EXISTS usage(user_id INTEGER, day TEXT, n INTEGER DEFAULT 0, PRIMARY KEY(user_id, day));
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS allowed(id INTEGER PRIMARY KEY);
CREATE TABLE IF NOT EXISTS urlmap(url TEXT PRIMARY KEY, key TEXT, title TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS prefs(user_id INTEGER, key TEXT, value TEXT, PRIMARY KEY(user_id, key));
CREATE TABLE IF NOT EXISTS favorites(user_id INTEGER, url TEXT, title TEXT, ts INTEGER, PRIMARY KEY(user_id, url));
CREATE TABLE IF NOT EXISTS watch(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, url TEXT, title TEXT,
                                 seen TEXT, mode TEXT, ts INTEGER, UNIQUE(user_id, url));
""")
# فهارس (v12): السجل/الحصة/التقارير كانت بتعمل full scan على جدول history كل مرة
for _idx in ("CREATE INDEX IF NOT EXISTS idx_history_user_ts ON history(user_id, ts DESC)",
             "CREATE INDEX IF NOT EXISTS idx_history_ts ON history(ts)",
             "CREATE INDEX IF NOT EXISTS idx_urlmap_ts ON urlmap(ts)"):
    try: db.execute(_idx); db.commit()
    except sqlite3.DatabaseError: pass
for _alter in ("ALTER TABLE users ADD COLUMN quality TEXT DEFAULT 'ask'",
               "ALTER TABLE cache ADD COLUMN ts INTEGER DEFAULT 0",
               "ALTER TABLE history ADD COLUMN url TEXT DEFAULT ''",
               "ALTER TABLE watch ADD COLUMN kw TEXT DEFAULT ''"):
    try:
        db.execute(_alter); db.commit()
    except sqlite3.OperationalError:
        pass

# نسخة في الذاكرة من قوائم الحظر/المسموح (بدل استعلام قاعدة بيانات مع كل رسالة وكل ضغطة زرار)
BANNED = {r[0] for r in db.execute("SELECT id FROM banned")}
ALLOWED_DB = {r[0] for r in db.execute("SELECT id FROM allowed")}

def db_exec(q, args=()):
    with db_lock:
        cur = db.execute(q, args); db.commit(); return cur.fetchall()

# ───────────── إعدادات الأدمن (بتتغير من لوحة الأدمن وبتتخزن في القاعدة) ─────────────
# قيم المتغيرات (Variables) هنا هي القيم الابتدائية بس؛ أي تغيير من اللوحة بيتخزن ويغلب عليها.
SETTING_DEFAULTS = {
    "public": "1",                               # عام افتراضيًا؛ يمكن تغييره يدويًا من لوحة الأدمن
    "wm_on": "0",                               # العلامة المائية شغّالة؟
    "wm_type": "text",                          # text | image
    "wm_text": "", "wm_img_sig": "",
    "wm_pos": "br",                             # tl | tr | bl | br | c
    "wm_size": "M",                             # S | M | L
    "pe_on": "0", "pe_map": "{}",               # إيموجي بريميوم
    # ── تحكم الأدمن المتقدم (كلها بتتغير من 🛠 لوحة الأدمن) ──
    "xfer": "direct",       # direct = بث مباشر من المصدر لما يمكن | disk = تنزيل على السيرفر ثم رفع (القديم)
    "fast_up": "1",         # رفع متوازي متعدد الجلسات
    "max_mb": "0",          # أقصى حجم ملف بالميجا (0 = الحد الأقصى لتليجرام 2GB)
    "max_min": "0",         # أقصى مدة فيديو بالدقايق (0 = بلا حد)
    "max_h": "0",           # أعلى جودة مسموحة (0 = بلا حد)
    "quota": "0",           # حصة المستخدم اليومية (0 = بلا حد)
    "pl_on": "1", "pl_max": "0",   # القوائم: مسموحة؟ / أقصى عدد عناصر (0 = بلا حد)
    "mp3_on": "1",          # خيار الصوت MP3
    "title_link": "1",      # عنوان الفيديو رابط للأصل (يوتيوب فقط)
    "cap_site": "1",        # الكابشن: اسم الموقع 📍
    "cap_chan": "1",        # الكابشن: اسم القناة 👤
    "cap_dur": "1",         # الكابشن: مدة الفيديو ⏱
    "cap_qual": "1",        # الكابشن: الجودة 📺
    "thumb_on": "1",        # صورة الفيديو المصغرة الأصلية
    "dev_btn": "1",         # زر المطور تحت كل فيديو
    "cover": "1",           # صورة الغلاف مع رسالة الترحيب
    "cover_fid": "",        # file_id لصورة الغلاف بعد أول إرسال (للإرسال الفوري)
    "maint": "0",           # وضع الصيانة (الأدمن بس يستخدم البوت)
    "fsub": "",             # قناة الاشتراك الإجباري (@channel) — فاضي = مقفول
    "blk_extra": "",        # مواقع محظورة إضافية (من اللوحة)، مفصولة بفاصلة
    "watch_kw": "تانية بكلوريا",   # فلتر العنوان الافتراضي للقنوات الجديدة (كلمات لازم كلها تكون في العنوان؛ فاصلة = بدائل). فاضي = كل الفيديوهات
    "mp4_pref": "auto",     # auto = لو فيه ملف MP4 جاهز بنفس الجودة (أو أعلى) يتحمّل هو بدل فيديو+صوت+دمج
    "spd_dl": "0", "spd_up": "0", "spd_ts": "0",   # آخر سرعات متوسطة (بايت/ث) للتنزيل والرفع، بتتحدّث من التحميلات الحقيقية و/speed
}
CFG = dict(SETTING_DEFAULTS)
CFG.update({k: v for k, v in db.execute("SELECT key, value FROM settings") if k in SETTING_DEFAULTS})
# إزالة القفل القديم مرة واحدة: يرجع البوت عامًا بعد التحديث، وبعدها يظل زر الأدمن قابلًا للتغيير.
if not db_exec("SELECT value FROM settings WHERE key=?", ("public_access_reset_v1",)):
    CFG["public"] = "1"
    db_exec("INSERT OR REPLACE INTO settings(key, value) VALUES (?,?)", ("public", "1"))
    db_exec("INSERT OR REPLACE INTO settings(key, value) VALUES (?,?)", ("public_access_reset_v1", "done"))

def cfg(key):
    return CFG[key]

def cfg_set(key, val):
    CFG[key] = str(val)
    db_exec("INSERT OR REPLACE INTO settings(key, value) VALUES (?,?)", (key, str(val)))

def cfg_int(key):
    try: return max(0, int(float(CFG[key] or 0)))
    except (TypeError, ValueError): return 0

# خيارات اللوحة: key → (عنوان, [(قيمة, اسمها)]). الضغطة على الزرار بتلف على القيم بالترتيب.
ADMIN_OPTS = {
    "xfer":       ("🚀 وضع الإرسال", [("direct", "⚡ مباشر من المصدر"), ("disk", "💾 عبر السيرفر")]),
    "fast_up":    ("⚡ الرفع المتوازي", [("1", "✅ شغّال"), ("0", "⛔ مقفول")]),
    "max_mb":     ("📏 أقصى حجم", [("0", "♾ 2GB"), ("50", "50MB"), ("100", "100MB"), ("300", "300MB"),
                                    ("500", "500MB"), ("1000", "1GB"), ("1500", "1.5GB")]),
    "max_min":    ("⏱ أقصى مدة", [("0", "♾ بلا حد"), ("5", "5د"), ("15", "15د"), ("30", "30د"),
                                    ("60", "ساعة"), ("120", "ساعتين"), ("240", "4 ساعات")]),
    "max_h":      ("📺 أعلى جودة", [("0", "♾ بلا حد"), ("2160", "4K"), ("1080", "1080p"), ("720", "720p"),
                                    ("480", "480p"), ("360", "360p")]),
    "quota":      ("🔢 الحصة اليومية", [("0", "♾ بلا حد"), ("3", "3"), ("5", "5"), ("10", "10"),
                                         ("20", "20"), ("50", "50"), ("100", "100")]),
    "pl_on":      ("📋 القوائم", [("1", "✅ مسموحة"), ("0", "⛔ ممنوعة")]),
    "pl_max":     ("📋 أقصى عناصر القائمة", [("0", "♾ بلا حد"), ("5", "5"), ("10", "10"), ("25", "25"),
                                              ("50", "50"), ("100", "100")]),
    "mp4_pref":   ("📦 MP4 جاهز بدل الدمج", [("auto", "✅ لو بنفس الجودة"), ("off", "⛔ مقفول")]),
    "mp3_on":     ("🎧 MP3", [("1", "✅ متاح"), ("0", "⛔ مقفول")]),
    "title_link": ("🔗 رابط العنوان (يوتيوب)", [("1", "✅ شغّال"), ("0", "⛔ مقفول")]),
    "cap_site":   ("📍 الموقع في الكابشن", [("1", "✅ ظاهر"), ("0", "⛔ مخفي")]),
    "cap_chan":   ("👤 القناة في الكابشن", [("1", "✅ ظاهرة"), ("0", "⛔ مخفية")]),
    "cap_dur":    ("⏱ المدة في الكابشن", [("1", "✅ ظاهرة"), ("0", "⛔ مخفية")]),
    "cap_qual":   ("📺 الجودة في الكابشن", [("1", "✅ ظاهرة"), ("0", "⛔ مخفية")]),
    "thumb_on":   ("🖼 الصورة المصغرة", [("1", "✅ شغّالة"), ("0", "⛔ مقفولة")]),
    "dev_btn":    ("👨‍💻 زر المطور تحت الفيديو", [("1", "✅ ظاهر"), ("0", "⛔ مخفي")]),
    "cover":      ("🖼 صورة الغلاف", [("1", "✅ شغّالة"), ("0", "⛔ مقفولة")]),
    "maint":      ("🛠 وضع الصيانة", [("0", "⛔ مقفول"), ("1", "🚧 شغّال")]),
}

def opt_next(key):
    vals = [v for v, _ in ADMIN_OPTS[key][1]]
    cur = CFG[key]
    return vals[(vals.index(cur) + 1) % len(vals)] if cur in vals else vals[0]

def opt_label(key):
    cur = CFG[key]
    for v, name in ADMIN_OPTS[key][1]:
        if v == cur: return name
    return cur

def max_size():
    """أقصى حجم ملف مسموح بالبايت (حد تليجرام 2GB، والأدمن يقدر ينزّله)."""
    mb = cfg_int("max_mb")
    return min(MAX_SIZE, mb * 1024 * 1024) if mb else MAX_SIZE

def clamp_mode(mode):
    """يطبّق حد الجودة والـ MP3 اللي ضابطهم الأدمن على اختيار المستخدم."""
    cap = cfg_int("max_h")
    if mode == "audio" or not cap: return mode
    if mode == "best": return str(cap)
    try: return str(min(int(mode), cap))
    except ValueError: return mode

def cache_get(key, mode):
    r = db_exec("SELECT file_id FROM cache WHERE key=? AND mode=?", (key, mode))
    return r[0][0] if r else None

def cache_put(key, mode, fid):
    db_exec("INSERT OR REPLACE INTO cache(key, mode, file_id, ts) VALUES (?,?,?,?)",
            (key, mode, fid, int(time.time())))

def urlmap_get(url):
    """يعيد مفتاح الكاش وعنوان الرابط السابق إن وُجدا؛ ما زال metadata يُفحص قبل عرض الاختيارات."""
    r = db_exec("SELECT m.key, m.title FROM urlmap m WHERE m.url=? "
                "AND EXISTS (SELECT 1 FROM cache c WHERE c.key = m.key)", (url,))
    return r[0] if r else None

def urlmap_put(url, key, title):
    db_exec("INSERT OR REPLACE INTO urlmap(url, key, title, ts) VALUES (?,?,?,?)",
            (url[:500], key, (title or "")[:100], int(time.time())))

def touch_user(uid):
    db_exec("INSERT OR IGNORE INTO users(id, first_seen) VALUES (?,?)", (uid, int(time.time())))

def record(uid, title, mode, url=""):
    db_exec("UPDATE users SET downloads = downloads + 1 WHERE id=?", (uid,))
    db_exec("INSERT INTO history(user_id, title, mode, ts, url) VALUES (?,?,?,?,?)",
            (uid, title[:80], mode, int(time.time()), (url or "")[:1000]))

def clean_stale_tmp(max_age=3600):
    """بقايا تحميلات اتقطعت (Crash / إعادة تشغيل) — بتتمسح عشان القرص ما يمتلاش."""
    tmp, now = tempfile.gettempdir(), time.time()
    for n in os.listdir(tmp):
        if not n.startswith(("dl_", "speed_")): continue
        path = os.path.join(tmp, n)
        try:
            if now - os.path.getmtime(path) > max_age:
                shutil.rmtree(path, ignore_errors=True) if os.path.isdir(path) else os.remove(path)
        except OSError:
            pass

def get_pref(uid):
    r = db_exec("SELECT quality FROM users WHERE id=?", (uid,))
    return (r[0][0] if r and r[0][0] else "ask")

def set_pref(uid, q):
    if q not in VALID_PREFS: return
    db_exec("UPDATE users SET quality=? WHERE id=?", (q, uid))

# ───────────── الموديلات ─────────────
@dataclass
class Item:
    url: str
    title: str
    key: str
    engine: str = "ytdlp"     # ytdlp | gallery
    referer: str = ""
    status: str = "wait"      # wait | dl | up | done | err
    detail: str = ""
    info: object = field(default=None, repr=False)   # نتيجة الفحص (بتتستخدم تاني عشان نوفر استخراج تاني)
    est: float = 0.0          # الوقت المتوقع بالثواني (بيتحسب أول ما التحميل يبدأ)
    t0: float = 0.0           # وقت بداية العنصر
    size: int = 0             # الحجم الفعلي بالبايت
    v_dl: float = 0.0         # سرعة التنزيل الفعلية بايت/ث
    v_up: float = 0.0         # سرعة الرفع الفعلية بايت/ث
    took: float = 0.0         # الزمن الكلي الفعلي بالثواني
    route: str = ""           # direct | disk | cache

@dataclass
class Batch:
    id: str
    user_id: int
    chat_id: int
    items: list
    mode: str = "720"
    cancelled: bool = False
    done: bool = False
    started: bool = False
    started_at: float = 0.0
    msg: object = None
    preview: object = None        # رسالة صورة المعاينة (بتتمسح بعد التحميل)
    sem: UnlimitedSemaphore = field(default_factory=lambda: UNLIMITED)
    created: float = field(default_factory=time.time)
    sequential: bool = False      # واحد ورا التاني بالترتيب (القوائم/الروابط المتعددة)
    sel: set = field(default_factory=set)   # أرقام العناصر المختارة (شاشة الاختيار)
    page: int = 0
    pref: str = "ask"             # الجودة الافتراضية للمستخدم وقت إنشاء الدفعة
    ptitle: str = ""              # عنوان القائمة

batches: dict[str, Batch] = {}
awaiting: dict[int, str] = {}
bc_pending: dict[int, tuple] = {}

# رسائل أخطاء مفهومة بالعربي
ERR_MAP = [
    (r"too many users have viewed|download quota", "⏳ ملف درايف وصل حد التحميل اليومي — حاول بعد شوية أو انسخه لدرايفك"),
    (r"cannot retrieve the public link|anyone with the link|gdown_missing", "🔒 الملف مش متاح للعامة — لازم المشاركة تكون «أي شخص معه الرابط»"),
    (r"sign in to confirm|not a bot", "🤖 يوتيوب طلب التحقق إنك مش روبوت (بيحصل مع IP الاستضافات). صاحب البوت لازم يرفع كوكيز يوتيوب جديدة من لوحة الأدمن 🍪 ← كوكيز يوتيوب."),
    (r"private video|video is private|this account is private", "🔒 الفيديو/الحساب خاص"),
    (r"confirm your age|age[- ]restricted|inappropriate for some users", "🔞 الفيديو مقيّد بالعمر ولا يمكن تحميله في الوضع المجهول"),
    (r"login required|log in|logged in|rate-limit reached|requires? authentication|cookies", "🔑 المحتوى يتطلب تسجيل دخول، والتنزيل المجهول غير متاح له"),
    (r"\bdrm\b|widevine", "🛡 محمي بـ DRM ومينفعش يتحمل"),
    (r"geo[- ]?restrict|not available in your country|blocked .* in your country", "🌍 محجوب في بلد السيرفر"),
    (r"live event|is live|premieres in|will begin in", "📡 ده بث مباشر/لسه ما بدأش — حاول لما يخلص"),
    (r"unsupported url|no video|there is no video|no media|مفيش فيديو", "🔎 مفيش فيديو قابل للتحميل في الرابط ده"),
    (r"unavailable|removed|deleted|does not exist|not found|404", "🗑 الفيديو مش متاح أو اتحذف"),
    (r"429|too many requests", "⏳ الموقع حظر السيرفر مؤقتًا — حاول بعد شوية"),
    (r"timed out|timeout", "⏱ الموقع اتأخر في الرد — حاول تاني"),
]

def clean_err(e):
    s = ANSI_RE.sub("", str(e)).replace("ERROR:", "").strip()
    for rx, msg in ERR_MAP:
        if re.search(rx, s, re.I): return msg
    return "⚠️ " + s[:150].replace("<", "‹").replace(">", "›")

def mode_label(m):
    return {"best": "أعلى جودة", "audio": "MP3", "ask": "اسألني كل مرة"}.get(m, f"{m}p")

def is_admin(uid):
    return uid in ADMIN_IDS

def is_banned(uid):
    return uid in BANNED

def is_whitelisted(uid):
    return uid in ALLOWED_IDS or uid in ALLOWED_DB

def is_allowed(uid):
    if uid in ADMIN_IDS: return True
    if is_banned(uid): return False
    return cfg("public") == "1" or is_whitelisted(uid)

def extra_blocked():
    return tuple(x.strip().lower() for x in cfg("blk_extra").split(",") if x.strip())

def is_blocked(url):
    host = (urlparse(url).hostname or "").lower()
    return any(host == d or host.endswith("." + d) for d in BLOCKED + extra_blocked())

def in_maintenance(uid):
    return cfg("maint") == "1" and uid not in ADMIN_IDS

MAINT_TEXT = "🚧 البوت في صيانة دلوقتي — جرّب بعد شوية."

_sub_cache = {}      # uid → وقت آخر تحقق ناجح

async def sub_required(uid):
    """بيرجّع اسم القناة لو المستخدم لازم يشترك فيها قبل الاستخدام، وإلا None. أي خطأ تحقق = نسمح (بدون تعطيل البوت)."""
    ch = cfg("fsub").strip()
    if not ch or uid in ADMIN_IDS: return None
    if time.time() - _sub_cache.get(uid, 0) < 600: return None
    try:
        mem = await app.get_chat_member(ch, uid)
        if mem.status not in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED):
            _sub_cache[uid] = time.time(); return None
        return ch
    except Exception as e:
        err = str(e)
        if "USER_NOT_PARTICIPANT" in err: return ch
        log.warning("force-sub check failed for %s (%s) — allowing", ch, e)
        return None

def sub_kb(ch):
    link = "https://t.me/" + ch.lstrip("@")
    return KB([U("📢 اشترك في القناة", link, S.SUCCESS)], [B("✅ اشتركت — تحقق", "fs", S.PRIMARY)])

def is_safe_url(url):
    """يمنع الروابط الداخلية (localhost / الشبكة الخاصة / metadata) عشان السيرفر ما يتستغلش.
    بيتطبق على: رابط المستخدم، وكل رابط بيتلقط من جوه صفحة، وكل Redirect بنتبعه بنفسنا."""
    try:
        p = urlparse(url)
        if p.scheme not in ("http", "https") or not p.hostname: return False
        for *_, sa in socket.getaddrinfo(p.hostname, None):
            ip = ipaddress.ip_address(sa[0].split("%")[0])
            if getattr(ip, "ipv4_mapped", None): ip = ip.ipv4_mapped
            if not ip.is_global or ip.is_multicast:      # is_global بتغطي private/loopback/link-local/CGNAT/reserved
                return False
        return True
    except Exception:
        return False

def url_ok(url):
    return is_safe_url(url) and not is_blocked(url)

# ───────────── إيموجي بريميوم ─────────────
PE = {"on": False, "map": {}, "pat": None, "broken": False}

def _norm_emoji(x): return x.replace("\ufe0f", "").strip()

def pe_reload():
    try: m = json.loads(cfg("pe_map") or "{}")
    except ValueError: m = {}
    PE["map"] = {k: str(v) for k, v in m.items() if k}
    PE["on"] = cfg("pe_on") == "1" and bool(PE["map"])
    keys = sorted(PE["map"], key=len, reverse=True)
    PE["pat"] = re.compile("(" + "|".join(re.escape(k) for k in keys) + ")\ufe0f?") if keys else None

def pe_active(): return PE["on"] and not PE["broken"] and PE["pat"] is not None

def pe_html(text):
    if not text or not pe_active(): return text
    return PE["pat"].sub(lambda m: f'<emoji id="{PE["map"][m.group(1)]}">{m.group(1)}</emoji>', text)

def pe_button(text):
    """لو الزرار بيبدأ بإيموجي مربوط ببريميوم: (id, النص من غير الإيموجي)."""
    if not pe_active(): return None, text
    m = PE["pat"].match(text)
    if not m: return None, text
    return PE["map"][m.group(1)], text[m.end():].lstrip()

def plainify_kb(kb):
    try:
        for row in kb.inline_keyboard:
            for btn in row:
                orig = getattr(btn, "pe_orig", None)
                if orig: btn.icon_custom_emoji_id = None; btn.text = orig
    except Exception: pass

# ───────────── الأزرار الملونة ─────────────
def B(text, data, style=S.PRIMARY):
    kw = {}
    if COLORS and style is not None: kw["style"] = style
    icon, label = pe_button(text)
    if icon and label: kw["icon_custom_emoji_id"] = icon
    else: label = text
    btn = InlineKeyboardButton(label, callback_data=data, **kw)
    if icon and label: btn.pe_orig = text
    return btn

def U(text, url, style=S.PRIMARY):
    """زر رابط (بيفتح URL)."""
    kw = {"url": url}
    if COLORS and style is not None: kw["style"] = style
    return InlineKeyboardButton(text, **kw)

def dev_button():
    return U(DEV_LABEL, f"https://t.me/{DEV_USERNAME}", S.PRIMARY)

def KB(*rows):
    return InlineKeyboardMarkup([list(r) for r in rows])

def media_kb():
    """الكيبورد اللي بيتحط تحت الفيديو المُرسَل (زر المطور) — بيتحكم فيه الأدمن."""
    return KB([dev_button()]) if cfg("dev_btn") == "1" else None

def menu_kb(uid):
    rows = [
        [B("➕ تحميل فيديو أو صور", "dl", S.SUCCESS)],
        [B("📜 السجل", "me|h|a|0"), B("⭐ المفضلة", "me|f|0")],
        [B("📊 تحميلاتي", "me"), B("⚙️ الإعدادات", "st")],
        [B("🔔 مراقبة القنوات", "wt|ls"), B("🌐 المواقع", "sites")],
        [B("❓ المساعدة", "hp")],
    ]
    if is_admin(uid):
        rows.append([B("🛠 لوحة الأدمن", "ad", S.DANGER)])
    rows.append([dev_button()])
    return KB(*rows)

def back_kb():
    return KB([B("🏠 القائمة الرئيسية", "m")], [dev_button()])

def duration_text(value):
    try:
        seconds = max(0, int(float(value)))
    except (TypeError, ValueError, OverflowError):
        return "غير متاح"
    hours, rem = divmod(seconds, 3600)
    minutes, seconds = divmod(rem, 60)
    return f"{hours}:{minutes:02d}:{seconds:02d}" if hours else f"{minutes}:{seconds:02d}"

_EXACT = {}          # url الصيغة -> الحجم الحقيقي (Content-Length) لما الموقع ما يعلنش filesize

def _is_exact(fmt):
    try:
        if int(float(fmt.get("filesize") or 0)) > 0: return True
    except (TypeError, ValueError, OverflowError):
        pass
    return bool(_EXACT.get(fmt.get("url")))

def _format_size(fmt, duration):
    try:
        value = int(float(fmt.get("filesize") or 0))
        if value > 0: return value
    except (TypeError, ValueError, OverflowError):
        pass
    value = _EXACT.get(fmt.get("url"))
    if value: return value
    try:
        value = int(float(fmt.get("filesize_approx") or 0))
        if value > 0: return value
    except (TypeError, ValueError, OverflowError):
        pass
    try:
        bitrate = float(fmt.get("tbr") or fmt.get("abr") or 0)
        seconds = float(duration or 0)
        if bitrate > 0 and seconds > 0:
            return int(bitrate * 1000 * seconds / 8)
    except (TypeError, ValueError, OverflowError):
        pass
    return None

def _format_height(fmt):
    """دقة الصيغة = أقصر ضلع (1080x1920 الطولي = 1080p مش 1920p) — نفس تعريف yt-dlp للـ res."""
    try:
        w, h = int(fmt.get("width") or 0), int(fmt.get("height") or 0)
    except (TypeError, ValueError, OverflowError):
        return 0
    return min(w, h) if w > 0 and h > 0 else max(h, 0)

def _format_rank(fmt):
    height = _format_height(fmt)
    try: bitrate = float(fmt.get("tbr") or fmt.get("abr") or 0)
    except (TypeError, ValueError): bitrate = 0
    try: fps = float(fmt.get("fps") or 0)
    except (TypeError, ValueError): fps = 0
    h264 = str(fmt.get("vcodec") or "").startswith("avc1")
    return height, h264, bitrate, fps

def quality_modes(info):
    formats = (info.get("formats") or []) if isinstance(info, dict) else []
    heights = []
    for fmt in formats:
        if not isinstance(fmt, dict) or fmt.get("vcodec") in (None, "none"): continue
        height = _format_height(fmt)
        if height > 0: heights.append(height)
    if not heights: return ["best", "1080", "720", "480", "360"]
    # لا نعرض 720p مثلاً إذا كانت الصيغ الفعلية 1080p و360p فقط؛
    # عرض الزر يجب أن يطابق أقصر ضلع للصيغة التي سيختارها yt-dlp فعلياً.
    return ["best"] + [str(height) for height in sorted(set(heights), reverse=True)]

def audio_available(info):
    if not isinstance(info, dict) or not info.get("formats"): return True
    # acodec غير معروف (None، زي روابط mp4 المباشرة) معناه إن الصوت ممكن يكون موجود؛ "none" بس هي اللي معناها مفيش صوت
    return any(isinstance(f, dict) and f.get("acodec") != "none"
               for f in info.get("formats") or [])

def thumbnail_url(info):
    if not isinstance(info, dict): return None
    url = info.get("thumbnail")
    if isinstance(url, str) and url.startswith("https://"): return url
    thumbnails = [t for t in (info.get("thumbnails") or [])
                  if isinstance(t, dict) and isinstance(t.get("url"), str) and t["url"].startswith("https://")]
    if not thumbnails: return None
    def rank(t):
        try: return int(t.get("width") or 0) * int(t.get("height") or 0)
        except (TypeError, ValueError, OverflowError): return 0
    return max(thumbnails, key=rank)["url"]

_SEL_CACHE = {}
_SEL_EXACT = {}

def _head_size(fmt):
    """HEAD سريع للحصول على الحجم الحقيقي للصيغة (بس للروابط المباشرة، مش HLS/DASH)."""
    url = fmt.get("url")
    if not isinstance(url, str) or not url.startswith("https://") or url in _EXACT: return
    if str(fmt.get("protocol") or "") not in ("https", "http"): return
    if _is_exact(fmt) or not is_safe_url(url): return
    try:
        import requests
        h = dict(fmt.get("http_headers") or {})
        r = requests.head(url, headers=h, allow_redirects=True, timeout=4)
        n = int(r.headers.get("Content-Length") or 0)
        if r.status_code < 400 and n > 0: _EXACT[url] = n
    except Exception as e:
        log.debug("HEAD size failed: %s", e)

def warm_exact_sizes(info):
    """بيجيب الأحجام الحقيقية لكل الجودات بالتوازي قبل ما نعرض الأزرار (بحد أقصى ~4 ثواني)."""
    if not isinstance(info, dict): return
    try:
        todo = {}
        for mode in quality_modes(info):
            for f in (selected_formats(info, clamp_mode(mode)) or []):
                if not _is_exact(f) and f.get("url"): todo[f["url"]] = f
        if not todo: return
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(min(8, len(todo))) as ex:
            list(ex.map(_head_size, list(todo.values())[:24]))
        if len(_EXACT) > 2000: _EXACT.clear()
    except Exception as e:
        log.debug("warm sizes failed: %s", e)

def pick_format(info, mode):
    """بيفضّل ملف MP4 جاهز (فيديو+صوت في ملف واحد، من غير دمج) لو جودته مش أقل من أفضل اختيار مدموج. بدون شبكة."""
    base = fmt_for(mode)
    if mode == "audio" or cfg("mp4_pref") != "auto" or not isinstance(info, dict) or not info.get("formats"):
        return base
    try:
        full = _select(info, base, mode)
        if not full or len(full) < 2: return base              # أصلًا ملف واحد
        prog_fmt = progressive_fmt(mode)
        prog = _select(info, prog_fmt, mode)
        if prog and len(prog) == 1:
            hv = lambda fs: max((_format_height(f) for f in fs if f.get("vcodec") not in (None, "none")), default=0)
            if hv(prog) >= hv(full): return prog_fmt
    except Exception as e:
        log.debug("pick_format failed: %s", e)
    return base

def selected_formats(info, mode):
    return _select(info, pick_format(info, mode), mode)

def _select(info, fmt, mode):
    """الصيغ اللي yt-dlp هيختارها فعليًا للـ format ده (نفس خيارات التحميل بالظبط) — بدون شبكة."""
    o = {"quiet": True, "no_warnings": True, "format": fmt}
    srt = sort_for(mode)
    if srt: o["format_sort"] = srt
    with yt_dlp.YoutubeDL(o) as y:
        res = y.process_ie_result(copy.deepcopy(info), download=False)
    got = [f for f in (res.get("requested_formats") or [res]) if isinstance(f, dict)]
    if not got or not any(f.get("url") or f.get("format_id") for f in got): return None
    return got

def selection_summary(info, mode):
    """(الحجم التقديري بالبايت أو None، الدقة الفعلية المختارة أو 0) — متخزّنة مؤقتًا."""
    if not isinstance(info, dict): return None, 0
    key = (info.get("extractor_key"), info.get("id"), mode, size_filter())
    if key in _SEL_CACHE: return _SEL_CACHE[key]
    size, res = None, 0
    try:
        chosen = selected_formats(info, mode)
        if chosen:
            parts = [_format_size(f, info.get("duration")) for f in chosen]
            if all(p is not None for p in parts):
                size = sum(parts)
                _SEL_EXACT[key] = all(_is_exact(f) for f in chosen)
            res = max((_format_height(f) for f in chosen if f.get("vcodec") not in (None, "none")), default=0)
    except Exception as e:
        log.debug("selection summary failed for %s: %s", mode, e)
    if len(_SEL_CACHE) > 300: _SEL_CACHE.clear(); _SEL_EXACT.clear()
    if info.get("id"): _SEL_CACHE[key] = (size, res)
    return size, res

def estimated_size(info, mode):
    if not isinstance(info, dict): return None
    duration = info.get("duration")
    if mode == "audio":
        try:
            seconds = float(duration or 0)
            return int(seconds * 192000 / 8) if seconds > 0 else None
        except (TypeError, ValueError, OverflowError):
            return None
    size, _ = selection_summary(info, mode)
    if size: return size
    target = None if mode == "best" else int(mode)
    formats = [f for f in (info.get("formats") or []) if isinstance(f, dict)]
    def has_video(f): return f.get("vcodec") not in (None, "none")
    def has_audio(f): return f.get("acodec") not in (None, "none")
    video = [f for f in formats if has_video(f) and f.get("height")]
    if target is not None:
        video = [f for f in video if _format_height(f) <= target]
    if not video: return None
    video.sort(key=_format_rank, reverse=True)
    separate_video = [f for f in video if not has_audio(f)]
    combined = [f for f in video if has_audio(f)]
    if separate_video:
        vfmt = separate_video[0]
        audio = [f for f in formats if has_audio(f) and not has_video(f)]
        audio.sort(key=_format_rank, reverse=True)
        vsize = _format_size(vfmt, duration)
        asize = _format_size(audio[0], duration) if audio else None
        if vsize is not None and asize is not None: return vsize + asize
    if combined:
        combined.sort(key=_format_rank, reverse=True)
        return _format_size(combined[0], duration)
    return None

# ───────────── قياس السرعة والوقت المتوقع ─────────────
DEFAULT_DL, DEFAULT_UP = 12e6, 10e6      # قيم أولية (بايت/ث) لحد ما يتقاس أول تحميل حقيقي
_spd_saved = {"at": 0.0}

def speed_get(kind):
    """متوسط السرعة المحفوظ (بايت/ث) أو القيمة الأولية. kind: dl | up"""
    try: v = float(CFG.get("spd_" + kind) or 0)
    except (TypeError, ValueError): v = 0.0
    return v if v > 0 else (DEFAULT_DL if kind == "dl" else DEFAULT_UP)

def speed_known():
    return float(CFG.get("spd_dl") or 0) > 0 or float(CFG.get("spd_up") or 0) > 0

def speed_note(kind, bps, nbytes=0, force=False):
    """يسجّل عينة سرعة حقيقية في المتوسط المتحرك (EMA). العينات الصغيرة/الغريبة بتتجاهل."""
    try: bps, nbytes = float(bps), float(nbytes)
    except (TypeError, ValueError): return
    if bps < 50e3 or bps > 600e6 or (nbytes and nbytes < 4 * 1048576 and not force): return
    old = float(CFG.get("spd_" + kind) or 0)
    new = bps if old <= 0 else 0.7 * old + 0.3 * bps
    CFG["spd_" + kind] = str(int(new))
    now = time.time()
    if force or now - _spd_saved["at"] > 20:        # ما نكتبش في DB كل عينة
        _spd_saved["at"] = now
        for k in ("spd_dl", "spd_up"):
            try: db_exec("INSERT OR REPLACE INTO settings(key, value) VALUES (?,?)", (k, CFG[k]))
            except Exception: pass
        cfg_set("spd_ts", int(now))

def estimate_seconds(info, mode):
    """الوقت المتوقع (ثواني) لتحميل ورفع الجودة دي، من الحجم التقديري وآخر سرعات متوسطة. None لو الحجم مجهول."""
    size = estimated_size(info, clamp_mode(mode)) if isinstance(info, dict) else None
    if not size: return None
    dl, up = speed_get("dl"), speed_get("up")
    merged = False
    try:
        got = selected_formats(info, clamp_mode(mode)) if mode != "audio" else None
        merged = bool(got and len(got) > 1)
    except Exception:
        pass
    if cfg("xfer") == "direct" and not merged:
        t = size / max(min(dl, up), 1.0)                  # بث مباشر: بياخد وقت أبطأ طرف
    else:
        t = size / max(dl, 1.0) + size / max(up, 1.0)     # تنزيل ثم رفع
        if merged: t += size / 150e6 + 1.5                # دمج بدون إعادة ترميز (سريع)
    return t + 2.0                                        # تهيئة الاتصال

def short_time(seconds):
    s = max(0, int(round(seconds)))
    return f"{s}ث" if s < 60 else f"{s // 60}د {s % 60:02}ث"

def speed_line():
    dl, up = speed_get("dl"), speed_get("up")
    src = "" if speed_known() else " (تقدير أولي — اضغط /speed)"
    return f"⬇️ {dl / 1e6:.1f} • ⬆️ {up / 1e6:.1f} MB/s{src}"

def quality_button_label(info, mode):
    if mode == "best": label = "🏆 أعلى جودة"
    elif mode == "audio": label = "🎧 MP3"
    else:
        try: h_ = int(mode)
        except (TypeError, ValueError): h_ = 0
        icon = "💎" if h_ >= 1440 else "🔥" if h_ >= 1080 else "✨" if h_ >= 720 else "📺" if h_ >= 480 else "📱"
        label = f"{icon} {'4K' if h_ >= 2160 else str(h_) + 'p'}"
    eff = clamp_mode(mode)
    if mode == "best" and eff == "best" and isinstance(info, dict):
        res = selection_summary(info, "best")[1]
        if res: label += f" ({res}p)"
    size = estimated_size(info, eff)
    if not size: return label
    key = (info.get("extractor_key"), info.get("id"), eff, size_filter()) if isinstance(info, dict) else None
    approx = "" if (key and _SEL_EXACT.get(key)) else "~"
    out = f"{label} · {approx}{human_bytes(size)}"
    try:
        est = estimate_seconds(info, eff)
        if est: out += f" · ⏱{short_time(est)}"
    except Exception as e:
        log.debug("estimate failed: %s", e)
    return out

def picker_kb(bid, info=None):
    modes = quality_modes(info) if info else ["best", "1080", "720", "480", "360"]
    cap = cfg_int("max_h")
    rows = [[B(quality_button_label(info, "best"), f"q|{bid}|best", S.SUCCESS)]]
    video_modes = [m for m in modes if m != "best" and (not cap or int(m) <= cap)]
    for i in range(0, len(video_modes), 2):
        rows.append([B(quality_button_label(info, m), f"q|{bid}|{m}") for m in video_modes[i:i + 2]])
    if audio_available(info) and cfg("mp3_on") == "1":
        rows.append([B(quality_button_label(info, "audio"), f"q|{bid}|audio")])
    rows.append([B("❌ إلغاء", f"x|{bid}", S.DANGER)])
    return KB(*rows)

def metadata_text(items, playlist_title=None):
    if len(items) != 1 or items[0].engine != "ytdlp" or not items[0].info:
        bullets = [f"• {esc_t(item.title, 55)}" for item in items[:6]]
        if len(items) > 6: bullets.append(f"… و{len(items) - 6} كمان")
        return (ui_title("🎬", f"لقيت {len(items)} عنصر", esc_t(playlist_title, 120) if playlist_title else "") + "\n"
                + ui_quote(*bullets) + "\n\n👇 <b>اختار الجودة</b>\n<i>هتتطبق على كل العناصر</i>")
    item, info = items[0], items[0].info
    site = site_of(item.url)
    who = esc_t(info.get("uploader") or info.get("channel") or "", 40)
    heights = sorted({_format_height(f) for f in (info.get("formats") or [])
                      if isinstance(f, dict) and _format_height(f) and f.get("vcodec") not in (None, "none")}, reverse=True)
    def _n(v):
        try: v = float(v)
        except (TypeError, ValueError): return ""
        for lim, suf in ((1e9, "B"), (1e6, "M"), (1e3, "K")):
            if v >= lim: return f"{v / lim:.1f}".rstrip("0").rstrip(".") + suf
        return str(int(v))
    ud = str(info.get("upload_date") or "")
    date = f"{ud[:4]}-{ud[4:6]}-{ud[6:8]}" if len(ud) == 8 and ud.isdigit() else ""
    views = _n(info.get("view_count"))
    line1 = " • ".join(x for x in (f"📍 {esc_t(site)}" if site else "", f"👤 {who}" if who else "") if x)
    line2 = " • ".join(x for x in (f"⏱ {duration_text(info.get('duration'))}", f"👁 {views}" if views else "",
                                   f"📅 {date}" if date else "") if x)
    line3 = ("📺 " + " · ".join(f"{h}p" for h in heights[:9])) if heights else ""
    if audio_available(info): line3 += ("  " if line3 else "") + "🎧 MP3"
    return (f"🎬 <b>{esc_t(info.get('title') or item.title or 'فيديو', 110)}</b>\n{LINE}\n"
            + ui_quote(line1, line2, line3)
            + "\n\n👇 <b>اختر الجودة</b>  <i>(~ = حجم تقريبي • ⏱ = الوقت المتوقع للوصول)</i>"
            + f"\n<i>🚀 {speed_line()}</i>")

def _escape_metadata_title(value, limit):
    text = " ".join(str(value or "").split())[:limit]
    return re.sub(r"([_*`\[\]])", r"\\\1", text)

def cancel_kb(b):
    return KB([B("⏹ إيقاف التنزيل", f"c|{b.id}", S.DANGER)])

def after_kb():
    return KB([B("➕ تحميل جديد", "dl", S.SUCCESS)], [B("📊 تحميلاتي", "me"), B("🏠 القائمة", "m")], [dev_button()])

def settings_text(uid):
    return (ui_title("⚙️", "الإعدادات", "خصّص البوت على مزاجك") + "\n"
            + ui_quote(f"🎞 الجودة الافتراضية: <b>{mode_label(get_pref(uid))}</b>")
            + "\n\n<i>💡 لو اخترت جودة، البوت هيبدأ التحميل فورًا من غير ما يسألك.</i>")

def settings_kb(uid):
    cur = get_pref(uid)
    def mk(v, label):
        sel = v == cur
        return B(("✅ " if sel else "") + label, f"st|{v}", S.SUCCESS if sel else S.PRIMARY)
    cap = cfg_int("max_h")
    def ok(h): return not cap or h <= cap
    rows = [[mk("ask", "🤔 اسألني كل مرة")], [mk("best", "🏆 أعلى جودة")]]
    pair = [mk(str(h), f"{h}p") for h in (1080, 720, 480, 360) if ok(h)]
    for i in range(0, len(pair), 2): rows.append(pair[i:i + 2])
    if cfg("mp3_on") == "1": rows.append([mk("audio", "🎧 MP3")])
    rows.append(nav_rows())
    return KB(*rows)

def admin_home_text():
    users = db_exec("SELECT COUNT(*) FROM users")[0][0]
    day = db_exec("SELECT COUNT(*), COUNT(DISTINCT user_id) FROM history WHERE ts>?", (int(time.time()) - 86400,))[0]
    return (ui_title("🛠", "لوحة الأدمن") + "\n"
            + ui_quote(f"👥 مستخدمين: <b>{users}</b>",
                       f"🔥 نشطين 24س: <b>{day[1]}</b>   📥 تحميلات 24س: <b>{day[0]}</b>",
                       f"🌍 الوصول: <b>{'عام' if cfg('public') == '1' else 'خاص'}</b>   🛠 صيانة: <b>{opt_label('maint')}</b>")
            + "\n\n<i>اختار قسم 👇</i>")

def admin_kb():
    return KB(
        [B("📊 المراقبة", "ad|g1", S.SUCCESS), B("👥 الإدارة", "ad|g2")],
        [B("⚙️ الصيانة والإعدادات", "ad|g3")],
        [B("📢 إذاعة", "ad|bc", S.SUCCESS), B("📈 تقرير اليوم", "ad|rp")],
        [B("🏠 القائمة الرئيسية", "m")],
    )

ADMIN_GROUPS = {
    "g1": ("📊 المراقبة", [
        [("📊 إحصائيات", "ad|st", S.PRIMARY), ("📈 تقرير اليوم", "ad|rp", S.SUCCESS)],
        [("📜 آخر التحميلات", "ad|lg", S.PRIMARY), ("⚡ اختبار السرعة", "ad|sp", S.SUCCESS)]]),
    "g2": ("👥 الإدارة", [
        [("👥 المستخدمين", "ad|us", S.PRIMARY), ("🚫 مواقع محظورة", "ad|bl", S.PRIMARY)],
        [("📢 اشتراك إجباري", "ad|fs", S.PRIMARY), ("⚙️ وصول البوت", "ad|cf", S.PRIMARY)]]),
    "g3": ("⚙️ الصيانة والإعدادات", [
        [("🎛 التحكم المتقدم", "ad|ct", S.SUCCESS), ("💧 العلامة المائية", "ad|wm", S.PRIMARY)],
        [("🍪 كوكيز يوتيوب", "ad|ck", S.SUCCESS), ("✨ إيموجي بريميوم", "ad|pe", S.PRIMARY)],
        [("💾 نسخة احتياطية", "ad|bk", S.PRIMARY), ("🗑 مسح الكاش", "ad|cc", S.DANGER)]]),
}

def admin_group_kb(g):
    rows = [[B(t, cb, st) for t, cb, st in row] for row in ADMIN_GROUPS[g][1]]
    rows.append([B("⬅️ رجوع", "ad")])
    return KB(*rows)

def ctl_text():
    body = [f"{title}: <b>{opt_label(key)}</b>" for key, (title, _) in ADMIN_OPTS.items()]
    return (ui_title("🎛", "التحكم المتقدم", "اضغط أي زر لتغيير قيمته (بيلف على القيم)") + "\n"
            + ui_quote(*body)
            + "\n\n<i>💡 «مباشر من المصدر» = البوت يبث الفيديو من رابط المصدر لتليجرام من غير ما يحفظه على "
              "السيرفر (للصيغ اللي بتدعم ده)، وغير كده بيرجع تلقائيًا للتنزيل العادي.</i>")

def ctl_kb():
    keys = list(ADMIN_OPTS)
    rows = []
    for i in range(0, len(keys), 2):
        rows.append([B(f"{ADMIN_OPTS[k][0]}: {opt_label(k)}", f"ad|ct|{k}",
                       S.DANGER if (k == "maint" and cfg(k) == "1") else S.PRIMARY) for k in keys[i:i + 2]])
    rows.append([B("⬅️ رجوع", "ad")])
    return KB(*rows)

# ───────────── yt-dlp (مع تقليد المتصفح) ─────────────
YT_HOSTS = ("youtube.com", "youtu.be", "youtube-nocookie.com")
RETRY_IMP = re.compile(r"403|forbidden|cloudflare|just a moment|captcha|429|impersonat|not a bot|"
                       r"unable to download webpage|unsupported url|timed out|challenge", re.I)
RETRY_YT_ANON = re.compile(r"sign in to confirm|not a bot|login_required|po.?token|http error 403", re.I)
ARIA2_EXIT = re.compile(r"aria2c exited with code\s+(\d+)", re.I)

def is_youtube_url(url):
    host = (urlparse(url).hostname or "").lower()
    return any(host == h or host.endswith("." + h) for h in YT_HOSTS)

def youtube_android_vr_opts(opts):
    """Best-effort anonymous fallback; YouTube may still reject the hosting IP or limit formats."""
    retry = copy.deepcopy(opts)
    args = retry.setdefault("extractor_args", {})
    yt_args = dict(args.get("youtube") or {})
    yt_args["player_client"] = ["tv", "mweb", "web_safari"] if has_cookies() else ["android_vr"]
    args["youtube"] = yt_args
    return retry

def aria2_exit_code(error):
    match = ARIA2_EXIT.search(str(error))
    return int(match.group(1)) if match else None

def native_downloader_opts(opts):
    """نسخة من خيارات yt-dlp من غير aria2، لاستخدام المحمّل الأصلي عند الحاجة."""
    native = dict(opts)
    native.pop("external_downloader", None)
    native.pop("external_downloader_args", None)
    return native

def note_aria2_failure(error):
    global HAS_ARIA2
    code = aria2_exit_code(error)
    if code == 28 and HAS_ARIA2:
        HAS_ARIA2 = False
        log.error("aria2 rejected a command-line option (exit 28); disabling aria2 for this process")
    return code is not None

def missing_output_error(error):
    """يتكرر أحياناً مع aria2 أثناء دمج الصيغ: الملف المؤقت يختفي قبل أن يقرأه yt-dlp."""
    return isinstance(error, FileNotFoundError) or "No such file or directory" in str(error)

def base_opts(referer=None):
    o = {"quiet": True, "no_warnings": True, "retries": 10, "fragment_retries": 10,
         "socket_timeout": 30, "concurrent_fragment_downloads": FRAGMENTS, "noprogress": True}
    if referer: o["http_headers"] = {"Referer": referer, "User-Agent": UA}
    if has_cookies(): o["cookiefile"] = COOKIE_FILE
    if PROXY: o["proxy"] = PROXY
    return o

def ydl_run(url, opts, download):
    """يجرب افتراضيًا بلا جلسة؛ لرفض YouTube يعيد بعميل Android VR مجهول ثم Chrome impersonation."""
    try:
        with yt_dlp.YoutubeDL(opts) as y:
            return y.extract_info(url, download=download)
    except Exception as initial_error:
        error = initial_error
        if opts.get("external_downloader") and (note_aria2_failure(error) or missing_output_error(error)):
            native = native_downloader_opts(opts)
            log.warning("external downloader failed (code %s); retrying with yt-dlp native downloader",
                        aria2_exit_code(error))
            try:
                with yt_dlp.YoutubeDL(native) as y:
                    return y.extract_info(url, download=download)
            except Exception as native_error:
                error = native_error
                log.warning("native downloader retry failed: %s", native_error)
        if is_youtube_url(url) and RETRY_YT_ANON.search(str(error)):
            anonymous = youtube_android_vr_opts(opts)
            if not HAS_ARIA2:
                anonymous = native_downloader_opts(anonymous)
            log.warning("YouTube rejected the default client; retrying with fallback clients (cookies: %s)", has_cookies())
            try:
                with yt_dlp.YoutubeDL(anonymous) as y:
                    return y.extract_info(url, download=download)
            except Exception as anonymous_error:
                error = anonymous_error
                log.warning("YouTube android_vr retry failed: %s", anonymous_error)
        if IMPERSONATE and (RETRY_IMP.search(str(error)) or RETRY_IMP.search(str(initial_error))):
            o2 = native_downloader_opts(opts)
            o2["impersonate"] = IMPERSONATE
            try:
                with yt_dlp.YoutubeDL(o2) as y:
                    return y.extract_info(url, download=download)
            except Exception as impersonate_error:
                error = impersonate_error
        raise error

def is_single_video(url):
    """فيديو يوتيوب مفرد (مش Playlist). المواقع التانية بيقررها yt-dlp نفسه."""
    p = urlparse(url)
    host = (p.hostname or "").lower()
    if not any(host == h or host.endswith("." + h) for h in YT_HOSTS): return False
    if host.endswith("youtu.be") or p.path.startswith(("/shorts/", "/live/", "/embed/")): return True
    return p.path == "/watch" and "v=" in p.query

def probe_ytdlp(url, referer=None):
    single = is_single_video(url)
    o = base_opts(referer)
    o.update(extract_flat="in_playlist", noplaylist=single)
    pl_limit = cfg_int("pl_max")
    if pl_limit > 0: o["playlistend"] = pl_limit
    info = ydl_run(url, o, False)
    items, ptitle = [], None
    if info.get("_type") == "playlist":
        if cfg("pl_on") != "1":
            raise RuntimeError("القوائم (Playlists) والروابط متعددة الفيديو مقفولة من صاحب البوت")
        ptitle = info.get("title")
        for e in info.get("entries") or []:
            if not e: continue
            u, eid = e.get("url") or e.get("webpage_url"), e.get("id")
            ie = (e.get("ie_key") or info.get("extractor_key") or "x").lower()
            if not u or not u.startswith("http"):
                if ie == "youtube" and eid: u = f"https://www.youtube.com/watch?v={eid}"
                else: continue
            if not url_ok(u): continue
            items.append(Item(u, e.get("title") or u, f"{ie}:{eid or u}", referer=referer or ""))
            if pl_limit > 0 and len(items) >= pl_limit: break
    else:
        ie = (info.get("extractor_key") or "x").lower()
        items.append(Item(url, info.get("title") or url, f"{ie}:{info.get('id') or url}",
                          referer=referer or "", info=info if info.get("formats") else None))
    return items, ptitle

# ───────────── كاشف الفيديو في أي صفحة ─────────────
OG_RE = re.compile(r"""<meta[^>]+(?:property|name)=["']og:video(?::secure_url|:url)?["'][^>]+content=["']([^"']+)""", re.I)
SRC_RE = re.compile(r"""<(?:video|source)[^>]+src=["']([^"']+)""", re.I)
MEDIA_RE = re.compile(r"""https?://[^\s"'<>\\]+?\.(?:m3u8|mpd|mp4|webm|mov|mkv)(?:\?[^\s"'<>\\]*)?""", re.I)
IFRAME_RE = re.compile(r"""<iframe[^>]+src=["']([^"']+)""", re.I)
TITLE_RE = re.compile(r"""<meta[^>]+property=["']og:title["'][^>]+content=["']([^"']+)|<title[^>]*>([^<]+)""", re.I)

class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *a, **kw): return None

_REDIRECT_CODES = (301, 302, 303, 307, 308)

def _get_once(url):
    """طلب واحد من غير ما يتبع Redirect تلقائيًا. بيرجّع (نص, لينك_التحويل_أو_None)."""
    try:
        if IMPERSONATE:
            from curl_cffi import requests as cr
            r = cr.get(url, impersonate="chrome", timeout=20, allow_redirects=False)
            if r.status_code in _REDIRECT_CODES and r.headers.get("location"):
                return "", r.headers["location"]
            return r.text[:3_000_000], None
    except Exception as e:
        log.debug("curl_cffi fetch failed: %s", e)
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    try:
        with urllib.request.build_opener(_NoRedirect).open(req, timeout=20) as r:
            return r.read(3_000_000).decode("utf-8", "ignore"), None
    except urllib.error.HTTPError as e:
        if e.code in _REDIRECT_CODES and e.headers.get("Location"):
            return "", e.headers["Location"]
        raise

def fetch_html(url):
    """بيجيب الصفحة وبيفحص كل Redirect (لحد 5) قبل ما يتبعه — عشان تحويلة لعنوان داخلي ما تعدّيش."""
    cur = url
    for _ in range(6):
        if not url_ok(cur): raise RuntimeError("unsafe or blocked url")
        text, loc = _get_once(cur)
        if loc is None: return text
        cur = urljoin(cur, loc)
    raise RuntimeError("too many redirects")

def sniff(url):
    txt = fetch_html(url).replace("\\/", "/").replace("&amp;", "&")
    cands = OG_RE.findall(txt) + SRC_RE.findall(txt) + MEDIA_RE.findall(txt) + IFRAME_RE.findall(txt)
    seen, urls = set(), []
    for c in cands:
        c = urljoin(url, c.strip())
        if c.startswith("http") and c not in seen and c != url and url_ok(c):   # SSRF: كل مرشح لازم يعدّي الفحص
            seen.add(c); urls.append(c)
    m = TITLE_RE.search(txt)
    title = (m.group(1) or m.group(2)).strip() if m else ""
    for c in urls:
        try:
            items, _ = probe_ytdlp(c, referer=url)
        except Exception:
            continue
        if items:
            it = items[0]
            it.title = title[:100] or it.title
            it.referer = url
            it.key = "sniff:" + hashlib.sha1(c.encode()).hexdigest()[:16]
            return [it]
    raise RuntimeError("no video found in page")

# ───────────── gallery-dl (صور وألبومات) ─────────────
def gallery_supported(url):
    if not (HAS_GALLERY and gdx): return False
    try: return gdx.find(url) is not None
    except Exception: return False

def do_gallery(url, outdir):
    if is_drive(url): return do_drive(url, outdir)
    cmd = ["gallery-dl", "-q", "-D", outdir, "-f", "{num:>03}.{extension}"]
    if MAX_GALLERY > 0: cmd += ["--range", f"1-{MAX_GALLERY}"]
    r = subprocess.run(cmd + [url], capture_output=True, text=True)
    files = sorted(os.path.join(outdir, f) for f in os.listdir(outdir)
                   if os.path.isfile(os.path.join(outdir, f)) and not f.endswith((".json", ".txt", ".part")))
    if not files:
        raise RuntimeError((r.stderr or "no media").strip()[-300:])
    return files

# ───────────── جوجل درايف (ملفات ومجلدات) ─────────────
DRIVE_RE = re.compile(r"https?://(?:drive\.google\.com|drive\.usercontent\.google\.com)/", re.I)
DRIVE_ID_RE = re.compile(r"(?:/d/|[?&]id=)([A-Za-z0-9_-]{15,})")

def is_drive(url): return bool(DRIVE_RE.match(url or ""))
def drive_is_folder(url): return "/folders/" in url or "folderview" in url

def do_drive(url, outdir):
    try:
        import gdown
    except ImportError:
        raise RuntimeError("gdown_missing")
    if drive_is_folder(url):
        kw = {"url": url, "output": outdir, "quiet": True}
        if "remaining_ok" in inspect.signature(gdown.download_folder).parameters: kw["remaining_ok"] = True
        gdown.download_folder(**kw)
    else:
        mid = DRIVE_ID_RE.search(url)
        if not mid: raise RuntimeError("رابط درايف غير صالح")
        out = gdown.download(id=mid.group(1), output=outdir + os.sep, quiet=True)
        if not out: raise RuntimeError("cannot retrieve the public link")
    files = sorted(os.path.join(r, f) for r, _, fs in os.walk(outdir) for f in fs
                   if not f.endswith((".part", ".tmp")))
    ok = [f for f in files if os.path.getsize(f) <= max_size()]
    if not ok:
        raise RuntimeError("الملف أكبر من الحد المسموح" if files else "مفيش ملفات في الرابط ده")
    return ok

def drive_item(url):
    kind = "مجلد" if drive_is_folder(url) else "ملف"
    return Item(url, f"📁 Google Drive ({kind})", "drv:" + hashlib.sha1(url.encode()).hexdigest()[:16], engine="gallery")

# ───────────── محرك الاكتشاف (بالترتيب) ─────────────
def probe(url):
    """yt-dlp ← gallery-dl ← كاشف الصفحة. لو الكل فشل بيرجّع خطأ yt-dlp الأصلي."""
    try:
        res = probe_ytdlp(url)
        if is_drive(url) and res[0] and res[0][0].info is None:   # ملف درايف مش فيديو → gdown
            return [drive_item(url)], None
        return res
    except Exception as first:
        if is_drive(url):
            return [drive_item(url)], None
        if gallery_supported(url):
            host = (urlparse(url).hostname or "").replace("www.", "")
            return [Item(url, f"📷 {host}", "gal:" + hashlib.sha1(url.encode()).hexdigest()[:16],
                         engine="gallery")], None
        try:
            return sniff(url), None
        except Exception as e2:
            log.info("all engines failed for %s | ytdlp: %s | sniff: %s", url, first, e2)
            # سيرفر تحميل خارجي (اختياري): لو يوتيوب/موقع حاجب IP السيرفر بنجرب cobalt بدل ما نفشل
            if ((VIDKRAKEN_API_KEY and is_youtube_url(url))
                    or (COBALT_API_URL and (is_youtube_url(url) or RETRY_IMP.search(str(first))))):
                host = (urlparse(url).hostname or "").replace("www.", "")
                return [Item(url, f"🎬 {host}", "cobalt:" + hashlib.sha1(url.encode()).hexdigest()[:16],
                             engine="cobalt")], None
            raise first

# ───────────── كاش الفحص + دمج الطلبات المتطابقة (v12) ─────────────
PROBE_CACHE = {}        # url -> (وقت, [Item], عنوان_القائمة)
PROBE_FLIGHTS = {}      # url -> Task شغّال دلوقتي: طلبين لنفس الرابط = فحص واحد بس

def _probe_cacheable(items):
    if len(items) != 1: return False
    it = items[0]
    info = it.info
    if it.engine != "ytdlp" or not isinstance(info, dict) or not info.get("formats"): return False
    return not (info.get("is_live") or info.get("live_status") in ("is_live", "is_upcoming"))

def _probe_clone(items, ptitle):
    # نسخ جديدة من Item (الحالة بتتغيّر)؛ نتيجة الفحص نفسها (info) مشتركة للقراءة بس
    return [dc_replace(i) for i in items], ptitle

def probe_cache_trim():
    now = time.monotonic()
    for k in [k for k, v in PROBE_CACHE.items() if now - v[0] >= PROBE_TTL]:
        PROBE_CACHE.pop(k, None)
    while len(PROBE_CACHE) >= PROBE_CACHE_MAX:
        PROBE_CACHE.pop(next(iter(PROBE_CACHE)), None)

async def probe_shared(url):
    """فحص الرابط بسقف PROBE_SEM، مع كاش PROBE_TTL ثانية، ودمج الطلبات المتزامنة لنفس الرابط في فحص واحد."""
    hit = PROBE_CACHE.get(url)
    if hit and PROBE_TTL and time.monotonic() - hit[0] < PROBE_TTL:
        return _probe_clone(hit[1], hit[2])
    task = PROBE_FLIGHTS.get(url)
    if task is None:
        async def _run():
            async with PROBE_SEM:
                return await asyncio.to_thread(probe, url)
        task = asyncio.ensure_future(_run())
        PROBE_FLIGHTS[url] = task
        def _done(t, url=url):
            PROBE_FLIGHTS.pop(url, None)
            if t.cancelled() or t.exception() is not None: return
            items, pl = t.result()
            if PROBE_TTL and _probe_cacheable(items):
                probe_cache_trim()
                PROBE_CACHE[url] = (time.monotonic(), items, pl)
        task.add_done_callback(_done)
    items, pl = await asyncio.shield(task)
    return _probe_clone(items, pl)

def check_limits(info):
    """يرفض البث المباشر، والفيديو الأطول من حد المدة اللي ضابطه الأدمن (الافتراضي بلا حد)."""
    if not info: return
    if info.get("is_live") or info.get("live_status") in ("is_live", "is_upcoming"):
        raise RuntimeError("live event")                      # بيتحوّل لرسالة عربي من ERR_MAP
    limit_min = cfg_int("max_min")
    try: duration = float(info.get("duration") or 0)
    except (TypeError, ValueError): duration = 0
    if limit_min and duration > limit_min * 60:
        raise RuntimeError(f"الفيديو أطول من الحد المسموح ({limit_min} دقيقة)")

def _match_filter(info, *, incomplete=False):
    if not incomplete: check_limits(info)
    return None

# H.264 أولًا: تليجرام (iOS/Desktop) ساعات مش بيشغّل VP9/AV1 جوه الـ MP4
def size_filter():
    mb = cfg_int("max_mb")
    return f"[filesize<?{min(mb, 1900) if mb else 1900}M]"

def sort_for(mode):
    """ترتيب الصيغ: الدقة (أقصر ضلع، بحد أقصى الجودة المطلوبة) ثم H.264 لتوافق تليجرام.
    ده بيحل مشكلة الفيديوهات الطولية (Shorts/TikTok) اللي كان فلتر height بيدّيها جودة أقل من المطلوبة."""
    if mode == "audio": return []
    if mode == "best": return ["vcodec:h264"]
    return [f"res:{mode}", "vcodec:h264"]

def fmt_for(mode):
    SZ = size_filter()
    if mode == "audio": return "bestaudio/best"
    return f"bv*{SZ}+ba[ext=m4a]/bv*{SZ}+ba/b{SZ}/b"

FALLBACK = {"best": ["1080", "720", "480", "360"], "1080": ["720", "480", "360"], "720": ["480", "360"],
            "480": ["360"], "360": [], "audio": []}

def fallback_qualities(mode):
    if mode in FALLBACK: return FALLBACK[mode]
    try: target = int(mode)
    except (TypeError, ValueError): return []
    return [str(height) for height in (2160, 1440, 1080, 720, 480, 360) if height < target]

def do_download_fit(it, mode, outdir, progress_hook=None):
    """لو الملف عدّى 2GB بينزل جودة تلقائيًا بدل ما يفشل. بيرجّع (مسار, info, الجودة_الفعلية)."""
    for m in [mode] + fallback_qualities(mode):
        path, info = do_download(it, m, outdir, progress_hook)
        if os.path.getsize(path) <= max_size():
            return path, info, m
        log.info("file too big in %s for %s, trying lower quality", m, it.url)
        try: os.remove(path)
        except OSError: pass
    raise RuntimeError(f"الملف أكبر من الحد المسموح ({human_bytes(max_size())}) حتى بأقل جودة")

def do_download(it, mode, outdir, progress_hook=None):
    o = base_opts(it.referer or None)
    # استخدام id بدلاً من العنوان يمنع مشاكل Unicode/طول الاسم وتعارض ملفات الدمج.
    o.update(noplaylist=True, outtmpl=f"{outdir}/%(id)s.%(ext)s")
    if progress_hook: o["progress_hooks"] = [progress_hook]
    if HAS_ARIA2:
        o["external_downloader"] = {"default": "aria2c", "dash": "native",
                                    "m3u8": "native", "m3u8_native": "native"}
        o["external_downloader_args"] = {"aria2c": [
            "-x", str(min(CONN, 16)), "-s", str(CONN), "-k", "1M", "--min-split-size=1M",
            "--file-allocation=none", "--disable-ipv6=true", "--connect-timeout=10",
            "--max-tries=5", "--retry-wait=1", "--summary-interval=0",
            "--console-log-level=error"]}
    o["format"] = pick_format(it.info, mode)
    if sort_for(mode): o["format_sort"] = sort_for(mode)
    o["match_filter"] = _match_filter
    if mode == "audio":
        o["postprocessors"] = [{"key": "FFmpegExtractAudio", "preferredcodec": "mp3",
                                "preferredquality": "192"}]
    else:
        o["merge_output_format"] = "mp4"
    info = None
    if it.info:                    # نستخدم نتيجة الفحص: بنوفر 2-5 ثواني استخراج
        check_limits(it.info)      # بره الـ try عشان الرفض ما يتحوّلش لإعادة استخراج
        try:
            with yt_dlp.YoutubeDL(o) as y:
                info = y.process_ie_result(copy.deepcopy(it.info), download=True)
        except Exception as e:
            log.info("reuse probe info failed, re-extracting: %s", e)
            for f in os.listdir(outdir):
                try: os.remove(os.path.join(outdir, f))
                except OSError: pass
            info = None
            if o.get("external_downloader") and (note_aria2_failure(e) or missing_output_error(e)):
                o = native_downloader_opts(o)
                log.warning("external downloader failed on reused probe info; retrying with yt-dlp native downloader")
                with yt_dlp.YoutubeDL(o) as y:
                    info = y.process_ie_result(copy.deepcopy(it.info), download=True)
    if info is None:
        info = ydl_run(it.url, o, True)
    files = [os.path.join(outdir, f) for f in os.listdir(outdir)]
    files = [f for f in files if os.path.isfile(f) and not f.endswith((".aria2", ".part", ".ytdl"))]
    if not files:
        raise RuntimeError("التحميل فشل (مفيش ملف ناتج)")
    return max(files, key=os.path.getsize), info

def dir_size(d):
    t = 0
    for f in os.listdir(d):
        try: t += os.path.getsize(os.path.join(d, f))
        except OSError: pass
    return t

async def make_thumb(path, out):
    for ss in ("1", "0"):          # الفيديو القصير (<1 ثانية) مفيهوش فريم عند الثانية 1
        try:
            p = await asyncio.create_subprocess_exec(
                "ffmpeg", "-y", "-ss", ss, "-i", path, "-frames:v", "1", "-vf", "scale=320:-1", out,
                stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)
            await p.wait()
        except Exception:
            return None
        if os.path.exists(out): return out
    return None

# ───────────── العلامة المائية (بتتحكم فيها من لوحة الأدمن) ─────────────
FONT = next((f for f in ("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
                         "/usr/share/fonts/dejavu/DejaVuSans-Bold.ttf") if os.path.exists(f)), None)
WM_IMG_PATH = os.path.join(os.path.dirname(os.path.abspath(DB_PATH)), "watermark.png")   # جنب القاعدة (على Volume)
WM_SIZES = {"S": 0.03, "M": 0.045, "L": 0.065}      # حجم النص = نسبة من ارتفاع الفيديو
WM_IMG_SIZES = {"S": 0.12, "M": 0.2, "L": 0.3}      # عرض الصورة = نسبة من عرض الفيديو
WM_POS_LABEL = {"tl": "↖️ فوق شمال", "tr": "↗️ فوق يمين", "bl": "↙️ تحت شمال", "br": "↘️ تحت يمين", "c": "⏺ المنتصف"}
WM_SIZE_LABEL = {"S": "صغير", "M": "وسط", "L": "كبير"}

def wm_snapshot(mode):
    """لقطة من إعدادات العلامة وقت بداية العنصر (عشان تغيير الإعدادات في نص التحميل ما يلخبطش الكاش).
    None = من غير علامة (مقفولة أو الوضع صوت)."""
    if mode == "audio" or cfg("wm_on") != "1": return None
    t = cfg("wm_type")
    d = {"type": t, "pos": cfg("wm_pos"), "size": cfg("wm_size"),
         "v": cfg("wm_text") if t == "text" else cfg("wm_img_sig")}
    d["sig"] = hashlib.sha1(repr(sorted(d.items())).encode()).hexdigest()[:8]
    return d

def cache_mode(mode, wm):
    """الكاش بيفرّق بين النسخة العادية والنسخ اللي عليها علامة (حسب نوعها ومكانها وحجمها)."""
    return f"{mode}|wm{wm['sig']}" if wm else mode

def wm_missing():
    """سبب إن العلامة مش جاهزة (None = جاهزة)."""
    if cfg("wm_type") == "image":
        return None if os.path.exists(WM_IMG_PATH) else "ارفع صورة العلامة الأول (🖼 رفع صورة)"
    if not FONT: return "الخط مش متسطّب على السيرفر"
    return None if cfg("wm_text").strip() else "اكتب نص العلامة الأول (✏️ تغيير النص)"

def build_wm_cmd(src, out, w, h, wm, txt_file=None):
    """أمر ffmpeg بيحط العلامة (دالة نقية عشان تتختبر لوحدها). بيعيد ترميز الفيديو H.264 والصوت بيتنسخ."""
    pos, even = wm["pos"], "scale=trunc(iw/2)*2:trunc(ih/2)*2"
    m = max(8, int(min(w, h) * 0.02))
    enc = ["-c:v", "libx264", "-preset", "veryfast", "-crf", "23", "-pix_fmt", "yuv420p",
           "-c:a", "copy", "-movflags", "+faststart", out]
    if wm["type"] == "image":
        ox = {"tl": m, "bl": m, "tr": f"W-w-{m}", "br": f"W-w-{m}", "c": "(W-w)/2"}[pos]
        oy = {"tl": m, "tr": m, "bl": f"H-h-{m}", "br": f"H-h-{m}", "c": "(H-h)/2"}[pos]
        ww = max(32, int(w * WM_IMG_SIZES[wm["size"]]) // 2 * 2)
        fc = (f"[1:v]scale={ww}:-2,format=rgba,colorchannelmixer=aa=0.85[wm];"
              f"[0:v][wm]overlay={ox}:{oy},{even}[v]")
        return ["ffmpeg", "-y", "-i", src, "-i", WM_IMG_PATH, "-filter_complex", fc,
                "-map", "[v]", "-map", "0:a?"] + enc
    fs = max(14, int(h * WM_SIZES[wm["size"]]))
    tx = {"tl": m, "bl": m, "tr": f"w-text_w-{m}", "br": f"w-text_w-{m}", "c": "(w-text_w)/2"}[pos]
    ty = {"tl": m, "tr": m, "bl": f"h-text_h-{m}", "br": f"h-text_h-{m}", "c": "(h-text_h)/2"}[pos]
    vf = (f"drawtext=fontfile={FONT}:textfile={txt_file}:expansion=none:fontsize={fs}:fontcolor=white@0.85:"
          f"borderw={max(1, fs // 14)}:bordercolor=black@0.6:x={tx}:y={ty},{even}")
    return ["ffmpeg", "-y", "-i", src, "-vf", vf, "-map", "0:v:0", "-map", "0:a?"] + enc

async def probe_wh(path):
    try:
        p = await asyncio.create_subprocess_exec(
            "ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height",
            "-of", "csv=s=x:p=0", path, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
        out, _ = await p.communicate()
        w, h = out.decode().strip().split("x")[:2]
        return int(w), int(h)
    except Exception:
        return 0, 0

async def apply_watermark(path, wm, outdir):
    """بيعمل نسخة بالعلامة المائية ويمسح الأصل. لو فشل بيرمي خطأ واضح (مفيش إرسال من غير علامة بالسكوت)."""
    if wm["type"] == "image":
        if not os.path.exists(WM_IMG_PATH): raise RuntimeError("صورة العلامة المائية مش موجودة — ارفعها من لوحة الأدمن")
    elif not FONT:
        raise RuntimeError("خط العلامة المائية مش متسطّب على السيرفر")
    w, h = await probe_wh(path)
    if not (w and h): raise RuntimeError("مقدرتش أقرا أبعاد الفيديو علشان أحط العلامة")
    out, txt_file = os.path.join(outdir, "wm_out.mp4"), None
    if wm["type"] == "text":
        txt_file = os.path.join(outdir, "wm.txt")
        with open(txt_file, "w", encoding="utf-8") as f: f.write(wm["v"])     # من غير سطر جديد في الآخر
    p = await asyncio.create_subprocess_exec(*build_wm_cmd(path, out, w, h, wm, txt_file),
                                             stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE)
    _, err = await p.communicate()
    if p.returncode != 0 or not os.path.exists(out):
        log.warning("watermark failed: %s", err.decode("utf-8", "ignore")[-400:])
        raise RuntimeError("فشل إضافة العلامة المائية")
    os.remove(path)
    return out

async def with_retry(fn, *a, tries=3, **kw):
    """إعادة محاولة للرفع: FloodWait بيستنى المدة المطلوبة، وأي خطأ شبكة بيتعاد بفاصل متزايد."""
    for i in range(tries):
        try:
            return await fn(*a, **kw)
        except FloodWait as e:
            if i == tries - 1: raise
            await asyncio.sleep(min(e.value + 1, 60))
        except asyncio.CancelledError:
            raise
        except Exception as e:
            if i == tries - 1: raise
            log.info("send failed (%s), retry %d", e, i + 1)
            await asyncio.sleep(2 * (i + 1))

async def wait_disk(poll=3, tries=40):
    """مانع إننا نبدأ تحميل جديد والقرص شبه ممتلئ (تحميلات متزامنة + دمج فيديو/صوت بياخدوا مساحة)."""
    for _ in range(tries):
        if shutil.disk_usage(tempfile.gettempdir()).free > MIN_FREE_MB * 1024 * 1024: return
        await asyncio.sleep(poll)
    raise RuntimeError("السيرفر ممتلئ مؤقتًا — حاول بعد شوية")

# ───────────── الإرسال ─────────────
def human_bytes(value):
    try: value = max(float(value or 0), 0.0)
    except (TypeError, ValueError): value = 0.0
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if value < 1024 or unit == "TB":
            return f"{value:.0f} {unit}" if unit == "B" else f"{value:.1f} {unit}"
        value /= 1024

def duration_text(seconds):
    """تنسيق مدة قصيرة بشكل موحد في شاشة التقدم."""
    seconds = max(0, int(float(seconds or 0)))
    hh, rem = divmod(seconds, 3600)
    mm, ss = divmod(rem, 60)
    return f"{hh}س {mm:02}د {ss:02}ث" if hh else f"{mm}د {ss:02}ث" if mm else f"{ss}ث"

def progress_text(current, total=None, speed=None, eta=None, elapsed=None, width=12):
    current = max(float(current or 0), 0.0)
    try: total = float(total) if total else 0.0
    except (TypeError, ValueError): total = 0.0
    if total > 0:
        ratio = min(max(current / total, 0.0), 1.0)
        heading = f"<b>📊 {int(ratio * 100)}%</b>  {ui_bar(ratio, width)}"
        amount = f"📦 {human_bytes(current)} / {human_bytes(total)}"
    else:
        pos = int(time.monotonic() * 2) % (width - 1)
        heading = "<b>📊 …</b>  " + "▱" * pos + "▰▰" + "▱" * (width - pos - 2)
        amount = f"📦 {human_bytes(current)}"
    parts = [amount]
    try:
        if speed and float(speed) > 0: parts.append(f"⚡ {human_bytes(speed)}/ث")
    except (TypeError, ValueError): pass
    try:
        if elapsed is not None: parts.append(f"⏱ مستغرق: {duration_text(elapsed)}")
        if eta is not None: parts.append(f"⌛ متبقي: {duration_text(eta)}")
    except (TypeError, ValueError, OverflowError): pass
    return heading + "\n" + "  •  ".join(parts)

def make_upload_progress(it, label="رفع"):
    st = {"started": time.monotonic(), "at": time.monotonic(), "bytes": 0.0,
          "last": 0.0, "speed": 0.0}
    async def callback(current, total, *_):
        now, cur = time.monotonic(), float(current or 0)
        cur = max(cur, st["last"])
        if cur <= st["last"] and not (total and cur >= total): return
        dt, finished = now - st["at"], bool(total and cur >= total)
        if dt < 1.0 and not finished: return
        inst = max(cur - st["bytes"], 0) / max(dt, 0.01)
        st["speed"] = inst if not st["speed"] else 0.85 * st["speed"] + 0.15 * inst
        st["at"], st["bytes"], st["last"] = now, cur, cur
        try: eta = (float(total) - cur) / st["speed"] if st["speed"] > 0 and total else None
        except (TypeError, ValueError): eta = None
        it.detail = progress_text(cur, total, st["speed"], eta, now - st["started"])
    return callback

def make_download_progress_hook(it, loop, state):
    throttle = {"at": 0.0}
    def hook(data):
        chk = getattr(it, "is_cancelled", None)
        if chk and chk():                       # الإلغاء يوقف التنزيل فورًا مش بعد ما الملف يخلص
            raise yt_dlp.utils.DownloadCancelled("أُلغي")
        status = data.get("status")
        now = time.monotonic()
        if status == "downloading":
            if now - throttle["at"] < 0.7: return
            throttle["at"] = now
            current = max(float(data.get("downloaded_bytes") or 0), state.get("current", 0.0))
            exact_total = data.get("total_bytes")
            estimate_total = data.get("total_bytes_estimate")
            if exact_total:
                state["total"] = max(float(exact_total), state.get("total", 0.0))
            elif not state.get("total") and estimate_total:
                state["total"] = float(estimate_total)
            state["current"] = current
            state["total"] = max(state.get("total", 0.0), current)
            total = state.get("total")
            speed = data.get("speed")
            eta = data.get("eta")
            detail = progress_text(current, total, speed, eta, now - state["started"])
        elif status == "finished":
            detail = "🔄 اكتمل الجزء • جارٍ الدمج والمعالجة..."
        else:
            return
        def publish():
            it.detail = detail
            state["updated"] = time.monotonic()
        try: loop.call_soon_threadsafe(publish)
        except RuntimeError: pass
    return hook

async def wait_with_progress(task, it, outdir, hook_state=None):
    previous_size, previous_at = 0, time.monotonic()
    while not task.done():
        await asyncio.sleep(1)
        now = time.monotonic()
        if hook_state and now - hook_state["updated"] < 2:
            continue
        size = dir_size(outdir)
        # حجم المجلد قد ينقص أثناء الدمج/حذف ملف وسيط؛ لا نسمح للتقدم بالرجوع.
        if hook_state:
            size = max(size, hook_state.get("current", 0.0))
            hook_state["current"] = size
        speed = max(size - previous_size, 0) / max(now - previous_at, 0.01)
        it.detail = progress_text(size, speed=speed,
                                  elapsed=now - (hook_state or {}).get("started", previous_at))
        previous_size, previous_at = size, now
        if hook_state: hook_state["updated"] = now
    return await task

# ───────────── العنوان / الصورة المصغرة / الإرسال المباشر ─────────────
def youtube_watch_url(it, info):
    """الرابط الأصلي لفيديو يوتيوب (للعنوان القابل للضغط). غير يوتيوب → None."""
    vid = None
    if isinstance(info, dict) and str(info.get("extractor_key") or "").lower() == "youtube":
        vid = info.get("id")
    elif str(it.key).startswith("youtube:"):
        vid = it.key.split(":", 1)[1]
    if vid and re.fullmatch(r"[\w-]{11}", str(vid)):
        return f"https://www.youtube.com/watch?v={vid}"
    return it.url if is_youtube_url(it.url) else None

def build_caption(it, info, mode=None):
    """كابشن HTML: عنوان الفيديو (عريض)، ولو يوتيوب يبقى رابط للفيديو الأصلي، وتحته سطر الموقع والقناة."""
    title = " ".join(str((info or {}).get("title") or it.title or "").split())[:200]
    safe = html.escape(title, quote=False)
    link = youtube_watch_url(it, info) if cfg("title_link") == "1" else None
    if link:
        head = f'<b><a href="{html.escape(link, quote=True)}">{safe or "▶️ YouTube"}</a></b>'
    else:
        head = f"<b>{safe}</b>" if safe else ""
    site = site_of(it.url)
    who = html.escape(" ".join(str((info or {}).get("uploader") or (info or {}).get("channel") or "").split())[:40], quote=False)
    meta = " • ".join(x for x in (f"📍 {html.escape(site, quote=False)}" if site and cfg("cap_site") == "1" else "",
                                  f"👤 {who}" if who and cfg("cap_chan") == "1" else "") if x)
    facts = []
    try:
        dur = int(float((info or {}).get("duration") or 0))
        if dur > 0 and cfg("cap_dur") == "1": facts.append(f"⏱ {duration_text(dur)}")
    except (TypeError, ValueError, OverflowError): pass
    if cfg("cap_qual") != "1": pass
    elif mode == "audio": facts.append("🎧 MP3")
    elif mode:
        height = _format_height(info or {})
        facts.append(f"📺 {height}p" if height else f"📺 {mode_label(mode)}")
    sub = [x for x in (meta, "  ".join(facts)) if x]
    return head + ("\n" + "\n".join(f"<i>{x}</i>" for x in sub) if head and sub else "")

def safe_filename(title, ext):
    name = re.sub(r'[\\/:*?"<>|\x00-\x1f]+', " ", str(title or "video"))
    name = " ".join(name.split())[:60].strip(" .") or "video"
    return f"{name}.{ext}"

def safe_get(url, hops=3, **kw):
    """GET مع فحص SSRF لكل تحويلة (بنتبع التحويلات بنفسنا)."""
    import requests
    cur = url
    for _ in range(hops + 1):
        if not is_safe_url(cur): raise RuntimeError("unsafe url")
        r = requests.get(cur, allow_redirects=False, **kw)
        if r.status_code in (301, 302, 303, 307, 308) and r.headers.get("location"):
            cur = urljoin(cur, r.headers["location"]); r.close(); continue
        return r
    raise RuntimeError("too many redirects")

def fetch_thumb_file(url, outdir):
    """بينزّل صورة الفيديو الأصلية ويحوّلها JPEG ≤320px (شرط تليجرام للـ thumb)."""
    r = safe_get(url, headers={"User-Agent": UA}, timeout=15, stream=True, proxies={"http": PROXY, "https": PROXY} if PROXY else None)
    try:
        if r.status_code != 200: return None
        raw_path = os.path.join(outdir, "thumb_src")
        got = 0
        with open(raw_path, "wb") as f:
            for chunk in r.iter_content(65536):
                got += len(chunk)
                if got > 5 * 1024 * 1024: return None
                f.write(chunk)
    finally:
        r.close()
    out = os.path.join(outdir, "thumb_orig.jpg")
    for q in ("4", "10"):
        subprocess.run(["ffmpeg", "-y", "-i", raw_path, "-frames:v", "1", "-vf", "scale='min(320,iw)':-2",
                        "-q:v", q, out], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
        if os.path.exists(out) and os.path.getsize(out) <= 195 * 1024: return out
    return None

async def get_thumb(info, outdir):
    if cfg("thumb_on") != "1": return None
    url = thumbnail_url(info)
    if not url: return None
    try: return await asyncio.to_thread(fetch_thumb_file, url, outdir)
    except Exception as e:
        log.debug("thumbnail fetch failed: %s", e)
        return None

DIRECT_VIDEO_EXT = {"mp4", "m4v", "mov"}
HTTP_ONLY = "[protocol~='^https?$']"

@dataclass
class DirectPlan:
    url: str
    headers: dict
    name: str
    info: dict
    audio: bool = False

def _single_http(res, audio):
    """هل اختيار yt-dlp ده ملف واحد http(s) جاهز للتشغيل في تليجرام (بدون دمج/تجزئة)؟"""
    if not isinstance(res, dict) or res.get("requested_formats") or res.get("fragments"): return None
    if res.get("protocol") not in ("http", "https") or not res.get("url"): return None
    ext = str(res.get("ext") or "").lower()
    if audio:
        return res if ext in ("m4a", "mp3", "aac") and res.get("vcodec") in (None, "none") else None
    if ext not in DIRECT_VIDEO_EXT or res.get("vcodec") == "none" or res.get("acodec") == "none": return None
    return res

def _height_of(res):
    fmts = res.get("requested_formats") or [res]
    return max((_format_height(f) for f in fmts if isinstance(f, dict)), default=0)

def progressive_fmt(mode):
    SZ = size_filter()
    return f"b[ext=mp4]{HTTP_ONLY}[vcodec^=avc1]{SZ}/b[ext=mp4]{HTTP_ONLY}{SZ}"

def plan_direct(it, mode):
    """(sync) بيقرر لو العنصر ينفع يتبث مباشرة من المصدر لتليجرام من غير تنزيل على السيرفر.
    بيرجّع DirectPlan أو None (None = المسار العادي). مفيش هبوط صامت في الجودة: لو الجودة المطلوبة محتاجة
    دمج فيديو+صوت (زي يوتيوب HD) يرجع None."""
    info = it.info
    if info is None:
        o = base_opts(it.referer or None); o["noplaylist"] = True
        info = ydl_run(it.url, o, False)
        if not isinstance(info, dict) or info.get("_type") == "playlist" or not info.get("formats"): return None
    check_limits(info)
    audio = mode == "audio"
    base = base_opts(it.referer or None)
    base.update(noplaylist=True)
    chosen, headers, y = None, None, None
    def run(fmt):
        """يطبّق اختيار الصيغة على نتيجة الفحص (من غير شبكة). فشل الاختيار = (None, None)."""
        o = dict(base); o["format"] = fmt
        if not audio and sort_for(mode): o["format_sort"] = sort_for(mode)
        yd = yt_dlp.YoutubeDL(o)
        try: return yd, yd.process_ie_result(copy.deepcopy(info), download=False)
        except yt_dlp.utils.YoutubeDLError:
            yd.close(); return None, None
        except Exception:
            yd.close(); raise
    if audio:
        y, res = run(f"ba[ext=m4a]{HTTP_ONLY}/ba[ext=mp3]{HTTP_ONLY}")
        chosen = _single_http(res, True)
    else:
        y, full = run(fmt_for(mode))
        chosen = _single_http(full, False)
        if chosen is None:
            if y: y.close()
            y, prog = run(progressive_fmt(mode))
            if _single_http(prog, False) and (full is None or _height_of(prog) >= _height_of(full)):
                chosen = prog
    try:
        if chosen is None: return None
        headers = dict(chosen.get("http_headers") or info.get("http_headers") or {})
        try:
            cookie = y.cookiejar.get_cookie_header(chosen["url"])
            if cookie: headers["Cookie"] = cookie
        except Exception:
            pass
    finally:
        if y: y.close()
    ext = str(chosen.get("ext") or "mp4").lower()
    meta = dict(info)                                   # أبعاد الصيغة المختارة فعلًا (مش أعلى صيغة في الفيديو)
    meta["width"], meta["height"] = chosen.get("width") or 0, chosen.get("height") or 0
    return DirectPlan(chosen["url"], headers, safe_filename(info.get("title") or it.title, ext), meta, audio)

async def send_direct(b, it, plan):
    """بث الملف من رابط المصدر لتليجرام مباشرةً (Range متوازي → رفع متوازي) بلا حفظ على القرص."""
    src = await asyncio.to_thread(fastio.HttpSource.open, plan.url, plan.name, plan.headers,
                                  PROXY or None, is_safe_url, max_size())
    src.cancelled = lambda: b.cancelled
    outdir = tempfile.mkdtemp(prefix="dl_")
    try:
        thumb = await get_thumb(plan.info, outdir)
        it.status, it.detail = "up", f"⚡ بث مباشر • {human_bytes(src.size)}"
        prog = make_upload_progress(it)
        t_s = time.monotonic()
        fid = await with_retry(send_media, b, it, src, plan.info, thumb, prog, tries=2)
        it.size = int(src.size or 0)
        it.v_up = it.size / max(time.monotonic() - t_s, 0.01)     # أبطأ طرف (تنزيل/رفع) لأنهم بيتم بالتوازي
        speed_note("up", it.v_up, it.size)
        return fid
    finally:
        shutil.rmtree(outdir, ignore_errors=True)

# ───────────── سيرفر تحميل خارجي اختياري (cobalt) ─────────────
def vidkraken_resolve(url, mode):
    """vidkraken.com: بيبعت الطلب وبيستنى الـ job يخلص. بيرجّع (رابط, اسم_ملف). (يوتيوب بس)"""
    import requests
    if mode == "audio": fmt = "audio-mp3"
    else:
        try: want = 1080 if mode == "best" else int(mode)
        except (TypeError, ValueError): want = 1080
        fmt = str(next((h for h in (1080, 720, 480, 360) if h <= want), 360))
    h = {"Authorization": "Bearer " + VIDKRAKEN_API_KEY, "Content-Type": "application/json", "User-Agent": UA}
    r = requests.post(VIDKRAKEN_URL + "/download", json={"url": url, "format": fmt}, headers=h, timeout=30)
    try: data = r.json()
    except ValueError: raise RuntimeError(f"vidkraken HTTP {r.status_code}")
    if r.status_code >= 400 or not data.get("jobId"):
        raise RuntimeError("vidkraken: " + str(data.get("error") or r.status_code))
    title = data.get("title") or "video"
    deadline = time.monotonic() + 300
    while time.monotonic() < deadline:
        time.sleep(2)
        g = requests.get(f"{VIDKRAKEN_URL}/download/{data['jobId']}", headers=h, timeout=30)
        try: st = g.json()
        except ValueError: continue
        link = st.get("downloadUrl")
        if link:
            return link, f"{title}.{'mp3' if fmt == 'audio-mp3' else 'mp4'}"
        if st.get("error") or str(st.get("status") or "").upper() in ("FAILED", "ERROR", "CANCELLED", "EXPIRED"):
            raise RuntimeError("vidkraken: " + str(st.get("error") or st.get("status")))
    raise RuntimeError("vidkraken: timeout")

def cobalt_resolve(url, mode):
    """بيجيب رابط تحميل من الخدمات الخارجية: vidkraken (يوتيوب) ثم cobalt. بيرجّع (رابط, اسم_ملف)."""
    import requests
    if VIDKRAKEN_API_KEY and is_youtube_url(url):
        try: return vidkraken_resolve(url, mode)
        except Exception as e:
            log.info("vidkraken failed (%s)%s", e, " — trying cobalt" if COBALT_API_URL else "")
            if not COBALT_API_URL: raise
    body = {"url": url, "filenameStyle": "basic"}
    if mode == "audio": body.update(downloadMode="audio", audioFormat="mp3")
    else: body.update(videoQuality="max" if mode == "best" else str(mode), youtubeVideoCodec="h264")
    headers = {"Accept": "application/json", "Content-Type": "application/json", "User-Agent": UA}
    if COBALT_API_KEY: headers["Authorization"] = "Api-Key " + COBALT_API_KEY
    r = requests.post(COBALT_API_URL + "/", json=body, headers=headers, timeout=40)
    try: data = r.json()
    except ValueError: raise RuntimeError(f"cobalt HTTP {r.status_code}")
    st = data.get("status")
    if st in ("tunnel", "redirect") and data.get("url"):
        return data["url"], data.get("filename") or "video.mp4"
    if st == "picker":
        for p in data.get("picker") or []:
            if p.get("url") and p.get("type") in ("video", None): return p["url"], "video.mp4"
    err = (data.get("error") or {}).get("code") if isinstance(data.get("error"), dict) else None
    raise RuntimeError("cobalt: " + str(err or st or "error"))

def cobalt_host():
    return (urlparse(COBALT_API_URL or VIDKRAKEN_URL).hostname or "").lower()

def cobalt_url_ok(u):
    host = (urlparse(u).hostname or "").lower()
    return host == cobalt_host() or is_safe_url(u)

def cobalt_fetch_file(url, outdir, name):
    """نزّل ملف cobalt (لو الحجم مجهول/مفيش Range) على القرص بالتتابع."""
    import requests
    path = os.path.join(outdir, name)
    with requests.get(url, stream=True, timeout=(15, 60), headers={"User-Agent": UA}) as r:
        r.raise_for_status()
        got = 0
        with open(path, "wb") as f:
            for chunk in r.iter_content(1 << 20):
                got += len(chunk)
                if got > max_size(): raise RuntimeError("الملف أكبر من الحد المسموح")
                f.write(chunk)
    return path

async def run_cobalt(b, it):
    it.status, it.detail = "dl", "🌐 بطلب الرابط من سيرفر التحميل الخارجي..."
    url, fname = await asyncio.to_thread(cobalt_resolve, it.url, b.mode)
    stem, ext = os.path.splitext(fname)
    if stem: it.title = stem[:100]
    ext = ext.lstrip(".").lower() or ("mp3" if b.mode == "audio" else "mp4")
    name = safe_filename(it.title, ext)
    try:
        src = await asyncio.to_thread(fastio.HttpSource.open, url, name, None, None, cobalt_url_ok, max_size())
        src.cancelled = lambda: b.cancelled
        it.status, it.detail = "up", f"⚡ بث مباشر • {human_bytes(src.size)}"
        return await with_retry(send_media, b, it, src, {"title": it.title}, None, make_upload_progress(it), tries=2)
    except asyncio.CancelledError:
        raise
    except Exception as e:
        log.info("cobalt stream unavailable (%s) — downloading to disk", e)
    outdir = tempfile.mkdtemp(prefix="dl_")
    try:
        task = asyncio.create_task(asyncio.to_thread(cobalt_fetch_file, url, outdir, name))
        path = await wait_with_progress(task, it, outdir)
        it.status, it.detail = "up", "جارٍ تهيئة الرفع..."
        return await with_retry(send_media, b, it, path, {"title": it.title}, None, make_upload_progress(it))
    finally:
        shutil.rmtree(outdir, ignore_errors=True)

async def send_media(b, it, src, info, thumb=None, progress=None):
    info = info or {}
    cap, kb = build_caption(it, info or it.info, b.mode), media_kb()
    if b.mode == "audio":
        m = await app.send_audio(b.chat_id, src, caption=cap, parse_mode=ParseMode.HTML,
                                 duration=int(info.get("duration") or 0),
                                 title=info.get("title"), performer=info.get("uploader"),
                                 thumb=thumb, reply_markup=kb, progress=progress)
        return m.audio.file_id if m.audio else None
    m = await app.send_video(b.chat_id, src, caption=cap, parse_mode=ParseMode.HTML,
                             duration=int(info.get("duration") or 0),
                             width=info.get("width") or 0, height=info.get("height") or 0,
                             thumb=thumb, supports_streaming=True, reply_markup=kb, progress=progress)
    if m.video: return m.video.file_id
    return m.document.file_id if m.document else None

IMG_EXT, VID_EXT = {".jpg", ".jpeg", ".png", ".webp"}, {".mp4", ".mov", ".mkv", ".webm", ".m4v"}

async def send_gallery(b, it, files, progress_factory=None):
    progress_factory = progress_factory or (lambda label: None)
    cap, ext = build_caption(it, {}), lambda f: os.path.splitext(f)[1].lower()
    imgs = [f for f in files if ext(f) in IMG_EXT and os.path.getsize(f) <= 10 * 1024 * 1024]
    vids = [f for f in files if ext(f) in VID_EXT]
    gifs = [f for f in files if ext(f) == ".gif"]
    docs = [f for f in files if f not in imgs and f not in vids and f not in gifs]
    first = True
    for i in range(0, len(imgs), 10):
        chunk = imgs[i:i + 10]
        try:
            if len(chunk) == 1:
                await app.send_photo(b.chat_id, chunk[0], caption=cap if first else None, parse_mode=ParseMode.HTML,
                                     progress=progress_factory("رفع صورة"))
            else:
                it.detail = f"رفع ألبوم الصور {i + 1}–{i + len(chunk)} من {len(imgs)}"
                await app.send_media_group(b.chat_id, [InputMediaPhoto(p, caption=cap if (first and j == 0) else None, parse_mode=ParseMode.HTML)
                                                       for j, p in enumerate(chunk)])
        except FloodWait as e:
            await asyncio.sleep(e.value + 1)
        except Exception:
            docs += chunk
        first = False
    for v in vids:
        await app.send_video(b.chat_id, v, caption=cap if first else None, parse_mode=ParseMode.HTML, supports_streaming=True,
                             progress=progress_factory("رفع فيديو")); first = False
    for g in gifs:
        await app.send_animation(b.chat_id, g, caption=cap if first else None, parse_mode=ParseMode.HTML,
                                 progress=progress_factory("رفع GIF")); first = False
    for d in docs:
        await app.send_document(b.chat_id, d, caption=cap if first else None, parse_mode=ParseMode.HTML,
                                progress=progress_factory("رفع ملف")); first = False

# ───────────── معالجة عنصر واحد ─────────────
class Flight:
    __slots__ = ("lock", "refs", "err", "err_at")
    def __init__(self):
        self.lock, self.refs, self.err, self.err_at = asyncio.Lock(), 0, None, 0.0

FLIGHTS = {}

class flight:
    """نفس (الفيديو + الجودة) مطلوب من أكتر من عنصر في نفس الوقت → واحد بس بيحمّل، والباقي بيستنى.
    لو اللي حمّل فشل، اللي مستنيين بياخدوا نفس الخطأ فورًا بدل ما كل واحد يعيد المحاولة ويستنى."""
    def __init__(self, key, batch):
        self.key, self.batch, self.f = key, batch, None
    async def __aenter__(self):
        f = FLIGHTS.get(self.key)
        if f is None: f = FLIGHTS[self.key] = Flight()
        f.refs += 1
        self.f = f
        try:
            await f.lock.acquire()
        except BaseException:
            self._unref()
            raise
        return f
    def _unref(self):
        self.f.refs -= 1
        if self.f.refs <= 0 and FLIGHTS.get(self.key) is self.f: FLIGHTS.pop(self.key, None)
    async def __aexit__(self, et, ev, tb):
        f = self.f
        if et is None:
            f.err = None
        elif issubclass(et, Exception) and not self.batch.cancelled and str(ev):
            f.err, f.err_at = str(ev), time.monotonic()
        f.lock.release()
        self._unref()
        return False

async def _send_from_cache(b, it, cm):
    """True لو العنصر اتبعت من الكاش (file_id متخزّن). file_id باظ → بيتمسح من الكاش."""
    fid = cache_get(it.key, cm)
    if not fid: return False
    try:
        it.status, it.detail = "up", "فوري ⚡"
        await send_media(b, it, fid, None)
        it.status, it.route, it.took = "done", "cache", time.monotonic() - it.t0
        record(b.user_id, it.title, b.mode, it.url)
        return True
    except asyncio.CancelledError:
        raise
    except Exception as e:
        log.warning("cache miss for %s: %s", it.key, e)
        if isinstance(e, BadRequest):
            db_exec("DELETE FROM cache WHERE key=? AND mode=?", (it.key, cm))
        it.status, it.detail = "wait", ""
        return False

async def run_item(b, it):
    async with b.sem:
        if b.cancelled:
            it.status, it.detail = "err", "أُلغي"
            return
        it.t0 = time.monotonic()
        it.is_cancelled = lambda: b.cancelled
        try: it.est = estimate_seconds(it.info, b.mode) or 0.0 if it.engine == "ytdlp" else 0.0
        except Exception: it.est = 0.0
        wm = wm_snapshot(b.mode) if it.engine == "ytdlp" else None   # إعدادات العلامة وقت بداية العنصر
        cm = cache_mode(b.mode, wm)
        try:
            if it.engine in ("ytdlp", "cobalt"):
                if await _send_from_cache(b, it, cm): return
                # لو نفس الفيديو بنفس الجودة بيتحمّل دلوقتي لحد تاني: نستنى ونستلمه من الكاش بدل ما نحمّله تاني
                async with flight((it.key, cm), b) as fl:
                    if fl.err and time.monotonic() - fl.err_at < 30:
                        raise RuntimeError(fl.err)
                    if await _send_from_cache(b, it, cm): return
                    await _fetch_and_send(b, it, cm, wm)
            else:
                await _fetch_and_send(b, it, cm, wm)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            it.status, it.detail = "err", clean_err(e)
            log.warning("item failed %s: %s", it.url, e)

async def _fetch_and_send(b, it, cm, wm):
    """تحميل/بث عنصر وإرساله (من غير الكاش). الأخطاء بتطلع لـ run_item."""
    if it.engine == "cobalt":
        it.status = "wait"
        async with user_sem(b.user_id), DL_SEM:
            if b.cancelled: raise RuntimeError("أُلغي")
            fid = await run_cobalt(b, it)
        if fid: cache_put(it.key, cm, fid)
        it.status = "done"; record(b.user_id, it.title, b.mode, it.url)
        return

    # ⚡ المسار السريع: بث مباشر من رابط المصدر لتليجرام (بدون تنزيل على السيرفر) لو الصيغة تسمح.
    # أي فشل هنا بيرجّع تلقائيًا للمسار العادي تحت — المستخدم مش بيشوف فرق غير في السرعة.
    if it.engine == "ytdlp" and cfg("xfer") == "direct" and not wm and not b.cancelled:
        plan = None
        try:
            it.status, it.detail = "dl", "⚡ بفحص أسرع مسار للإرسال..."
            async with PROBE_SEM:
                plan = await asyncio.to_thread(plan_direct, it, b.mode)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            log.info("direct plan unavailable for %s: %s", it.url, e)
        if plan:
            try:
                it.status, it.detail = "wait", ""
                async with user_sem(b.user_id), UP_SEM:
                    if b.cancelled: raise RuntimeError("أُلغي")
                    fid = await send_direct(b, it, plan)
                if fid: cache_put(it.key, cm, fid)
                it.status, it.route, it.took = "done", "direct", time.monotonic() - it.t0
                record(b.user_id, it.title, b.mode, it.url)
                it.info = None
                return
            except asyncio.CancelledError:
                raise
            except Exception as e:
                if b.cancelled: raise RuntimeError("أُلغي")
                log.warning("direct stream failed for %s (%s) — falling back to server download", it.url, e)
                it.status, it.detail = "dl", "جارٍ تجهيز التنزيل..."

    outdir = tempfile.mkdtemp(prefix="dl_")
    try:
        if it.engine == "gallery":
            it.status = "wait"
            async with user_sem(b.user_id), DL_SEM:
                it.status, it.detail = "dl", "جارٍ تجهيز تنزيل الصور..."
                task = asyncio.create_task(asyncio.to_thread(do_gallery, it.url, outdir))
                files = await wait_with_progress(task, it, outdir)
            if b.cancelled: raise RuntimeError("أُلغي")
            it.status = "wait"
            async with UP_SEM:
                it.status, it.detail = "up", f"بدء رفع {len(files)} ملف..."
                await with_retry(send_gallery, b, it, files,
                                 lambda label: make_upload_progress(it, label), tries=2)
            it.status = "done"; record(b.user_id, it.title, "gallery", it.url)
            return

        it.status = "wait"
        async with user_sem(b.user_id), DL_SEM:
            if b.cancelled: raise RuntimeError("أُلغي")
            it.status, it.detail = "dl", "جارٍ تجهيز التنزيل..."
            await wait_disk()
            loop = asyncio.get_running_loop()
            progress_state = {"updated": time.monotonic(), "started": time.monotonic()}
            hook = make_download_progress_hook(it, loop, progress_state)
            task = asyncio.create_task(asyncio.to_thread(
                do_download_fit, it, b.mode, outdir, hook))
            path, info, used = await wait_with_progress(task, it, outdir, progress_state)
            elapsed = time.monotonic() - progress_state["started"]
            it.size = os.path.getsize(path)
            it.v_dl = it.size / max(elapsed, 0.01)
            speed_note("dl", it.v_dl, it.size)
            it.detail = (f"<b>📊 100%</b>  {ui_bar(1, 12)}\n"
                         f"📦 {human_bytes(it.size)}  •  ⏱ مستغرق: {duration_text(elapsed)}\n"
                         "✅ اكتمل التنزيل")
            if wm and not b.cancelled:
                it.detail = "🔖 بيحط العلامة المائية..."
                path = await apply_watermark(path, wm, outdir)
                if os.path.getsize(path) > max_size():
                    raise RuntimeError("الملف بعد العلامة المائية أكبر من الحد المسموح")
        if b.cancelled: raise RuntimeError("أُلغي")
        if used != b.mode: log.info("quality lowered %s -> %s for %s", b.mode, used, it.url)

        it.status = "wait"
        async with UP_SEM:
            it.status, it.detail = "up", "جارٍ تهيئة الرفع..."
            prog = make_upload_progress(it)
            thumb = await get_thumb(info or it.info, outdir)         # صورة الفيديو الأصلية
            if not thumb and b.mode != "audio":
                thumb = await make_thumb(path, f"{outdir}/thumb.jpg")   # أو فريم من الفيديو نفسه
            t_up = time.monotonic()
            fid = await with_retry(send_media, b, it, path, info, thumb, prog)
            it.v_up = (it.size or os.path.getsize(path)) / max(time.monotonic() - t_up, 0.01)
            speed_note("up", it.v_up, it.size)
        if fid: cache_put(it.key, cm, fid)
        it.status, it.route, it.took = "done", "disk", time.monotonic() - it.t0
        record(b.user_id, it.title, b.mode, it.url)
    finally:
        it.info = None
        shutil.rmtree(outdir, ignore_errors=True)

# ───────────── شاشة الحالة ─────────────
SPINNER = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"

def batch_label(b):
    if b.items and all(i.engine == "gallery" for i in b.items):
        return "ملفات" if any(i.key.startswith("drv:") for i in b.items) else "صور"
    return mode_label(b.mode)

def stage_line(i):
    """مراحل العنصر بشكل مرئي: فحص ▸ تنزيل ▸ رفع (المرحلة الحالية عريضة)."""
    if "بث مباشر" in (i.detail or ""):
        return "✅ فحص  ▸  ⚡ <b>بث مباشر (تنزيل + رفع معًا)</b>"
    if i.status == "dl":
        return "✅ فحص  ▸  ⬇️ <b>تنزيل</b>  ▸  ▫️ رفع"
    return "✅ فحص  ▸  ✅ تنزيل  ▸  ⬆️ <b>رفع</b>"

def render(b, final=False):
    total = len(b.items)
    c = Counter(i.status for i in b.items)
    active = [i for i in b.items if i.status in ("dl", "up")]
    blocks = []
    for i in active[:12]:
        index = b.items.index(i) + 1
        icon, stage = ("⬇️", "جارٍ التنزيل") if i.status == "dl" else ("⬆️", "جارٍ الرفع إليك")
        blocks.append(f"{icon} <b>{index}/{total}</b> • {stage} {SPINNER[int(time.monotonic() * 2) % len(SPINNER)]}\n"
                      f"<b>{esc_t(i.title, 45)}</b>\n<i>{stage_line(i)}</i>\n{ui_quote(i.detail) if i.detail else ''}"
                      + (f"\n<i>🎯 متوقع ~{short_time(i.est)} • مضى {short_time(time.monotonic() - i.t0)}</i>"
                         if i.est and i.t0 else ""))
    if len(active) > 12: blocks.append(f"… و{len(active) - 12} عناصر تانية شغالة دلوقتي")
    if not active and not final and c["wait"]:
        blocks.append(f"⏳ <b>جارٍ التجهيز...</b> <i>({c['wait']} في الانتظار)</i>")
    txt = "\n\n".join(blocks)
    if not final and txt:
        txt = ui_title("🚀", "جارٍ التحميل", f"{batch_label(b)} • {total} عنصر") + "\n" + txt
    if not final and (c["done"] or c["err"]):
        txt += ((("\n\n" if txt else "") + f"✅ {c['done']}/{total} اتبعتوا")
                + (f"  •  ⏳ {c['wait']} بالانتظار" if c["wait"] else "")
                + (f"  •  ❌ {c['err']}" if c["err"] else ""))
        took_list = [i.took for i in b.items if i.status == "done" and i.took and i.route != "cache"]
        left = c["wait"] + len(active)
        if b.sequential and took_list and left:
            txt += f"\n⌛ <i>المتبقي تقريبًا ~{short_time(sum(took_list) / len(took_list) * left)}</i>"
    errs = [i for i in b.items if i.status == "err"]
    if errs: txt += "\n\n" + "\n\n".join(f"❌ <b>{esc_t(i.title, 40)}</b>\n{ui_quote(esc_t(i.detail, 170))}" for i in errs[-4:])
    txt = txt.strip()
    if final:
        secs = int(time.time() - b.started_at)
        took = f"{secs // 60}د {secs % 60}ث" if secs >= 60 else f"{secs} ث"
        stats = f"📦 {c['done']}/{total} عنصر  •  ⏱ {took}  •  🎞 {batch_label(b)}"
        vs = [i.v_up for i in b.items if i.status == "done" and i.v_up]
        if vs: stats += f"  •  ⚡ {sum(vs) / len(vs) / 1e6:.1f} MB/s"
        if c["done"] and not c["err"]: head = ui_title("✅", "اكتمل التحميل", "الملفات وصلتك فوق ☝️") + "\n" + stats
        elif c["done"]: head = ui_title("⚠️", "اكتمل جزئيًا") + "\n" + stats
        elif b.cancelled: head = ui_title("🛑", "تم الإلغاء") + "\n" + stats
        else: head = ui_title("❌", "فشل التحميل") + "\n" + stats
        def _done_line(i):
            line = f"✅ {esc_t(i.title, 45)}"
            if i.route == "cache": return line + "  ⚡ فوري (من الكاش)"
            nums = []
            if i.took: nums.append(f"⏱ {i.took:.1f}ث")
            if i.v_dl: nums.append(f"⬇️ {i.v_dl / 1e6:.1f} MB/s")
            if i.v_up: nums.append(f"⬆️ {i.v_up / 1e6:.1f} MB/s")
            if i.route == "direct": nums.append("🔀 مباشر")
            if i.est and i.took: nums.append(f"🎯 متوقع {short_time(i.est)}")
            return line + ("\n   " + " • ".join(nums) if nums else "")
        done_titles = [_done_line(i) for i in b.items if i.status == "done"]
        if len(done_titles) > 6: done_titles = done_titles[:6] + [f"… و{len(done_titles) - 6} كمان"]
        if done_titles: head += "\n" + ui_quote(*done_titles)
        txt = head + ("\n\n" + txt if txt else "")
    elif b.cancelled: txt += "\n\n🛑 <i>جاري الإلغاء بعد العناصر الجارية...</i>"
    return txt.strip() or ui_note("wait", "جارٍ التجهيز...", "ثواني وهنبدأ")

PREVIEWS = set()      # رسائل كارت المعاينة (صورة + كابشن) — مش غلاف /start

async def send_card(m, wait, text, kb, info):
    """كارت واحد مدمج: ثامنيل الفيديو + المعلومات + أزرار الجودة. لو فشل بيرجّع None والمتصل بيستخدم النص."""
    url = thumbnail_url(info)
    cap = pe_html(text)
    if not url or len(cap) > 1024: return None
    try:
        if not await asyncio.to_thread(is_safe_url, url): return None
        card = await app.send_photo(m.chat.id, url, caption=cap, reply_markup=kb, reply_to_message_id=m.id)
    except Exception as e:
        log.debug("preview card failed: %s", e)
        return None
    if len(PREVIEWS) > 3000: PREVIEWS.clear()
    PREVIEWS.add((card.chat.id, card.id))
    try: await wait.delete()
    except Exception: pass
    return card

async def safe_edit(msg, text, kb=None):
    t = pe_html(text)
    is_card = bool(getattr(msg, "photo", None))
    async def _edit(txt, k):
        if not is_card: return await msg.edit_text(txt, reply_markup=k)
        if len(txt) > 1024:      # حد الكابشن: نبسّط النص بدل ما التعديل يفشل
            txt = html.escape(html.unescape(re.sub(r"<[^>]+>", "", txt))[:1000], quote=False)
        return await msg.edit_caption(txt, reply_markup=k)
    try: await _edit(t, kb)
    except MessageNotModified: pass
    except FloodWait as e: await asyncio.sleep(min(e.value, 15))
    except Exception as e:
        if pe_active():          # ممكن الإيموجي البريميوم مرفوض (صاحب البوت من غير Premium) → نجرب من غيره
            plainify_kb(kb)
            try:
                await _edit(text, kb)
                PE["broken"] = True
                log.warning("premium emoji rejected (%s); disabled until admin re-enables", e)
            except MessageNotModified: pass
            except Exception as e2: log.debug("edit failed: %s", e2)
        else: log.debug("edit failed: %s", e)

async def replace_with_reply(old_msg, original_msg, text, kb=None):
    try:
        await old_msg.delete()
    except Exception as e:
        log.debug("could not delete metadata wait message: %s", e)
        await old_msg.edit_text(text, reply_markup=kb)
        return old_msg
    return await original_msg.reply_text(text, reply_markup=kb)

async def drop_preview(b):
    pm, b.preview = b.preview, None
    if pm:
        try: await pm.delete()
        except Exception as e: log.debug("preview delete failed: %s", e)

async def toast(chat_id, text, secs=6):
    """رسالة قصيرة بتتمسح لوحدها بعد ثواني (تأكيد من غير ما تتراكم الرسايل)."""
    try:
        m = await app.send_message(chat_id, text)
        await asyncio.sleep(secs)
        await m.delete()
    except Exception as e:
        log.debug("toast failed: %s", e)

async def run_batch(b):
    b.started = True
    b.started_at = time.time()
    if b.sequential and len(b.items) > 1:
        async def _seq():
            for it in b.items:          # واحد ورا التاني بالترتيب: ينزّل ويبعت، وبعدها اللي بعده
                await run_item(b, it)
        tasks = [asyncio.create_task(_seq())]
    else:
        tasks = [asyncio.create_task(run_item(b, it)) for it in b.items]
    async def loop():
        tick = 0
        while not b.done:
            await safe_edit(b.msg, render(b), cancel_kb(b))
            if ChatAction and tick % 2 == 0 and any(it.status in ("dl", "up") for it in b.items):
                action = (ChatAction.UPLOAD_AUDIO if b.mode == "audio"
                          else ChatAction.UPLOAD_PHOTO if all(it.engine == "gallery" for it in b.items)
                          else ChatAction.UPLOAD_VIDEO)
                try: await app.send_chat_action(b.chat_id, action)
                except Exception: pass
            tick += 1
            await asyncio.sleep(min(8.0, max(2.0, len(batches) / 15)))    # كتير شغّالين = تحديث أبطأ (حماية من FloodWait)
    ui = asyncio.create_task(loop())
    await asyncio.gather(*tasks, return_exceptions=True)
    b.done = True
    ui.cancel()
    await safe_edit(b.msg, render(b, final=True), after_kb())
    batches.pop(b.id, None)
    await drop_preview(b)
    done = sum(it.status == "done" for it in b.items)
    if done and not b.cancelled:
        what = (("وصلت الملفات 📁" if any(it.key.startswith("drv:") for it in b.items) else "وصلت الصور 📷")
                if all(it.engine == "gallery" for it in b.items)
                else "وصلك الصوت 🎧" if b.mode == "audio" else "وصلك الفيديو 🎬" if done == 1 else f"وصلتك {done} فيديوهات 🎬")
        await app.send_message(b.chat_id, pe_html(ui_note("ok", what, "الملفات وصلتك فوق ☝️")), reply_markup=after_kb())

async def begin(b, answer=None):
    """يبدأ الدفعة. لو الأدمن ضبط حصة يومية بيتطبق هنا (الأدمن مستثنى)."""
    quota = cfg_int("quota")
    if quota and b.user_id not in ADMIN_IDS:
        used = db_exec("SELECT COUNT(*) FROM history WHERE user_id=? AND ts>?",
                       (b.user_id, int(time.time()) - 86400))[0][0]
        left = quota - used
        if left <= 0:
            batches.pop(b.id, None)
            await drop_preview(b)
            return await safe_edit(b.msg, ui_note("stop", "وصلت لحصتك اليومية", f"{quota} تحميل كل 24 ساعة — جرّب لاحقًا."), back_kb())
        if len(b.items) > left:
            b.items = b.items[:left]
    asyncio.create_task(run_batch(b))

# ───────────── الشاشات ─────────────
# ───────────── نظام التصميم الموحّد (UI kit) ─────────────
LINE = "━━━━━━━━━━━━━━"

def esc_t(text, limit=None):
    """نص آمن للعرض جوه رسائل HTML/Markdown (العناوين والأخطاء وأسماء المستخدمين)."""
    t = " ".join(str(text or "").split())
    if limit and len(t) > limit: t = t[:limit - 1] + "…"
    t = html.escape(t, quote=False).replace("`", "'")
    t = re.sub(r"([*_~|])\1+", r"\1", t)
    return t.replace("](", "] (")

def ui_title(icon, text, sub=""):
    """عنوان الشاشة: أيقونة + عنوان عريض (+ سطر فرعي) + فاصل."""
    return f"{icon} <b>{text}</b>" + (f"\n<i>{sub}</i>" if sub else "") + f"\n{LINE}"

def ui_quote(*lines):
    return "<blockquote>" + "\n".join(str(x) for x in lines if x) + "</blockquote>"

def ui_bar(ratio, width=10):
    filled = int(min(max(float(ratio), 0.0), 1.0) * width)
    return "▰" * filled + "▱" * (width - filled)

def ui_meter(value, hi, width=8):
    """عداد صغير للقيم (سرعة مثلًا) من 0 لـ hi."""
    try: r = min(max(float(value) / float(hi), 0.0), 1.0)
    except (TypeError, ValueError, ZeroDivisionError): r = 0.0
    return "▮" * int(r * width) + "▯" * (width - int(r * width))

def nav_rows(back=None):
    """صف تنقل موحّد: رجوع + الرئيسية (أو الرئيسية بس)."""
    return [B("⬅️ رجوع", back), B("🏠 الرئيسية", "m")] if back else [B("🏠 القائمة الرئيسية", "m")]

NOTE_ICONS = {"ok": "✅", "err": "❌", "warn": "⚠️", "info": "💡", "lock": "🔒", "wait": "⏳", "stop": "🚫", "ask": "❔"}

def ui_note(kind, text, sub=""):
    """رسالة حالة موحّدة: أيقونة + عنوان عريض (+ تفاصيل في اقتباس)."""
    return f"{NOTE_ICONS.get(kind, 'ℹ️')} <b>{text}</b>" + (f"\n{ui_quote(sub)}" if sub else "")

def ui_prompt(icon, title, *lines):
    """شاشة طلب إدخال (البوت منتظر رد من المستخدم)."""
    return ui_title(icon, title) + ("\n" + ui_quote(*lines) if lines else "") + "\n\n<i>✍️ ابعت دلوقتي 👇</i>"

def cancel_row(back="m", label="⬅️ رجوع"):
    return [B(label, back)]

LOCKED_HTML = ui_note("lock", "البوت ده خاص", "كلّم صاحب البوت علشان يفعّلك.")
MAINT_HTML = ui_note("wait", "البوت في صيانة دلوقتي", "جرّب بعد شوية 🙏")

def uget(uid, key, default=""):
    r = db_exec("SELECT value FROM prefs WHERE user_id=? AND key=?", (uid, key))
    return r[0][0] if r else default

def uset(uid, key, value):
    db_exec("INSERT OR REPLACE INTO prefs(user_id, key, value) VALUES (?,?,?)", (uid, key, str(value)))

# ───────────── السجل والمفضلة والتقارير ─────────────
PAGE = 5
FAV_LIMIT = 100
NUMS = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣"]
HIST_FILTERS = {                      # مفتاح: (عنوان الشاشة، نص الزر، شرط SQL)
    "a": ("الكل", "📋 الكل", ""),
    "v": ("فيديو", "🎬 فيديو", " AND mode NOT IN ('audio','gallery')"),
    "m": ("صوت", "🎧 صوت", " AND mode='audio'"),
    "g": ("صور", "📷 صور", " AND mode='gallery'"),
}
SITE_NAMES = {"youtube.com": "YouTube", "youtu.be": "YouTube", "tiktok.com": "TikTok", "instagram.com": "Instagram",
              "facebook.com": "Facebook", "fb.watch": "Facebook", "twitter.com": "X", "x.com": "X",
              "reddit.com": "Reddit", "vimeo.com": "Vimeo", "pinterest.com": "Pinterest", "threads.net": "Threads",
              "soundcloud.com": "SoundCloud", "dailymotion.com": "Dailymotion", "twitch.tv": "Twitch"}

def ago(ts):
    sec = max(0, int(time.time()) - int(ts or 0))
    if sec < 60: return "الآن"
    if sec < 3600: return f"منذ {sec // 60} د"
    if sec < 86400: return f"منذ {sec // 3600} س"
    return f"منذ {sec // 86400} يوم"

def clean_t(text, limit=42):
    return esc_t(text, limit)

def site_of(url):
    try: host = (urlparse(url or "").hostname or "").lower()
    except ValueError: return ""
    if host.startswith("www."): host = host[4:]
    for key, name in SITE_NAMES.items():
        if host == key or host.endswith("." + key): return name
    parts = host.split(".")
    return ".".join(parts[-2:]) if len(parts) >= 2 else host

def _qlabel(mode):
    return "صور" if mode == "gallery" else mode_label(mode)

def me_text(uid):
    r = db_exec("SELECT downloads FROM users WHERE id=?", (uid,))
    total = r[0][0] if r else 0
    week = db_exec("SELECT COUNT(*) FROM history WHERE user_id=? AND ts>?", (uid, int(time.time()) - 7 * 86400))[0][0]
    favs = db_exec("SELECT COUNT(*) FROM favorites WHERE user_id=?", (uid,))[0][0]
    sites = Counter(x for x in (site_of(u) for (u,) in db_exec(
        "SELECT url FROM history WHERE user_id=? AND url!='' ORDER BY ts DESC LIMIT 300", (uid,))) if x)
    modes = Counter(m for (m,) in db_exec("SELECT mode FROM history WHERE user_id=? ORDER BY ts DESC LIMIT 300", (uid,)))
    lines = [ui_title("📊", "لوحة تحميلاتي"),
             f"📥 الإجمالي: <b>{total}</b>   📅 آخر 7 أيام: <b>{week}</b>   ⭐ مفضلة: <b>{favs}</b>"]
    facts = []
    if sites:
        name, n = sites.most_common(1)[0]; facts.append(f"🌐 أكتر موقع: <b>{esc_t(name)}</b> ({n})")
    if modes:
        m, n = modes.most_common(1)[0]; facts.append(f"🎞 جودتك الأكثر: <b>{_qlabel(m)}</b> ({n})")
    if facts: lines += ["", ui_quote(*facts)]
    lines += ["", "<i>اختار من الأزرار 👇</i>"]
    return "\n".join(lines)

def me_kb():
    return KB([B("📜 السجل", "me|h|a|0", S.SUCCESS), B("⭐ المفضلة", "me|f|0", S.SUCCESS)],
              [B("🗑 مسح السجل", "me|clr", S.DANGER)],
              nav_rows())

def _nav_row(base, page, pages):
    row = []
    if page > 0: row.append(B("◀️", f"{base}|{page - 1}"))
    row.append(B(f"{page + 1}/{pages}", "nop"))
    if page < pages - 1: row.append(B("▶️", f"{base}|{page + 1}"))
    return row

def hist_view(uid, flt="a", page=0):
    flt = flt if flt in HIST_FILTERS else "a"
    cond = HIST_FILTERS[flt][2]
    total = db_exec(f"SELECT COUNT(*) FROM history WHERE user_id=?{cond}", (uid,))[0][0]
    pages = max(1, -(-total // PAGE)); page = min(max(page, 0), pages - 1)
    rows = db_exec(f"SELECT rowid, title, mode, ts, url FROM history WHERE user_id=?{cond} "
                   "ORDER BY ts DESC LIMIT ? OFFSET ?", (uid, PAGE, page * PAGE))
    favs = {r[0] for r in db_exec("SELECT url FROM favorites WHERE user_id=?", (uid,))}
    lines = [ui_title("📜", "سجل تحميلاتك", f"{HIST_FILTERS[flt][0]} • {total} عنصر • صفحة {page + 1}/{pages}")]
    if not rows: lines.append(ui_quote("لسه مفيش تحميلات هنا."))
    for i, (rid, title, mode, ts, url) in enumerate(rows):
        extra = f" • 🌐 {esc_t(site_of(url))}" if url and site_of(url) else (" • 🕰 قديم" if not url else "")
        lines.append(f"{NUMS[i]} <b>{clean_t(title)}</b>\n      <i>{_qlabel(mode)} • {ago(ts)}{extra}</i>")
    if rows: lines += ["", "<i>🔁 إعادة التحميل  •  ⭐ حفظ في المفضلة</i>"]
    kb = [[B(("✅ " if k == flt else "") + v[1], f"me|h|{k}|0", S.SUCCESS if k == flt else S.PRIMARY)
           for k, v in HIST_FILTERS.items()]]
    again = [B(f"🔁 {i + 1}", f"hx|{r[0]}", S.SUCCESS) for i, r in enumerate(rows) if r[4]]
    star = [B(f"{'❤️' if r[4] in favs else '⭐'} {i + 1}", f"fv|{r[0]}|{flt}|{page}") for i, r in enumerate(rows) if r[4]]
    if again: kb.append(again)
    if star: kb.append(star)
    if pages > 1: kb.append(_nav_row(f"me|h|{flt}", page, pages))
    kb.append(nav_rows("me"))
    return "\n".join(lines), KB(*kb)

def fav_view(uid, page=0):
    total = db_exec("SELECT COUNT(*) FROM favorites WHERE user_id=?", (uid,))[0][0]
    pages = max(1, -(-total // PAGE)); page = min(max(page, 0), pages - 1)
    rows = db_exec("SELECT rowid, title, url, ts FROM favorites WHERE user_id=? ORDER BY ts DESC LIMIT ? OFFSET ?",
                   (uid, PAGE, page * PAGE))
    lines = [ui_title("⭐", "المفضلة", f"{total} عنصر • صفحة {page + 1}/{pages}")]
    if not rows: lines.append(ui_quote("لسه مفيش حاجة هنا.", "من 📜 السجل اضغط ⭐ جنب أي تحميل علشان تحفظه."))
    for i, (rid, title, url, ts) in enumerate(rows):
        lines.append(f"{NUMS[i]} <b>{clean_t(title)}</b>\n      <i>🌐 {esc_t(site_of(url)) or '—'} • {ago(ts)}</i>")
    if rows: lines += ["", "<i>🔁 تحميل  •  🗑 حذف من المفضلة</i>"]
    kb = []
    if rows:
        kb.append([B(f"🔁 {i + 1}", f"fx|{r[0]}", S.SUCCESS) for i, r in enumerate(rows)])
        kb.append([B(f"🗑 {i + 1}", f"fd|{r[0]}|{page}", S.DANGER) for i, r in enumerate(rows)])
    if pages > 1: kb.append(_nav_row("me|f", page, pages))
    kb.append(nav_rows("me"))
    return "\n".join(lines), KB(*kb)

def report_text(hours=24):
    since = int(time.time()) - hours * 3600
    total_users = db_exec("SELECT COUNT(*) FROM users")[0][0]
    new = db_exec("SELECT COUNT(*) FROM users WHERE first_seen>?", (since,))[0][0]
    rows = db_exec("SELECT user_id, mode, url FROM history WHERE ts>?", (since,))
    sites = Counter(x for x in (site_of(r[2]) for r in rows) if x)
    modes = Counter(_qlabel(r[1]) for r in rows)
    top_user = Counter(r[0] for r in rows).most_common(1)
    lines = [ui_title("📈", f"تقرير آخر {hours} ساعة"),
             f"👥 المستخدمين: <b>{total_users}</b>  (🆕 +{new})",
             f"🔥 نشطين: <b>{len({r[0] for r in rows})}</b>   📥 تحميلات: <b>{len(rows)}</b>"]
    facts = []
    if sites: facts.append("🌐 المواقع: " + " • ".join(f"{esc_t(k)} ({v})" for k, v in sites.most_common(5)))
    if modes: facts.append("🎞 الجودات: " + " • ".join(f"{esc_t(k)} ({v})" for k, v in modes.most_common(4)))
    if top_user: facts.append(f"🏆 أنشط مستخدم: <code>{top_user[0][0]}</code> ({top_user[0][1]} تحميل)")
    if facts: lines += ["", ui_quote(*facts)]
    return "\n".join(lines)

async def daily_report_loop():
    """تقرير يومي تلقائي للأدمن (الساعة DAILY_REPORT_HOUR بتوقيت UTC، الافتراضي 6؛ اكتب off للإيقاف)."""
    raw = os.getenv("DAILY_REPORT_HOUR", "6").strip().lower()
    if raw in ("off", "no", "false", "-1", "") or not ADMIN_IDS: return
    try: hour = int(raw) % 24
    except ValueError: return
    while True:
        await asyncio.sleep(300)
        try:
            now = time.gmtime()
            today = time.strftime("%Y-%m-%d", now)
            if now.tm_hour != hour: continue
            last = db_exec("SELECT value FROM settings WHERE key='last_report'")
            if last and last[0][0] == today: continue
            db_exec("INSERT OR REPLACE INTO settings(key, value) VALUES ('last_report', ?)", (today,))
            text = report_text(24)
            for aid in ADMIN_IDS:
                try: await app.send_message(aid, text)
                except Exception as e: log.info("daily report to %s failed: %s", aid, e)
        except Exception as e:
            log.warning("daily report loop: %s", e)

def greeting():
    hour = _dt.now(_TZ).hour if _TZ else (time.gmtime().tm_hour + 2) % 24
    if 5 <= hour < 12: return "صباح الخير ☀️"
    if 12 <= hour < 17: return "نهارك سعيد 🌤"
    if 17 <= hour < 21: return "مساء الخير 🌇"
    return "ليلة سعيدة 🌙"

def welcome_text(name, uid=None):
    text = (ui_title("🎬", "بوت تحميل الفيديوهات", "أسرع • أدق • أشيك ✨") + f"\n{greeting()}  <b>{esc_t(name, 30) or 'بيك'}</b> 👋\n\n"
            + ui_quote("🔗 ابعت أي رابط (أو أكتر من رابط)",
                       "🎥 فيديو بكل الجودات  •  🎧 MP3  •  📷 صور",
                       "📘 فيسبوك  •  📁 جوجل درايف  •  ▶️ يوتيوب وغيرهم",
                       f"🌐 +{SITE_COUNT} موقع  •  ⚡ تحميل فوري")
            + "\n<i>👇 اضغط «تحميل» أو ابعت الرابط مباشرة</i>")
    strip = []
    try:
        if speed_known(): strip.append(f"🚀 ⬇️ {speed_get('dl') / 1e6:.0f} • ⬆️ {speed_get('up') / 1e6:.0f} MB/s")
        if uid is not None:
            w = db_exec("SELECT COUNT(*) FROM watch WHERE user_id=?", (uid,))[0][0]
            if w: strip.append(f"🔔 {w} قناة مراقبة")
    except Exception: pass
    if strip: text += "\n\n" + "<i>" + "  •  ".join(strip) + "</i>"
    if uid is not None:
        try:
            r = db_exec("SELECT downloads FROM users WHERE id=?", (uid,))
            fav = db_exec("SELECT COUNT(*) FROM favorites WHERE user_id=?", (uid,))[0][0]
            if r and r[0][0]:
                text += f"\n\n📥 <b>{r[0][0]}</b> تحميل" + (f"  •  ⭐ <b>{fav}</b> مفضلة" if fav else "")
        except Exception: pass
    return text

HELP = (ui_title("❓", "طريقة الاستخدام") + "\n"
        + ui_quote("1️⃣ ابعت لينك (أو لينكات كتير في رسالة واحدة)",
                   "2️⃣ اختار الجودة من الأزرار",
                   "3️⃣ استنى وهيوصلك الفيديو ⚡")
        + "\n\n<b>💡 مميزات</b>\n"
        "🖼 كارت معاينة بالثامنيل والمدة وكل الجودات وأحجامها (بدون ~ = حجم دقيق)\n"
        "📘 فيسبوك: فيديوهات وريلز وأكتر من لينك مرة واحدة\n"
        "📁 جوجل درايف: ملفات ومجلدات (المشاركة «أي شخص معه الرابط»)\n"
        "📋 لينك Playlist: بتختار الفيديوهات (أزرار أو أرقام زي 1-5, 8) وبتتحمّل واحد ورا التاني\n"
        "🔔 /watch رابط_قناة: أي فيديو جديد بيتحمّل ويتبعتلك لوحده\n"
        "📷 لينكات الصور والألبومات بتتبعت صور\n"
        "🔎 لو الموقع مش معروف، بدوّر على الفيديو جوه الصفحة لوحدي\n"
        "⚡ الملفات المتحمّلة قبل كده بتتبعت فورًا من الكاش\n"
        "⚙️ من الإعدادات تثبّت جودة افتراضية وتتخطى سؤال الجودة\n"
        "🔁 من «تحميلاتي» تعيد أي تحميل، و⭐ تحفظه في المفضلة\n\n"
        "<b>⌨️ الأوامر</b>\n"
        "/start القائمة  •  /history السجل  •  /favorites المفضلة  •  /settings الإعدادات  •  /watch مراقبة قناة")

def sites_text():
    return (ui_title("🌐", "المواقع المدعومة", f"أكتر من {SITE_COUNT} موقع") + "\n"
            "<b>🎥 تواصل اجتماعي</b>\n" + ui_quote("يوتيوب • تيك توك • انستجرام • فيسبوك • X • ثريدز • ريديت • لينكدإن") + "\n"
            "<b>🎬 منصات فيديو</b>\n" + ui_quote("فيميو • ديلي موشن • تويتش • بيليبيلي • رومبل • Streamable • VK • OK.ru") + "\n"
            "<b>🎧 صوت</b>\n" + ui_quote("ساوند كلاود • باندكامب • ميكس كلاود") + "\n"
            "<b>📷 صور وألبومات</b>\n" + ui_quote("بنترست • تمبلر • فليكر • صور انستجرام وX وريديت وفيسبوك") + "\n"
            "<b>📁 ملفات</b>\n" + ui_quote("جوجل درايف (ملفات ومجلدات)") + "\n"
            "🔎 أي صفحة فيها فيديو، حتى لو الموقع مش في القايمة\n\n"
            "<i>⚠️ مش بيشتغل مع المحتوى المحمي بـ DRM (نتفلكس، ديزني+، شاهد VIP...) "
            "ولا المحتوى الخاص، ومحجوب المحتوى المخالف لقواعد تليجرام.</i>")

COVER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets", "cover.jpg")

def cover_active():
    return cfg("cover") == "1" and os.path.exists(COVER_PATH)

async def send_home(chat_id, text, kb):
    """الترحيب: صورة الغلاف + الكابشن + الأزرار (أو رسالة نصية لو الغلاف مقفول/ناقص). بيرجّع الرسالة."""
    if cover_active():
        fid = cfg("cover_fid")
        for src in ([fid] if fid else []) + [COVER_PATH]:
            try:
                m = await app.send_photo(chat_id, src, caption=pe_html(text), reply_markup=kb)
                if m and m.photo and m.photo.file_id != fid: cfg_set("cover_fid", m.photo.file_id)
                return m
            except FloodWait as e:
                await asyncio.sleep(min(e.value, 10))
            except Exception as e:
                log.info("cover send failed (%s)%s", e, " — retrying with file" if src == fid else "")
                if src == fid: cfg_set("cover_fid", "")
    return await app.send_message(chat_id, pe_html(text), reply_markup=kb)

async def show_home(cq):
    """الرجوع للرئيسية من أي شاشة: بيحافظ على شكل الغلاف (تعديل الكابشن لو الرسالة صورة، وإلا استبدال بصورة)."""
    uid, msg = cq.from_user.id, cq.message
    text, kb = welcome_text(cq.from_user.first_name or "", uid), menu_kb(uid)
    if not cover_active():
        return await show(cq, text, kb)
    if getattr(msg, "photo", None) and (msg.chat.id, msg.id) not in PREVIEWS:
        try: return await msg.edit_caption(pe_html(text), reply_markup=kb)
        except MessageNotModified: return
        except Exception as e: log.debug("edit_caption failed: %s", e)
    try: await msg.delete()
    except Exception: pass
    return await send_home(msg.chat.id, text, kb)

async def show(target, text, kb):
    if hasattr(target, "data"):
        msg = target.message
        if getattr(msg, "photo", None):      # رسالة الغلاف (صورة) ما ينفعش تتعدّل لنص → نبدّلها برسالة نصية
            try: await msg.delete()
            except Exception: pass
            return await app.send_message(msg.chat.id, pe_html(text), reply_markup=kb)
        await safe_edit(msg, text, kb)
    else:
        await target.reply_text(pe_html(text), reply_markup=kb)

def _dl_stream(n):
    req = urllib.request.Request(f"https://speed.cloudflare.com/__down?bytes={n}", headers={"User-Agent": UA})
    got = 0
    with urllib.request.urlopen(req, timeout=30) as r:
        while True:
            chunk = r.read(1 << 20)
            if not chunk: break
            got += len(chunk)
    return got

def speed_download_test(streams=4, size=25 * 1024 * 1024):
    from concurrent.futures import ThreadPoolExecutor
    t = time.monotonic()
    with ThreadPoolExecutor(streams) as ex:
        total = sum(ex.map(_dl_stream, [size] * streams))
    return total / max(time.monotonic() - t, 0.001) / 1e6  # MB/s decimal, aggregate streams

def _read_text(path):
    try:
        with open(path, "r", encoding="ascii") as f: return f.read().strip()
    except (OSError, UnicodeError):
        return None

def _cgroup_memory():
    pairs = (("/sys/fs/cgroup/memory.current", "/sys/fs/cgroup/memory.max"),
             ("/sys/fs/cgroup/memory/memory.usage_in_bytes", "/sys/fs/cgroup/memory/memory.limit_in_bytes"),
             ("/sys/fs/cgroup/memory.usage_in_bytes", "/sys/fs/cgroup/memory.limit_in_bytes"))
    for current_path, limit_path in pairs:
        current, raw_limit = _read_text(current_path), _read_text(limit_path)
        try:
            if current is None or raw_limit is None or raw_limit == "max": continue
            current, limit = int(current), int(raw_limit)
            if 0 < limit < (1 << 60): return current, limit
        except (TypeError, ValueError, OverflowError):
            continue
    return None, None

def _cgroup_cpu_limit():
    raw = _read_text("/sys/fs/cgroup/cpu.max")
    if raw:
        try:
            quota, period = raw.split()[:2]
            if quota != "max" and int(period) > 0: return int(quota) / int(period)
        except (ValueError, ZeroDivisionError):
            pass
    quota, period = _read_text("/sys/fs/cgroup/cpu/cpu.cfs_quota_us"), _read_text("/sys/fs/cgroup/cpu/cpu.cfs_period_us")
    try:
        if quota and period and int(quota) > 0 and int(period) > 0: return int(quota) / int(period)
    except (ValueError, ZeroDivisionError):
        pass
    return None

def _process_rss_bytes():
    status = _read_text("/proc/self/status")
    if status:
        for line in status.splitlines():
            if line.startswith("VmRSS:"):
                try: return int(line.split()[1]) * 1024
                except (IndexError, ValueError): break
    return None

def _allowed_cpu_count():
    try: return len(os.sched_getaffinity(0))
    except (AttributeError, OSError): return os.cpu_count()

def _cpu_sample_percent(interval=0.4):
    """نسبة استهلاك عملية البوت من نواة واحدة خلال عينة قصيرة؛ قد تتجاوز 100% عند تعدد الخيوط."""
    wall_start, cpu_start = time.monotonic(), time.process_time()
    time.sleep(interval)
    elapsed = max(time.monotonic() - wall_start, 0.001)
    return max(0.0, (time.process_time() - cpu_start) / elapsed * 100)

def runtime_metrics_text():
    cpu_pct = _cpu_sample_percent()
    cores = _allowed_cpu_count()
    cpu_limit = _cgroup_cpu_limit()
    rss = _process_rss_bytes()
    mem_current, mem_limit = _cgroup_memory()
    uptime = max(0, int(time.monotonic() - PROCESS_STARTED_AT))
    days, rem = divmod(uptime, 86400)
    hours, rem = divmod(rem, 3600)
    minutes, seconds = divmod(rem, 60)
    uptime_text = f"{days}ي {hours:02}س {minutes:02}د" if days else f"{hours:02}س {minutes:02}د {seconds:02}ث"
    lines = [f"🖥 CPU عملية البوت: {cpu_pct:.1f}% من نواة واحدة"
             + (f" | حصة cgroup: {cpu_limit:.2f} نواة" if cpu_limit else f" | أنوية CPU المسموحة: {cores or 'غير متاح'}")]
    if mem_current is not None and mem_limit:
        lines.append(f"🧠 RAM الحاوية: {mem_current / 1048576:.0f}/{mem_limit / 1048576:.0f} MiB")
    else:
        lines.append("🧠 RAM الحاوية: حد cgroup غير متاح")
    if rss is not None: lines.append(f"   ذاكرة عملية البوت RSS: {rss / 1048576:.0f} MiB")
    paths = [("تنزيلات /tmp", tempfile.gettempdir())]
    data_dir = os.path.dirname(os.path.abspath(DB_PATH)) or "."
    if os.path.isdir(data_dir) and os.path.realpath(data_dir) != os.path.realpath(tempfile.gettempdir()):
        paths.append(("بيانات DB", data_dir))
    for label, path in paths:
        try:
            disk = shutil.disk_usage(path)
            lines.append(f"💾 {label}: متاح {disk.free / 1073741824:.2f}/{disk.total / 1073741824:.2f} GiB")
        except OSError:
            lines.append(f"💾 {label}: غير متاح")
    lines.append(f"⏱ مدة تشغيل العملية: {uptime_text}")
    def _gate(label, g):
        cap = g.n or "∞"
        return f"{label} {g.active}/{cap}" + (f" (+{g.waiting} منتظر)" if g.waiting else "")
    lines.append("🚦 " + " • ".join([_gate("تنزيل", DL_SEM), _gate("رفع", UP_SEM), _gate("فحص", PROBE_SEM)])
                 + f" • دفعات {len(batches)} • كاش فحص {len(PROBE_CACHE)}")
    return "\n".join(lines)

_speed_running = False

async def speed_test(cq):
    """يقيس سرعة التحميل من النت وسرعة الرفع لتليجرام من السيرفر اللي البوت شغال عليه."""
    global _speed_running
    if _speed_running:
        return await cq.answer("⏳ الاختبار شغال دلوقتي", show_alert=True)
    _speed_running = True
    msg, path = cq.message, None
    again = KB([B("🔄 اختبار تاني", "ad|sp", S.SUCCESS)], [B("⬅️ رجوع", "ad")])
    try:
        await safe_edit(msg, ui_title("⚡", "اختبار السرعة", "1/2 • التنزيل") + "\n"
                        + ui_quote("⬇️ عينة من Cloudflare: 4 اتصالات × 25 MiB..."))
        try:
            dl = await asyncio.to_thread(speed_download_test)
            dl_txt = f"<b>{dl:.1f} MB/s</b> (≈ {dl*8:.0f} Mbps)"
        except Exception as e:
            dl, dl_txt = None, f"فشل ({esc_t(clean_err(e), 40)})"
        await safe_edit(msg, ui_title("⚡", "اختبار السرعة", "2/2 • الرفع") + "\n"
                        + ui_quote(f"⬇️ Cloudflare: {dl_txt}", "⬆️ عينة رفع إلى Telegram (40 MiB)..."))
        fd, path = tempfile.mkstemp(prefix="speed_", suffix=".bin")
        with os.fdopen(fd, "wb") as f:
            for _ in range(40): f.write(os.urandom(1 << 20))
        t = time.monotonic()
        m = await app.send_document(msg.chat.id, path, caption="speed test")
        up = 40 * 1.048576 / max(time.monotonic() - t, 0.001)
        if dl: speed_note("dl", dl * 1e6, force=True)
        speed_note("up", up * 1e6, force=True)
        try:
            t = time.monotonic(); await app.get_me(); ping = (time.monotonic() - t) * 1000
        except Exception: ping = None
        try: await m.delete()
        except Exception: pass
        verdict = ("🟢 ممتازة" if up >= 15 else "🟡 كويسة" if up >= 6 else "🔴 بطيئة — جرّب region تاني أو VPS قريب من تليجرام")
        await safe_edit(msg, ui_title("⚡", "نتيجة اختبار السرعة", "عينة من الخادم الحالي") + "\n"
                        + ui_quote(f"⬇️ Cloudflare (4×25 MiB): {dl_txt}",
                                   f"⬆️ Telegram (40 MiB): <b>{up:.1f} MB/s</b> (≈ {up*8:.0f} Mbps)  {ui_meter(up, 40)}",
                                   f"📡 Ping لتليجرام: <b>{ping:.0f} ms</b>" if ping else "📡 Ping: غير متاح",
                                   f"🏁 الرفع: <b>{verdict}</b>",
                                   f"📈 المتوسط المحفوظ (للوقت المتوقع): {speed_line()}",
                                   f"🧵 رفع متوازي: {UPLOAD_WORKERS if UPLOAD_TUNED else 4}")
                        + "\n\n<i>⚠️ عينة وقتية وليست أقصى سعة للبوت أو سرعة YouTube؛ تختلف حسب الشبكة والخادم.</i>", again)
    except Exception as e:
        await safe_edit(msg, ui_note("err", "الاختبار فشل", esc_t(clean_err(e), 150)), again)
    finally:
        _speed_running = False
        if path and os.path.exists(path): os.remove(path)

async def broadcast(admin_cq, chat_id, msg_id):
    ids = [r[0] for r in db_exec("SELECT id FROM users")]
    ok = bad = 0
    for u in ids:
        for _ in range(2):
            try:
                await app.copy_message(u, chat_id, msg_id); ok += 1; break
            except FloodWait as e:
                await asyncio.sleep(e.value + 1)
            except Exception:
                bad += 1; break
        await asyncio.sleep(0.05)
    await safe_edit(admin_cq.message, ui_title("📢", "خلصت الإذاعة") + "\n"
                    + ui_quote(f"✅ وصلت: <b>{ok}</b>", f"❌ فشلت: <b>{bad}</b>", f"👥 الإجمالي: <b>{ok + bad}</b>"), admin_kb())

# ───────────── شاشات إعدادات الأدمن ─────────────
def cf_text():
    pub = cfg("public") == "1"
    return (ui_title("⚙️", "وصول البوت") + "\n"
            + ui_quote(f"👥 الوصول: <b>{'🌍 عام (أي حد)' if pub else '🔒 خاص'}</b>",
                       "" if pub else "الأدمن + المسموح لهم بس")
            + "\n\n<i>الحصص وحدود الحجم والمدة والجودة من «🎛 التحكم المتقدم»، "
              "والمحظورين والمسموح لهم من «👥 المستخدمين».</i>\n\n"
              "<b>⌨️ أوامر سريعة</b>\n"
              "<code>/allow id</code> • <code>/unallow id</code> • <code>/ban id</code> • <code>/unban id</code>")

def cf_kb():
    pub = cfg("public") == "1"
    return KB(
        [B("🌍 عام — اضغط لتخليه خاص" if pub else "🔒 خاص — اضغط لتخليه عام", "ad|cf|pub",
           S.SUCCESS if pub else S.DANGER)],
        [B("⬅️ رجوع", "ad")],
    )

def wm_screen_text():
    t = cfg("wm_type")
    return (ui_title("💧", "العلامة المائية", "على الفيديوهات") + "\n"
            + ui_quote(f"الحالة: <b>{'✅ شغّالة' if cfg('wm_on') == '1' else '⛔ مقفولة'}</b>",
                       f"النوع: <b>{'✍️ نص' if t == 'text' else '🖼 صورة'}</b>",
                       f"النص: <b>{esc_t(cfg('wm_text')) or '— لسه'}</b>",
                       f"الصورة: <b>{'✅ مرفوعة' if os.path.exists(WM_IMG_PATH) else '— لسه'}</b>",
                       f"المكان: <b>{WM_POS_LABEL[cfg('wm_pos')]}</b>  •  الحجم: <b>{WM_SIZE_LABEL[cfg('wm_size')]}</b>")
            + "\n\n<i>⚠️ لما تكون شغّالة، كل فيديو بيتعاد ترميزه (وقت ومعالج أكتر). "
              "الصوت MP3 والصور والألبومات من غير علامة.\n"
              "💡 للكتابة بالعربي استخدم علامة صورة (النص بيطلع بحروف مفصولة).</i>")

def wm_kb():
    on, t, pos, sz = cfg("wm_on") == "1", cfg("wm_type"), cfg("wm_pos"), cfg("wm_size")
    def mk(label, sel, data):
        return B(("✅ " if sel else "") + label, data, S.SUCCESS if sel else S.PRIMARY)
    return KB(
        [B("⛔ إيقاف العلامة" if on else "✅ تفعيل العلامة", "ad|wm|tg", S.DANGER if on else S.SUCCESS)],
        [mk("✍️ نص", t == "text", "ad|wm|ty|text"), mk("🖼 صورة", t == "image", "ad|wm|ty|image")],
        [B("✏️ تغيير النص", "ad|wm|tx"), B("🖼 رفع صورة", "ad|wm|im")],
        [mk("↖️", pos == "tl", "ad|wm|ps|tl"), mk("↗️", pos == "tr", "ad|wm|ps|tr")],
        [mk("↙️", pos == "bl", "ad|wm|ps|bl"), mk("↘️", pos == "br", "ad|wm|ps|br")],
        [mk("⏺ المنتصف", pos == "c", "ad|wm|ps|c")],
        [mk("صغير", sz == "S", "ad|wm|sz|S"), mk("وسط", sz == "M", "ad|wm|sz|M"), mk("كبير", sz == "L", "ad|wm|sz|L")],
        [B("⬅️ رجوع", "ad")],
    )

def ck_screen_text():
    if has_cookies():
        try:
            total, yt, login = cookies_info(COOKIE_FILE)
            age = int((time.time() - os.path.getmtime(COOKIE_FILE)) / 3600)
            status = ui_quote(f"✅ موجودة: <b>{total}</b> كوكي ({yt} ليوتيوب/جوجل)",
                              "🔐 فيها جلسة تسجيل دخول" if login else "⚠️ مفيش جلسة تسجيل دخول — غالبًا مش هتفيد",
                              f"🕒 آخر تحديث من {age} ساعة")
        except Exception as e:
            status = ui_quote(f"⚠️ الملف موجود لكن مش مقروء: {esc_t(str(e), 60)}")
    else:
        status = ui_quote("❌ مفيش كوكيز دلوقتي")
    return (ui_title("🍪", "كوكيز يوتيوب") + "\n" + status + "\n\n"
            "<b>❔ ليه محتاجها؟</b>\n"
            "<i>يوتيوب بيحجب IP الاستضافات ويطلب «تأكيد إنك مش روبوت». الكوكيز بتحل ده غالبًا.</i>\n\n"
            "<b>🧭 إزاي أجيبها</b>\n" + ui_quote(
                "1️⃣ افتح نافذة خاصة (Incognito) وسجّل دخول بحساب جوجل ثانوي",
                "2️⃣ افتح youtube.com/robots.txt في نفس النافذة",
                "3️⃣ صدّر الكوكيز Netscape بإضافة «Get cookies.txt LOCALLY»",
                "4️⃣ اقفل النافذة الخاصة، وابعت الملف هنا 📤"))

def ck_kb():
    rows = [[B("📤 رفع كوكيز", "ad|ck|up", S.SUCCESS)]]
    if has_cookies(): rows.append([B("🗑 حذف الكوكيز", "ad|ck|rm", S.DANGER)])
    rows.append([B("⬅️ رجوع", "ad")])
    return KB(*rows)

def pe_screen_text():
    state = "✅ شغّال" if pe_active() else ("⚠️ اتعطّل (تليجرام رفضه — غالبًا صاحب البوت من غير Premium)" if PE["broken"] else "⛔ متوقف")
    keys = " ".join(PE["map"]) or "لسه مفيش"
    return (ui_title("✨", "إيموجي بريميوم") + "\n"
            + ui_quote(f"الحالة: <b>{state}</b>", f"المربوط ({len(PE['map'])}): {keys}")
            + "\n\n<i>شروط تليجرام: يظهر متحرك لمشتركي Premium، ولازم حساب صاحب البوت (اللي أنشأه من BotFather) "
              "يكون Premium، أو البوت يكون عنده يوزر مشترى من Fragment. غير كده بيظهر الإيموجي العادي.</i>\n\n"
              "<b>الإيموجي اللي البوت بيستخدمه</b>\n🚀 ⚡ ⏱ ⏹ ✅ ❌ ⏳ 🏁 ➕ 📊 ⚙️ 🌐 ❓ 🏠 🛠 🎬 📥 🍪\n\n"
              "اضغط «إضافة» وابعتلي من حسابك (لازم Premium) رسالة فيها الإيموجي البريميوم اللي عايزه، "
              "وأنا بربط كل واحد بالإيموجي العادي المقابل له.")

def pe_kb():
    return KB([B("➕ إضافة إيموجي", "ad|pe|add", S.SUCCESS)],
              [B("⛔ إيقاف" if cfg("pe_on") == "1" else "✅ تشغيل", "ad|pe|tg")],
              [B("🗑 مسح الكل", "ad|pe|rm", S.DANGER)],
              [B("⬅️ رجوع", "ad")])

def users_text():
    total = db_exec("SELECT COUNT(*) FROM users")[0][0]
    banned, allowed = sorted(BANNED), sorted(ALLOWED_DB | ALLOWED_IDS)
    fmt = lambda ids: (", ".join(map(str, ids[:15])) + (f" … (+{len(ids) - 15})" if len(ids) > 15 else "")) if ids else "—"
    return (ui_title("👥", "المستخدمين") + f"\n📊 الإجمالي: <b>{total}</b>\n\n"
            + ui_quote(f"🚫 محظورين ({len(banned)}): {fmt(banned)}",
                       f"✅ مسموح لهم ({len(allowed)}): {fmt(allowed)}",
                       f"👑 الأدمن: {fmt(sorted(ADMIN_IDS))}")
            + f"\n\n🌐 الوصول: <b>{'🌍 عام' if cfg('public') == '1' else '🔒 خاص'}</b>\n"
              "<i>اختار إجراء ثم ابعت أيدي المستخدم الرقمي 👇</i>")

def users_kb():
    return KB([B("🚫 حظر", "ad|us|ban", S.DANGER), B("✅ فك حظر", "ad|us|unban", S.SUCCESS)],
              [B("➕ سماح", "ad|us|allow"), B("➖ إزالة سماح", "ad|us|unallow")],
              [B("⬅️ رجوع", "ad")])

def blk_text():
    extra = extra_blocked()
    return (ui_title("🚫", "المواقع المحظورة") + "\n"
            + ui_quote(f"🔒 أساسية (ثابتة في الكود): <b>{len(BLOCKED)}</b> موقع",
                       f"➕ إضافية ({len(extra)}): {esc_t('، '.join(extra)) if extra else '—'}"))

def blk_kb():
    return KB([B("➕ حظر موقع", "ad|bl|add", S.DANGER), B("➖ شيل حظر", "ad|bl|rm")],
              [B("⬅️ رجوع", "ad")])

def fs_text():
    ch = cfg("fsub").strip()
    return (ui_title("📢", "الاشتراك الإجباري") + "\n"
            + ui_quote(f"الحالة: <b>{('✅ شغّال على ' + esc_t(ch)) if ch else '⛔ مقفول'}</b>")
            + "\n\n<i>المستخدم لازم يكون مشترك في القناة قبل ما يستخدم البوت. لازم البوت يكون «أدمن» فيها "
              "عشان يقدر يتحقق؛ ولو التحقق فشل لأي سبب البوت بيسمح للمستخدم (مش بيقفل).</i>")

def fs_kb():
    rows = [[B("✏️ تحديد قناة", "ad|fs|set", S.SUCCESS)]]
    if cfg("fsub").strip(): rows.append([B("⛔ إيقاف", "ad|fs|off", S.DANGER)])
    rows.append([B("⬅️ رجوع", "ad")])
    return KB(*rows)

def log_text():
    rows = db_exec("SELECT user_id, title, mode, ts FROM history ORDER BY ts DESC LIMIT 15")
    if not rows: return ui_title("📜", "آخر التحميلات") + "\n" + ui_quote("مفيش تحميلات لسه.")
    lines = [ui_title("📜", "آخر 15 تحميل", "بتوقيت UTC")]
    for u, t, q, ts in rows:
        when = time.strftime("%m/%d %H:%M", time.gmtime(ts))
        lines.append(f"<b>{esc_t(t, 34)}</b>\n<i>{when} • <code>{u}</code> • {_qlabel(q)}</i>")
    return "\n".join(lines)

def make_db_backup(dest):
    """نسخة متسقة من SQLite (حتى لو البوت شغال) عبر backup API."""
    with db_lock:
        out = sqlite3.connect(dest)
        try: db.backup(out)
        finally: out.close()

async def admin_input(m, uid, st):
    """ردود الأدمن على أسئلة لوحة الإعدادات (رقم / نص / صورة)."""
    awaiting.pop(uid, None)
    txt = " ".join((m.text or "").split())
    if st in ("ban", "unban", "allow", "unallow"):
        try: target = int(txt)
        except ValueError:
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", "أيدي غير صحيح", "ابعت رقم فقط، مثال: <code>123456789</code>"))
        return await m.reply_text(f"<b>{user_action(st, target)}</b>\n\n" + users_text(), reply_markup=users_kb())
    if st in ("blk_add", "blk_rm"):
        host = (urlparse(txt if "://" in txt else "//" + txt).hostname or "").lower()
        host = host[4:] if host.startswith("www.") else host
        if not re.fullmatch(r"[a-z0-9-]+(\.[a-z0-9-]+)+", host):
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", "اسم موقع غير صحيح", "مثلًا: <code>example.com</code>"))
        cur = list(extra_blocked())
        if st == "blk_add":
            if host not in cur: cur.append(host)
        else:
            if host in BLOCKED: return await m.reply_text(ui_note("stop", "موقع أساسي ثابت", "مينفعش يتشال."), reply_markup=blk_kb())
            cur = [d for d in cur if d != host]
        cfg_set("blk_extra", ",".join(cur))
        return await m.reply_text(ui_note("ok", "اتحدّث") + "\n\n" + blk_text(), reply_markup=blk_kb())
    if st == "fsub":
        ch = txt if txt.startswith("@") else "@" + txt
        if not re.fullmatch(r"@[A-Za-z][A-Za-z0-9_]{4,31}", ch):
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", "يوزر قناة غير صحيح", "مثلًا: <code>@mychannel</code>"))
        warn = ""
        try:
            await app.get_chat(ch)
            me = await app.get_chat_member(ch, "me")
            if me.status not in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER):
                warn = "\n\n" + ui_note("warn", "البوت مش أدمن في القناة دي", "ارفعه أدمن عشان التحقق يشتغل.")
        except Exception as e:
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", f"مقدرتش أوصل للقناة {esc_t(ch)}", esc_t(str(e), 80) + "\nتأكد من اليوزر وإن البوت مضاف فيها."))
        cfg_set("fsub", ch); _sub_cache.clear()
        return await m.reply_text(ui_note("ok", "اتفعّل الاشتراك الإجباري") + "\n\n" + fs_text() + warn, reply_markup=fs_kb())
    if st == "ck":
        raw = None
        try:
            if m.document:
                if (m.document.file_size or 0) > 2 * 1024 * 1024:
                    awaiting[uid] = st
                    return await m.reply_text(ui_note("err", "الملف كبير", "ملف الكوكيز لازم يكون أقل من 2MB."))
                src = await app.download_media(m, file_name=os.path.join(tempfile.gettempdir(), f"dl_ck_{uuid.uuid4().hex[:6]}.txt"))
                try:
                    with open(src, "r", encoding="utf-8", errors="ignore") as f: raw = f.read()
                finally:
                    try: os.remove(src)
                    except OSError: pass
            else:
                raw = m.text
        except Exception as e:
            log.info("cookies download failed: %s", e)
        ok, msg = await asyncio.to_thread(save_cookies_text, raw)
        if not ok:
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", esc_t(msg, 120), "ابعت ملف cookies.txt صحيح، أو اضغط رجوع من اللوحة."))
        try: await m.delete()      # الكوكيز حساسة: نمسح رسالة الملف من الشات
        except Exception: pass
        return await m.reply_text(ui_note("ok", "اتحفظت الكوكيز", esc_t(msg)) + "\n\n" + ck_screen_text(), reply_markup=ck_kb())
    if st == "pe":
        text = m.text or m.caption or ""
        u16 = text.encode("utf-16-le")
        found = {}
        for e in (m.entities or m.caption_entities or []):
            if e.type == MessageEntityType.CUSTOM_EMOJI and e.custom_emoji_id:
                fb = _norm_emoji(u16[e.offset * 2:(e.offset + e.length) * 2].decode("utf-16-le", "ignore"))
                if fb: found[fb] = e.custom_emoji_id
        if not found:
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", "مفيش إيموجي بريميوم في الرسالة", "ابعت رسالة فيها إيموجي بريميوم (من حساب Premium)."))
        try: cur = json.loads(cfg("pe_map") or "{}")
        except ValueError: cur = {}
        cur.update(found)
        cfg_set("pe_map", json.dumps(cur, ensure_ascii=False)); cfg_set("pe_on", "1")
        PE["broken"] = False; pe_reload()
        return await m.reply_text(ui_note("ok", f"اتربط {len(found)} إيموجي", " ".join(found)) + "\n\n" + pe_screen_text(), reply_markup=pe_kb())
    if st == "wm_text":
        if not txt or len(txt) > 60:
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", "النص لازم يكون من 1 لـ 60 حرف"))
        cfg_set("wm_text", txt); cfg_set("wm_type", "text")
        return await m.reply_text(ui_note("ok", "اتحفظ") + "\n\n" + wm_screen_text(), reply_markup=wm_kb())
    if st == "wm_img":
        doc = m.document if m.document and (m.document.mime_type or "").startswith("image/") else None
        if not (m.photo or doc):
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", "ابعت صورة", "يفضل PNG كملف."))
        src = await app.download_media(m, file_name=os.path.join(tempfile.gettempdir(), f"dl_wm_{uuid.uuid4().hex[:6]}_in"))
        tmp = (src or "") + ".png"
        try:
            if not src: raise RuntimeError("download failed")
            p = await asyncio.create_subprocess_exec(           # بيتأكد إنها صورة سليمة + بيصغّرها لو كبيرة
                "ffmpeg", "-y", "-i", src, "-frames:v", "1", "-vf", "scale='min(800,iw)':-2", tmp,
                stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)
            await p.wait()
            if p.returncode != 0 or not os.path.exists(tmp): raise RuntimeError("bad image")
            shutil.move(tmp, WM_IMG_PATH)
        except Exception as e:
            log.info("watermark image rejected: %s", e)
            awaiting[uid] = st
            return await m.reply_text(ui_note("err", "مقدرتش أقرا الصورة دي", "جرّب PNG تاني."))
        finally:
            for f in (src, tmp):
                if f and os.path.exists(f):
                    try: os.remove(f)
                    except OSError: pass
        with open(WM_IMG_PATH, "rb") as f: sig = hashlib.sha1(f.read()).hexdigest()[:8]
        cfg_set("wm_img_sig", sig); cfg_set("wm_type", "image")
        return await m.reply_text(ui_note("ok", "اتحفظت الصورة") + "\n\n" + wm_screen_text(), reply_markup=wm_kb())

# ───────────── الهاندلرز ─────────────
@app.on_message(filters.command("start") & filters.private)
async def on_start(_, m):
    if not is_allowed(m.from_user.id):
        return await m.reply_text(LOCKED_HTML)
    if in_maintenance(m.from_user.id):
        return await m.reply_text(MAINT_HTML)
    touch_user(m.from_user.id)
    awaiting.pop(m.from_user.id, None)
    await send_home(m.chat.id, welcome_text(m.from_user.first_name or "", m.from_user.id), menu_kb(m.from_user.id))

@app.on_message(filters.command(["menu", "history", "favorites", "settings", "help", "admin"]) & filters.private)
async def on_cmd(_, m):
    uid = m.from_user.id
    if not is_allowed(uid):
        return await m.reply_text(LOCKED_HTML)
    if in_maintenance(uid):
        return await m.reply_text(MAINT_HTML)
    touch_user(uid)
    awaiting.pop(uid, None)
    cmd = m.command[0].lower()
    if cmd == "history":
        txt, kb = hist_view(uid, "a", 0)
    elif cmd == "favorites":
        txt, kb = fav_view(uid, 0)
    elif cmd == "settings":
        txt, kb = settings_text(uid), settings_kb(uid)
    elif cmd == "help":
        return await app.send_message(m.chat.id, pe_html(HELP), reply_markup=back_kb())
    elif cmd == "admin":
        if not is_admin(uid): return
        txt, kb = admin_home_text(), admin_kb()
    else:
        return await send_home(m.chat.id, welcome_text(m.from_user.first_name or "", uid), menu_kb(uid))
    await m.reply_text(pe_html(txt), reply_markup=kb)

def user_action(cmd, target):
    """حظر / فك حظر / سماح / إزالة سماح — مشترك بين الأوامر ولوحة الأدمن."""
    if cmd == "ban" and target in ADMIN_IDS:
        return "مينفعش تحظر أدمن."
    if cmd == "ban":
        db_exec("INSERT OR IGNORE INTO banned(id) VALUES (?)", (target,)); BANNED.add(target)
        return f"🚫 اتحظر: {target}"
    if cmd == "unban":
        db_exec("DELETE FROM banned WHERE id=?", (target,)); BANNED.discard(target)
        return f"✅ اتفك الحظر عن: {target}"
    if cmd == "allow":
        db_exec("INSERT OR IGNORE INTO allowed(id) VALUES (?)", (target,)); ALLOWED_DB.add(target)
        return f"✅ اتضاف للمسموح لهم: {target}"
    db_exec("DELETE FROM allowed WHERE id=?", (target,)); ALLOWED_DB.discard(target)
    return f"➖ اتشال من المسموح لهم: {target}"

@app.on_message(filters.command(["watch", "watches", "unwatch"]) & filters.private)
async def on_watch(_, m):
    uid = m.from_user.id
    if not is_allowed(uid): return await m.reply_text(LOCKED_HTML)
    if in_maintenance(uid): return await m.reply_text(MAINT_HTML)
    touch_user(uid)
    cmd = m.command[0].lower()
    urls = [u.rstrip(".,;:!?)]}،؛") for u in URL_RE.findall(m.text or "")]
    if cmd != "watch" or not urls:
        txt, kb = watch_view(uid)
        return await m.reply_text(pe_html(txt), reply_markup=kb)
    url = urls[0]
    if not await asyncio.to_thread(is_safe_url, url) or is_blocked(url):
        return await m.reply_text(ui_note("err", "الرابط غير صالح", "اتأكد منه وابعته تاني."))
    mode = next((t for t in m.command[1:] if t in VALID_PREFS and t != "ask"), None)
    return await watch_add(m, uid, url, watch_mode_for(uid, mode))

class _CQ:
    """كائن شبيه بـ callback_query عشان /speed يستخدم نفس شاشة اختبار السرعة."""
    def __init__(self, message): self.message = message
    async def answer(self, text="", show_alert=False): pass

@app.on_message(filters.command("speed") & filters.private)
async def on_speed(_, m):
    if not is_admin(m.from_user.id): return
    msg = await m.reply_text(pe_html(ui_note("info", "جارٍ اختبار السرعة...", "بياخد حوالي نص دقيقة")))
    await speed_test(_CQ(msg))

@app.on_message(filters.command(["ban", "unban", "allow", "unallow"]) & filters.private)
async def on_ban(_, m):
    if not is_admin(m.from_user.id): return
    cmd = m.command[0].lower()
    try: target = int(m.command[1])
    except (IndexError, ValueError):
        return await m.reply_text(ui_note("info", "الاستخدام", f"<code>/{cmd} user_id</code>"))
    await m.reply_text(f"<b>{user_action(cmd, target)}</b>")

@app.on_message(filters.private & ~filters.command(["start", "ban", "unban", "allow", "unallow",
                                                    "menu", "history", "favorites", "settings", "help", "admin", "speed",
                                                    "watch", "watches", "unwatch"]))
async def on_message(_, m):
    uid = m.from_user.id
    if not is_allowed(uid):
        return await m.reply_text(LOCKED_HTML)
    if in_maintenance(uid):
        return await m.reply_text(MAINT_HTML)
    touch_user(uid)

    if awaiting.get(uid) == "bc" and is_admin(uid):
        awaiting.pop(uid)
        bc_pending[uid] = (m.chat.id, m.id)
        n = db_exec("SELECT COUNT(*) FROM users")[0][0]
        return await m.reply_text(ui_note("ask", f"هتتبعت الرسالة دي لـ {n} مستخدم", "تأكيد الإرسال؟"),
                                  reply_markup=KB([B("✅ تأكيد الإرسال", "ad|bc|ok", S.SUCCESS)],
                                                  [B("❌ إلغاء", "ad|bc|no", S.DANGER)]))

    if is_admin(uid) and awaiting.get(uid) in ("wm_text", "wm_img", "ck", "pe", "ban", "unban", "allow", "unallow",
                                               "blk_add", "blk_rm", "fsub"):
        return await admin_input(m, uid, awaiting[uid])

    need = await sub_required(uid)
    if need:
        return await m.reply_text(ui_note("lock", "اشتراك إجباري", f"اشترك في القناة {esc_t(need)} الأول، وبعدها اضغط «تحقق» 👇"),
                                  reply_markup=sub_kb(need))

    urls = list(dict.fromkeys(u.rstrip(".,;:!?)]}،؛") for u in URL_RE.findall(m.text or "")))
    if uid in kw_wait and m.text and not urls:                # كلمات فلتر القناة
        rid = kw_wait.pop(uid)
        kw = " ".join(m.text.split())[:120]
        if rid:
            db_exec("UPDATE watch SET kw=? WHERE id=? AND user_id=?", (kw, rid, uid))
        else:
            cfg_set("watch_kw", kw)
        txt, kb = watch_view(uid)
        return await m.reply_text(pe_html(ui_note("ok", "اتحفظ الفلتر", esc_t(kw)) + "\n\n" + txt), reply_markup=kb)
    wb = batches.get(psel_wait.get(uid, ""))
    if wb and not wb.started and not urls and m.text:       # أرقام مكتوبة لشاشة اختيار الفيديوهات
        idx = parse_ranges(m.text, len(wb.items))
        if idx is None:
            return await m.reply_text(ui_note("ask", "مش فاهم الأرقام", "اكتب زي: 1-5, 8, 12-20  أو  الكل"))
        wb.sel, wb.page = idx, (min(idx) // SEL_PAGE if idx else 0)
        txt, kb = sel_view(wb)
        await safe_edit(wb.msg, txt, kb)
        try: await m.delete()
        except Exception: pass
        return
    if not urls:
        return await m.reply_text(ui_note("ask", "مش لاقي رابط في رسالتك", "ابعت لينك يبدأ بـ https://  أو اختار من القائمة 👇"),
                                  reply_markup=menu_kb(uid))
    return await handle_urls(m, uid, urls)

# ───────────── مراقبة القنوات ─────────────
WATCH_MAX = 30

_AR_MAP = str.maketrans({"ث": "ت", "ة": "ه", "ى": "ي", "أ": "ا", "إ": "ا", "آ": "ا", "ؤ": "و", "ئ": "ي", "ـ": ""})

def norm_ar(text):
    """توحيد للنص العربي عشان المطابقة تتحمّل اختلاف الكتابة (ثانية/تانية، بكالوريا/بكلوريا، ة/ه، تشكيل...)."""
    t = re.sub(r"[\u064B-\u065F\u0670]", "", str(text or "").lower()).translate(_AR_MAP)
    return t.replace("ا", "")          # الألف بتتكتب وتتشال كتير (بكالوريا/بكلوريا) فنتجاهلها في المطابقة

def kw_match(title, kw):
    """True لو العنوان بيحتوي كل كلمات واحد من الفلاتر. kw فاضي = أي عنوان. الفاصلة (, ، |) = بدائل."""
    kw = (kw or "").strip()
    if not kw: return True
    t = norm_ar(title)
    for alt in re.split(r"[,،|؛;\n]+", kw):
        words = [norm_ar(w).rstrip("ه") or norm_ar(w) for w in alt.split()]     # تانية/تاني بيتطابقوا
        words = [w for w in words if w]
        if words and all(w in t for w in words): return True
    return False

kw_wait: dict[int, int] = {}       # uid → watch id (0 = الفلتر الافتراضي) مستني كلمات الفلتر

def watch_norm(url):
    """رابط قناة يوتيوب بدون تبويب → تبويب /videos (عشان نجيب الفيديوهات مش التبويبات)."""
    p = urlparse(url)
    host = (p.hostname or "").lower()
    if any(host == h or host.endswith("." + h) for h in YT_HOSTS):
        parts = [x for x in p.path.split("/") if x]
        if parts and (parts[0].startswith("@") or parts[0] in ("channel", "c", "user")):
            base = parts[:1] if parts[0].startswith("@") else parts[:2]
            if len(parts) == len(base):
                return f"https://www.youtube.com/{'/'.join(base)}/videos"
    return url

def watch_is_playlist(url):
    p = urlparse(url)
    return "list=" in (p.query or "") or p.path.rstrip("/").endswith("/playlist")

def watch_fetch(url, limit=10):
    """(اسم القناة/القائمة، [(id, url, title, live, ie)] الأحدث أولًا). فحص خفيف (flat) من غير تحميل."""
    pl = watch_is_playlist(url)
    o = base_opts(); o["extract_flat"] = "in_playlist"
    if not pl: o["playlistend"] = limit
    info = ydl_run(url, o, False)
    if not isinstance(info, dict): return "", []
    ents = [e for e in (info.get("entries") or []) if isinstance(e, dict)]
    if pl: ents = list(reversed(ents[-limit:]))        # القوائم بتضيف الجديد في الآخر
    out = []
    for e in ents:
        eid = e.get("id")
        u = e.get("url") or e.get("webpage_url")
        ie = (e.get("ie_key") or info.get("extractor_key") or "x").lower()
        if not u or not str(u).startswith("http"):
            if ie == "youtube" and eid: u = f"https://www.youtube.com/watch?v={eid}"
            else: continue
        if e.get("_type") == "playlist" or not url_ok(u): continue
        live = e.get("live_status") in ("is_live", "is_upcoming")
        out.append((str(eid or u), u, e.get("title") or u, live, ie))
    return info.get("title") or info.get("uploader") or info.get("channel") or "", out[:limit]

def watch_mode_for(uid, mode=None):
    mode = mode or get_pref(uid)
    return "720" if mode in (None, "", "ask") else mode

async def watch_add(m, uid, url, mode):
    url = watch_norm(url)
    if db_exec("SELECT COUNT(*) FROM watch WHERE user_id=?", (uid,))[0][0] >= WATCH_MAX:
        return await m.reply_text(ui_note("stop", "وصلت للحد الأقصى", f"{WATCH_MAX} قناة. امسح واحدة الأول."))
    wait = await m.reply_text(ui_note("info", "جارٍ فحص القناة...", "بجيب آخر الفيديوهات 🔍"))
    try:
        title, ents = await asyncio.to_thread(watch_fetch, url, 10)
    except Exception as e:
        return await wait.edit_text(ui_note("err", "مقدرتش أفتح القناة", esc_t(clean_err(e), 150)))
    if not ents:
        return await wait.edit_text(ui_note("err", "مفيش فيديوهات في الرابط ده", "ابعت رابط قناة أو قائمة تشغيل."))
    title = title or site_of(url) or url
    seen = [e[0] for e in ents if not e[3]]            # الموجود دلوقتي يعتبر قديم؛ هتوصلك الجديدة بس
    kw = cfg("watch_kw")
    db_exec("INSERT OR REPLACE INTO watch(user_id, url, title, seen, mode, ts, kw) VALUES (?,?,?,?,?,?,?)",
            (uid, url, title, json.dumps(seen), mode, int(time.time()), kw))
    await wait.edit_text(pe_html(ui_title("🔔", "تمت المراقبة", esc_t(title, 70)) + "\n"
                                 + ui_quote(f"📺 الجودة: {mode_label(clamp_mode(mode))}",
                                            f"🏷 الفلتر: {esc_t(kw) if kw else 'بدون (كل الفيديوهات)'}",
                                            f"⏱ الفحص كل {int(WATCH_EVERY_MIN)} دقيقة",
                                            "هيتبعتلك بس الفيديو الجديد اللي عنوانه فيه الفلتر" if kw
                                            else "أي فيديو جديد هيتحمّل ويتبعتلك لوحده")),
                         reply_markup=KB([B("🏷 تغيير الفلتر", f"wt|kw|{db_exec('SELECT id FROM watch WHERE user_id=? AND url=?', (uid, url))[0][0]}")],
                                         [B("📋 قنواتي", "wt|ls")], [B("🏠 القائمة الرئيسية", "m")]))

def watch_view(uid):
    rows_db = db_exec("SELECT id, title, mode, kw FROM watch WHERE user_id=? ORDER BY id", (uid,))
    if not rows_db:
        return (ui_title("🔔", "مراقبة القنوات") + "\n"
                + ui_quote("مفيش قنوات مراقبة دلوقتي", "ابعت: <code>/watch رابط_القناة</code>",
                           "أو مع جودة: <code>/watch رابط_القناة 1080</code>"),
                KB([B("🏠 القائمة الرئيسية", "m")]))
    lines = []
    for i, (_, t, md, kw) in enumerate(rows_db):
        lines.append(f"{i + 1}. {esc_t(t, 40)} • {mode_label(clamp_mode(watch_mode_for(uid, md)))}")
        lines.append(f"    🏷 {esc_t(kw, 40) if kw else 'بدون فلتر'}")
    kb = []
    for i, (rid, t, _, kw) in enumerate(rows_db):
        kb.append([B(f"🏷 فلتر {i + 1}: {plain_t(kw, 18) if kw else 'بدون'}", f"wt|kw|{rid}", S.PRIMARY),
                   B(f"🗑 {i + 1}", f"wt|rm|{rid}", S.DANGER)])
    kb.append([B("🏷 الفلتر الافتراضي للقنوات الجديدة", "wt|kw|0")])
    kb.append([B("🔄 افحص الآن", "wt|now", S.SUCCESS)])
    kb.append([B("🏠 القائمة الرئيسية", "m")])
    return (ui_title("🔔", f"قنواتي المراقبة ({len(rows_db)})", "🏷 = فلتر العنوان • 🗑 = حذف") + "\n" + ui_quote(*lines)
            + f"\n<i>الفحص كل {int(WATCH_EVERY_MIN)} دقيقة • للإضافة: /watch رابط_القناة [الجودة]</i>", KB(*kb))

WATCH_MEMO = {}

async def watch_fetch_cached(url, fresh=False, ttl=120):
    """نفس القناة متراقبة عند أكتر من مستخدم → فحص واحد في الدورة بدل فحص لكل مستخدم."""
    hit = WATCH_MEMO.get(url)
    if hit and not fresh and time.monotonic() - hit[0] < ttl: return hit[1]
    res = await asyncio.to_thread(watch_fetch, url, 10)
    WATCH_MEMO[url] = (time.monotonic(), res)
    return res

async def watch_check(row, fresh=False):
    rid, uid, url, title, seen_json, mode, kw = row
    if not is_allowed(uid) or is_banned(uid): return 0
    try: seen = list(json.loads(seen_json or "[]"))
    except ValueError: seen = []
    name, ents = await watch_fetch_cached(url, fresh=fresh)
    if not ents: return 0
    known = set(seen)
    new = [e for e in ents if e[0] not in known and not e[3]]
    if not new: return 0
    new.reverse()                                       # الأقدم الأول
    seen = (seen + [e[0] for e in new])[-300:]
    db_exec("UPDATE watch SET seen=? WHERE id=?", (json.dumps(seen), rid))
    new = [e for e in new if kw_match(e[2], kw)]        # الفيديوهات اللي عنوانها فيه الفلتر بس؛ الباقي بيتعتبر مشوف وبيتتجاهل
    if not new: return 0
    items = [Item(u, t, f"{ie}:{eid}") for eid, u, t, _, ie in new]
    mode = clamp_mode(watch_mode_for(uid, mode))
    try:
        await app.send_message(uid, pe_html(ui_title("🔔", f"فيديو جديد ({len(items)})", esc_t(title or name, 70) + (f" • 🏷 {esc_t(kw, 30)}" if kw else "")) + "\n"
                                            + ui_quote(*[esc_t(i.title, 60) for i in items[:6]])))
        msg = await app.send_message(uid, pe_html(ui_note("wait", "جارٍ التجهيز...", "ثواني وهنبدأ")))
    except Exception as e:
        log.info("watch notify failed for %s: %s", uid, e)
        return 0
    # إرسال متوازي (لحد 3 مع بعض) عشان السرعة؛ مفيش ترتيب مطلوب هنا
    b = Batch(id=uuid.uuid4().hex[:8], user_id=uid, chat_id=uid, items=items, mode=mode, msg=msg,
              sequential=False, sem=asyncio.Semaphore(3))
    batches[b.id] = b
    await begin(b)
    return len(items)

try: WATCH_EVERY_MIN = max(5.0, float(os.getenv("WATCH_INTERVAL_MIN", "30") or 30))
except ValueError: WATCH_EVERY_MIN = 30.0
WATCH_ON = os.getenv("WATCH_INTERVAL_MIN", "30").strip() != "0"

async def watch_loop():
    if not WATCH_ON: return
    await asyncio.sleep(120)
    while True:
        try:
            for row in db_exec("SELECT id, user_id, url, title, seen, mode, COALESCE(kw, '') FROM watch"):
                try: await watch_check(row)
                except asyncio.CancelledError: raise
                except Exception as e: log.info("watch check failed for %s: %s", row[2], e)
                await asyncio.sleep(3)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            log.warning("watch loop error: %s", e)
        await asyncio.sleep(WATCH_EVERY_MIN * 60)

# ───────────── اختيار فيديوهات من القائمة ─────────────
SEL_PAGE = 8
psel_wait: dict[int, str] = {}      # uid → batch id (مستني أرقام مكتوبة زي 1-5,8)

def plain_t(text, limit=30):
    t = " ".join(str(text or "").split())
    return t if len(t) <= limit else t[:limit - 1] + "…"

def parse_ranges(text, n):
    """'1-5, 8 ،12-20' → {0..4, 7, 11..19}. 'الكل' = الكل. None لو مفيش أرقام صالحة."""
    t = (text or "").translate(str.maketrans("٠١٢٣٤٥٦٧٨٩", "0123456789")).strip()
    if t in ("الكل", "all", "كل"): return set(range(n))
    out, ok = set(), False
    for tok in re.split(r"[,\s،؛;]+", t):
        mt = re.fullmatch(r"(\d+)\s*(?:[-–—:]\s*(\d+))?", tok)
        if not mt: continue
        a = int(mt.group(1)); z = int(mt.group(2) or a)
        if a > z: a, z = z, a
        ok = True
        out.update(i - 1 for i in range(max(a, 1), min(z, n) + 1))
    return out if ok else None

def sel_view(b):
    n = len(b.items)
    pages = max(1, (n + SEL_PAGE - 1) // SEL_PAGE)
    b.page = min(max(b.page, 0), pages - 1)
    head = (ui_title("📋", f"اختار الفيديوهات ({len(b.sel)}/{n})", esc_t(b.ptitle, 70) if b.ptitle else "")
            + "\n" + ui_quote("اضغط على الفيديو لتحديده أو إلغائه",
                              "هيتحمّلوا ويتبعتوا واحد ورا التاني بالترتيب",
                              "📝 أو ابعت أرقام زي: <code>1-5, 8, 12-20</code>"))
    rows = []
    for i in range(b.page * SEL_PAGE, min(n, (b.page + 1) * SEL_PAGE)):
        on = i in b.sel
        rows.append([B(f"{'☑️' if on else '⬜'} {i + 1}. {plain_t(b.items[i].title, 32)}", f"ps|{b.id}|t|{i}",
                       S.SUCCESS if on else S.PRIMARY)])
    if pages > 1:
        rows.append([B("◀️", f"ps|{b.id}|p|{b.page - 1}") if b.page > 0 else B("⏺", "nop"),
                     B(f"{b.page + 1}/{pages}", "nop"),
                     B("▶️", f"ps|{b.id}|p|{b.page + 1}") if b.page < pages - 1 else B("⏺", "nop")])
    rows.append([B("✅ الكل", f"ps|{b.id}|a"), B("⬜ لا شيء", f"ps|{b.id}|n"), B("🔄 عكس", f"ps|{b.id}|i")])
    rows.append([B(f"▶️ كمّل ({len(b.sel)})", f"ps|{b.id}|go", S.SUCCESS)] if b.sel else [B("اختار فيديو واحد على الأقل", "nop")])
    rows.append([B("❌ إلغاء", f"x|{b.id}", S.DANGER)])
    return head, KB(*rows)

async def after_selection(b):
    """بعد ما المستخدم يأكد الاختيار: إما نبدأ بالجودة الافتراضية أو نسأله عن الجودة."""
    psel_wait.pop(b.user_id, None)
    summary = metadata_text(b.items, b.ptitle)
    if b.pref != "ask":
        b.mode = clamp_mode(b.pref)
        await safe_edit(b.msg, summary + f"\n\n⚡ <b>بدأت بالجودة الافتراضية:</b> {mode_label(b.mode)}", cancel_kb(b))
        return await begin(b)
    await safe_edit(b.msg, summary, picker_kb(b.id, None))

async def handle_urls(m, uid, urls, force_mode=None):
    blocked = [u for u in urls if is_blocked(u)]
    urls = [u for u in urls if u not in blocked]
    if not urls:
        return await m.reply_text(ui_note("stop", "الموقع ده مش مسموح بيه", "مخالف لقواعد تليجرام."), reply_markup=back_kb())
    safe = await asyncio.gather(*[asyncio.to_thread(is_safe_url, u) for u in urls])
    urls = [u for u, ok in zip(urls, safe) if ok]
    if not urls:
        return await m.reply_text(ui_note("err", "الرابط غير صالح", "اتأكد منه وابعته تاني."), reply_markup=back_kb())
    wait = await m.reply_text(ui_note("info", "جارٍ فحص الرابط..." if len(urls) == 1 else f"جارٍ فحص {len(urls)} روابط...", "بجيب المعلومات والجودات المتاحة 🔍"))
    async def _probe(u):
        hit = await asyncio.to_thread(urlmap_get, u)
        try:
            result = await probe_shared(u)
            if hit and len(result[0]) == 1 and result[0][0].engine == "ytdlp":
                result[0][0].key = hit[0]   # احتفظ بمفتاح كاش الملف بعد فحص metadata الجديد
                if not result[0][0].title: result[0][0].title = hit[1] or u
            return result
        except Exception:
            if hit: return [Item(u, hit[1] or u, hit[0])], None
            raise
    results = await asyncio.gather(*[_probe(u) for u in urls], return_exceptions=True)
    items, fails, pl = [], [], None
    for u, r in zip(urls, results):
        if isinstance(r, Exception): fails.append(f"• {esc_t(u, 40)}: {esc_t(clean_err(r), 80)}")
        else:
            items += r[0]; pl = pl or r[1]
            if len(r[0]) == 1 and r[0][0].engine == "ytdlp" and r[0][0].url == u and not r[0][0].key.startswith("sniff:"):
                urlmap_put(u, r[0][0].key, r[0][0].title)
    if not items:
        return await wait.edit_text(ui_title("❌", "مقدرتش أحمّل الرابط") + "\n" + ui_quote(*fails), reply_markup=back_kb())

    b = Batch(id=uuid.uuid4().hex[:8], user_id=uid, chat_id=m.chat.id, items=items, msg=wait)
    batches[b.id] = b

    pref = force_mode or get_pref(uid)
    only_gallery = all(i.engine == "gallery" for i in items)
    preview_info = items[0].info if len(items) == 1 and items[0].engine == "ytdlp" else None
    summary = metadata_text(items, pl)
    if fails: summary += "\n\n⚠️ <b>روابط لم تنجح</b>\n" + ui_quote(*fails[:3])
    if pref == "audio" and cfg("mp3_on") != "1": pref = "ask"       # الأدمن قفل MP3
    if len(items) > 1 and not only_gallery:          # قائمة/أكتر من رابط: شاشة اختيار + تحميل متتابع
        b.pref, b.ptitle, b.sel, b.sequential = pref, pl or "", set(range(len(items))), True
        psel_wait[uid] = b.id
        txt, kb = sel_view(b)
        if fails: txt += "\n\n⚠️ <b>روابط لم تنجح</b>\n" + ui_quote(*fails[:3])
        return await safe_edit(wait, txt, kb)
    if pref != "ask" or only_gallery:         # جودة افتراضية، أو صور بس (مفيش جودة تتختار)
        b.mode = "best" if only_gallery else clamp_mode(pref)
        if not only_gallery:
            text = summary + f"\n\n⚡ <b>بدأت بالجودة الافتراضية:</b> {mode_label(b.mode)}"
            card = await send_card(m, wait, text, cancel_kb(b), preview_info) if preview_info else None
            if card: b.msg = card
            else: await safe_edit(wait, text, cancel_kb(b))
        else:
            await safe_edit(wait, render(b), cancel_kb(b))
        return await begin(b)

    await asyncio.to_thread(warm_exact_sizes, preview_info)
    kb = picker_kb(b.id, preview_info)
    card = await send_card(m, wait, summary, kb, preview_info) if preview_info else None
    if card: b.msg = card
    else: await wait.edit_text(summary, reply_markup=kb)

@app.on_callback_query()
async def on_cb(_, cq):
    uid, d = cq.from_user.id, cq.data.split("|")
    act = d[0]
    if not is_allowed(uid):
        return await cq.answer("🔒 البوت خاص", show_alert=True)
    if in_maintenance(uid):
        return await cq.answer(MAINT_TEXT, show_alert=True)
    touch_user(uid)

    if act == "fs":
        _sub_cache.pop(uid, None)
        need = await sub_required(uid)
        if need: return await cq.answer("لسه مشتركتش في القناة 🙂", show_alert=True)
        return await show_home(cq)

    if act == "m":
        awaiting.pop(uid, None)
        return await show_home(cq)
    if act == "dl":
        return await show(cq, ui_prompt("📥", "تحميل جديد", "🔗 ابعت لينك فيديو أو صور",
                                        "📋 أو أكتر من لينك في رسالة واحدة"), back_kb())
    if act == "hp":
        return await show(cq, HELP, back_kb())
    if act == "sites":
        return await show(cq, sites_text(), back_kb())

    if act == "nop":
        return await cq.answer()

    if act == "me":
        sub = d[1] if len(d) > 1 else ""
        if sub == "h":
            flt = d[2] if len(d) > 2 else "a"
            page = int(d[3]) if len(d) > 3 and d[3].isdigit() else 0
            txt, kb = hist_view(uid, flt, page)
            return await show(cq, txt, kb)
        if sub == "f":
            page = int(d[2]) if len(d) > 2 and d[2].isdigit() else 0
            txt, kb = fav_view(uid, page)
            return await show(cq, txt, kb)
        if sub == "clr":
            if len(d) == 2:
                return await show(cq, ui_note("warn", "تمسح سجل تحميلاتك؟", "المفضلة مش هتتمسح."),
                                  KB([B("✅ أيوه امسح", "me|clr|ok", S.DANGER)], [B("🔙 لأ، رجوع", "me")]))
            db_exec("DELETE FROM history WHERE user_id=?", (uid,))
            await cq.answer("✅ اتمسح السجل")
        return await show(cq, me_text(uid), me_kb())

    if act in ("hx", "fx"):
        if len(d) < 2 or not d[1].isdigit(): return await cq.answer()
        need = await sub_required(uid)
        if need: return await cq.answer(f"لازم تشترك في القناة {need} الأول", show_alert=True)
        if act == "hx":
            r = db_exec("SELECT url, mode FROM history WHERE rowid=? AND user_id=?", (int(d[1]), uid))
        else:
            r = db_exec("SELECT url, 'ask' FROM favorites WHERE rowid=? AND user_id=?", (int(d[1]), uid))
        if not r or not r[0][0]:
            return await cq.answer("الرابط مش محفوظ للعنصر ده (تحميل قديم).", show_alert=True)
        url, mode = r[0]
        await cq.answer("🔁 بجهّز الرابط...")
        return await handle_urls(cq.message, uid, [url], force_mode=mode if mode in VALID_PREFS and mode != "ask" else None)

    if act == "fv":
        if len(d) < 4 or not d[1].isdigit(): return await cq.answer()
        flt, page = d[2], (int(d[3]) if d[3].isdigit() else 0)
        r = db_exec("SELECT url, title FROM history WHERE rowid=? AND user_id=?", (int(d[1]), uid))
        if not r or not r[0][0]:
            return await cq.answer("الرابط مش محفوظ للعنصر ده.", show_alert=True)
        url, title = r[0]
        if db_exec("SELECT 1 FROM favorites WHERE user_id=? AND url=?", (uid, url)):
            db_exec("DELETE FROM favorites WHERE user_id=? AND url=?", (uid, url))
            await cq.answer("➖ اتشال من المفضلة")
        else:
            if db_exec("SELECT COUNT(*) FROM favorites WHERE user_id=?", (uid,))[0][0] >= FAV_LIMIT:
                return await cq.answer(f"المفضلة وصلت للحد الأقصى ({FAV_LIMIT})، امسح منها الأول.", show_alert=True)
            db_exec("INSERT OR REPLACE INTO favorites(user_id, url, title, ts) VALUES (?,?,?,?)",
                    (uid, url, title, int(time.time())))
            await cq.answer("⭐ اتضاف للمفضلة")
        txt, kb = hist_view(uid, flt, page)
        return await show(cq, txt, kb)

    if act == "fd":
        if len(d) < 3 or not d[1].isdigit(): return await cq.answer()
        db_exec("DELETE FROM favorites WHERE rowid=? AND user_id=?", (int(d[1]), uid))
        await cq.answer("🗑 اتشال من المفضلة")
        txt, kb = fav_view(uid, int(d[2]) if d[2].isdigit() else 0)
        return await show(cq, txt, kb)

    if act == "st":
        if len(d) > 1 and d[1] in VALID_PREFS:
            set_pref(uid, d[1])
            await cq.answer("✅ اتحفظ")
        return await show(cq, settings_text(uid), settings_kb(uid))

    if act == "q":
        b = batches.get(d[1])
        if not b or b.user_id != uid or b.started:
            return await cq.answer("انتهت صلاحية الطلب، ابعت الرابط تاني.", show_alert=True)
        mode = d[2]
        dynamic_resolution = (len(b.items) == 1 and mode.isdigit()
                              and mode in quality_modes(b.items[0].info or {}))
        audio_ok = mode == "audio" and (len(b.items) != 1 or audio_available(b.items[0].info or {}))
        if ((mode not in VALID_PREFS and not dynamic_resolution) or mode == "ask"
                or (mode == "audio" and (not audio_ok or cfg("mp3_on") != "1"))):
            return await cq.answer("اختيار غير صالح", show_alert=True)
        b.mode = clamp_mode(mode)
        b.started = True            # يمنع الضغط المزدوج على الزرار من تشغيل الدفعة مرتين
        await cq.answer("🚀 بدأنا!")
        return await begin(b)

    if act == "wt":
        sub = d[1] if len(d) > 1 else "ls"
        if sub == "rm" and len(d) > 2 and d[2].isdigit():
            db_exec("DELETE FROM watch WHERE id=? AND user_id=?", (int(d[2]), uid))
            await cq.answer("🗑 اتشالت")
        elif sub == "kw" and len(d) > 2 and d[2].isdigit():
            rid = int(d[2])
            if rid and not db_exec("SELECT 1 FROM watch WHERE id=? AND user_id=?", (rid, uid)):
                return await cq.answer("القناة مش موجودة", show_alert=True)
            kw_wait[uid] = rid
            cur = (db_exec("SELECT kw FROM watch WHERE id=?", (rid,))[0][0] if rid else cfg("watch_kw")) or ""
            who = "القناة دي" if rid else "كل القنوات الجديدة (الافتراضي)"
            return await show(cq, ui_prompt("🏷", f"فلتر العنوان — {who}",
                                            f"الحالي: {esc_t(cur) if cur else 'بدون فلتر'}",
                                            "اكتب الكلمات اللي لازم تكون في عنوان الفيديو",
                                            "مثال: <code>تانية بكلوريا</code>",
                                            "أكتر من بديل: <code>تانية بكلوريا, ثالث ثانوي</code>",
                                            "المطابقة بتتجاهل اختلاف الكتابة (ثانية/تانية، بكالوريا/بكلوريا)"),
                              KB([B("🚫 بدون فلتر (كل الفيديوهات)", "wt|kwx|" + d[2], S.DANGER)], [B("⬅️ رجوع", "wt|ls")]))
        elif sub == "kwx" and len(d) > 2 and d[2].isdigit():
            kw_wait.pop(uid, None)
            if int(d[2]): db_exec("UPDATE watch SET kw='' WHERE id=? AND user_id=?", (int(d[2]), uid))
            else: cfg_set("watch_kw", "")
            await cq.answer("✅ اتشال الفلتر")
        elif sub == "now":
            await cq.answer("🔄 بفحص القنوات...")
            n = 0
            for row in db_exec("SELECT id, user_id, url, title, seen, mode, COALESCE(kw, '') FROM watch WHERE user_id=?", (uid,)):
                try: n += await watch_check(row, fresh=True)
                except Exception as e: log.info("manual watch check failed: %s", e)
            if not n: await cq.answer("مفيش فيديوهات جديدة", show_alert=True)
            return
        txt, kb = watch_view(uid)
        return await show(cq, txt, kb)

    if act == "ps":
        b = batches.get(d[1]) if len(d) > 2 else None
        if not b or b.user_id != uid or b.started:
            return await cq.answer("انتهت صلاحية الطلب، ابعت الرابط تاني.", show_alert=True)
        op = d[2]
        arg = int(d[3]) if len(d) > 3 and d[3].lstrip("-").isdigit() else 0
        if op == "t":
            if 0 <= arg < len(b.items): b.sel ^= {arg}
        elif op == "p": b.page = arg
        elif op == "a": b.sel = set(range(len(b.items)))
        elif op == "n": b.sel = set()
        elif op == "i": b.sel = set(range(len(b.items))) - b.sel
        elif op == "go":
            if not b.sel: return await cq.answer("اختار فيديو واحد على الأقل", show_alert=True)
            b.items = [b.items[i] for i in sorted(b.sel)]
            await cq.answer(f"✅ {len(b.items)} فيديو")
            return await after_selection(b)
        txt, kb = sel_view(b)
        await safe_edit(b.msg, txt, kb)
        return await cq.answer()

    if act == "x":
        b = batches.get(d[1])
        if b and b.user_id == uid and not b.started:
            batches.pop(b.id, None)
        await cq.answer("✖️ اتلغى")
        if b and b.user_id == uid: await drop_preview(b)
        return await show_home(cq)

    if act == "c":
        b = batches.get(d[1])
        if b and b.user_id == uid:
            b.cancelled = True
            return await cq.answer("جاري الإلغاء...")
        return await cq.answer()

    if act == "ad":
        if not is_admin(uid):
            return await cq.answer("للأدمن فقط", show_alert=True)
        sub = d[1] if len(d) > 1 else ""
        if sub == "":
            return await show(cq, admin_home_text(), admin_kb())
        if sub in ADMIN_GROUPS:
            return await show(cq, ui_title("🛠", ADMIN_GROUPS[sub][0]) + "\n<i>اختار الأداة 👇</i>", admin_group_kb(sub))
        if sub == "rp":
            return await show(cq, report_text(24), KB([B("🔄 تحديث", "ad|rp", S.SUCCESS)], [B("⬅️ رجوع", "ad")]))
        if sub == "st":
            u = db_exec("SELECT COUNT(*), COALESCE(SUM(downloads),0) FROM users")[0]
            c = db_exec("SELECT COUNT(*) FROM cache")[0][0]
            act24 = db_exec("SELECT COUNT(DISTINCT user_id) FROM history WHERE ts > ?", (int(time.time()) - 86400,))[0][0]
            bn = db_exec("SELECT COUNT(*) FROM banned")[0][0]
            current_batches = list(batches.values())
            pending_batches = sum(not b.started and not b.done for b in current_batches)
            running_batches = sum(b.started and not b.done for b in current_batches)
            downloading = sum(it.status == "dl" for b in current_batches for it in b.items)
            uploading = sum(it.status == "up" for b in current_batches for it in b.items)
            runtime = await asyncio.to_thread(runtime_metrics_text)
            return await show(cq, ui_title("📊", "إحصائيات البوت") + "\n"
                f"👥 مستخدمين: <b>{u[0]}</b>   👤 نشطين 24س: <b>{act24}</b>   🚫 محظورين: <b>{bn}</b>\n"
                f"📥 تحميلات: <b>{u[1]}</b>   ⚡ في الكاش: <b>{c}</b>\n\n"
                "<b>🔄 الحالة الآن</b>\n" + ui_quote(
                    f"⏳ بانتظار الجودة: {pending_batches}   ⚙️ دفعات شغالة: {running_batches}",
                    f"⬇️ بينزل: {downloading}   ⬆️ بيترفع: {uploading}") + "\n\n"
                "<b>🎛 الإعدادات</b>\n" + ui_quote(
                    f"🚦 الحصة: {opt_label('quota')}  |  الحجم: {opt_label('max_mb')}  |  المدة: {opt_label('max_min')}  |  الجودة: {opt_label('max_h')}",
                    f"🚀 الإرسال: {opt_label('xfer')}  |  رفع متوازي: {fastio.SETTINGS['sessions']}×{fastio.SETTINGS['workers']}",
                    f"🌍 الوصول: {'عام' if cfg('public') == '1' else 'خاص'}  |  🛠 صيانة: {opt_label('maint')}",
                    f"📢 اشتراك إجباري: {cfg('fsub') or '⛔'}  |  🌐 cobalt: {'✅' if COBALT_API_URL else '❌'}  |  🐙 vidkraken: {'✅' if VIDKRAKEN_API_KEY else '❌'}  |  💧 علامة مائية: {'✅' if cfg('wm_on') == '1' else '⛔'}") + "\n\n"
                "<b>🖥 السيرفر</b>\n" + ui_quote(runtime) + "\n\n"
                "<b>🧩 المحركات</b>\n" + ui_quote(
                    f"aria2c: {'✅' if HAS_ARIA2 else '❌'}  |  تقليد المتصفح: {'✅' if IMPERSONATE else '❌'}  |  gallery-dl: {'✅' if HAS_GALLERY else '❌'}",
                    f"uvloop: {'✅' if HAS_UVLOOP else '❌'}  |  رفع متوازي: {UPLOAD_WORKERS if UPLOAD_TUNED else 4}",
                    f"🎨 ألوان: {'✅' if COLORS else '❌'}  |  🍪 كوكيز: {'✅' if has_cookies() else '❌'}  |  ✨ بريميوم: {'✅' if pe_active() else '⛔'}"),
                KB([B("🔄 تحديث", "ad|st", S.SUCCESS)], [B("⬅️ رجوع", "ad")]))
        if sub == "bc":
            if len(d) == 2:
                awaiting[uid] = "bc"
                return await show(cq, ui_prompt("📢", "إذاعة", "ابعت الرسالة اللي عايز تذيعها", "نص أو صورة أو فيديو..."),
                                  KB([B("❌ إلغاء", "ad|bc|no", S.DANGER)]))
            if d[2] == "no":
                awaiting.pop(uid, None); bc_pending.pop(uid, None)
                return await show(cq, admin_home_text(), admin_kb())
            if d[2] == "ok":
                p = bc_pending.pop(uid, None)
                if not p: return await cq.answer("مفيش رسالة معلّقة", show_alert=True)
                await safe_edit(cq.message, ui_note("wait", "جاري الإرسال...", "هتوصلك نتيجة الإذاعة هنا."))
                return asyncio.create_task(broadcast(cq, *p))
        if sub == "ck":
            awaiting.pop(uid, None)
            a = d[2] if len(d) > 2 else ""
            if a == "up":
                awaiting[uid] = "ck"
                return await show(cq, ui_prompt("📤", "رفع كوكيز يوتيوب", "ابعت ملف <code>cookies.txt</code>", "كملف Document (مش كنص)"),
                                  KB([B("⬅️ رجوع", "ad|ck")]))
            if a == "rm":
                for f in (COOKIE_FILE, COOKIE_FILE + ".envsig"):
                    try: os.remove(f)
                    except OSError: pass
                await cq.answer("اتحذفت")
            return await show(cq, ck_screen_text(), ck_kb())
        if sub == "pe":
            awaiting.pop(uid, None)
            a = d[2] if len(d) > 2 else ""
            if a == "add":
                awaiting[uid] = "pe"
                return await show(cq, ui_prompt("✨", "إضافة إيموجي بريميوم", "ابعت رسالة فيها الإيموجي البريميوم", "ممكن كذا واحد في نفس الرسالة"),
                                  KB([B("⬅️ رجوع", "ad|pe")]))
            if a == "tg":
                if not PE["map"]: return await cq.answer("ضيف إيموجي الأول", show_alert=True)
                cfg_set("pe_on", "0" if cfg("pe_on") == "1" else "1"); PE["broken"] = False; pe_reload()
            if a == "rm":
                cfg_set("pe_map", "{}"); cfg_set("pe_on", "0"); PE["broken"] = False; pe_reload()
            return await show(cq, pe_screen_text(), pe_kb())
        if sub == "cf":
            awaiting.pop(uid, None)
            a = d[2] if len(d) > 2 else ""
            if a == "pub":
                cfg_set("public", "0" if cfg("public") == "1" else "1")
            return await show(cq, cf_text(), cf_kb())
        if sub == "wm":
            awaiting.pop(uid, None)
            a, v = (d[2] if len(d) > 2 else ""), (d[3] if len(d) > 3 else "")
            if a == "tg":
                if cfg("wm_on") != "1" and wm_missing():
                    return await cq.answer(wm_missing(), show_alert=True)
                cfg_set("wm_on", "0" if cfg("wm_on") == "1" else "1")
            elif a == "ty" and v in ("text", "image"):
                cfg_set("wm_type", v)
                if cfg("wm_on") == "1" and wm_missing():
                    cfg_set("wm_on", "0")
                    await cq.answer(wm_missing() + " — العلامة اتقفلت لحد ما تكمّل", show_alert=True)
            elif a == "ps" and v in WM_POS_LABEL:
                cfg_set("wm_pos", v)
            elif a == "sz" and v in WM_SIZES:
                cfg_set("wm_size", v)
            elif a == "tx":
                awaiting[uid] = "wm_text"
                return await show(cq, ui_prompt("✏️", "نص العلامة المائية", "لحد 60 حرف، مثلًا <code>@channel</code>",
                                                "⚠️ العربي بيطلع بحروف مفصولة — للعربي استخدم صورة"),
                                  KB([B("⬅️ رجوع", "ad|wm")]))
            elif a == "im":
                awaiting[uid] = "wm_img"
                return await show(cq, ui_prompt("🖼", "صورة العلامة المائية", "الأفضل PNG بخلفية شفافة",
                                                "ابعتها كـ ملف (File) عشان الشفافية ما تضيعش"),
                                  KB([B("⬅️ رجوع", "ad|wm")]))
            return await show(cq, wm_screen_text(), wm_kb())
        if sub == "ct":
            awaiting.pop(uid, None)
            key = d[2] if len(d) > 2 else ""
            if key in ADMIN_OPTS:
                cfg_set(key, opt_next(key))
                await cq.answer(f"{ADMIN_OPTS[key][0]}: {opt_label(key)}")
            return await show(cq, ctl_text(), ctl_kb())
        if sub == "us":
            awaiting.pop(uid, None)
            a = d[2] if len(d) > 2 else ""
            if a in ("ban", "unban", "allow", "unallow"):
                awaiting[uid] = a
                label = {"ban": "حظره", "unban": "فك الحظر عنه", "allow": "السماح له", "unallow": "إزالة السماح عنه"}[a]
                return await show(cq, ui_prompt("👤", "إدارة مستخدم", f"ابعت أيدي المستخدم الرقمي اللي عايز {label}"),
                                  KB([B("⬅️ رجوع", "ad|us")]))
            return await show(cq, users_text(), users_kb())
        if sub == "bl":
            awaiting.pop(uid, None)
            a = d[2] if len(d) > 2 else ""
            if a in ("add", "rm"):
                awaiting[uid] = "blk_" + a
                return await show(cq, ui_prompt("🌐", "موقع", "ابعت اسم الموقع", "مثلًا <code>example.com</code>"),
                                  KB([B("⬅️ رجوع", "ad|bl")]))
            return await show(cq, blk_text(), blk_kb())
        if sub == "fs":
            awaiting.pop(uid, None)
            a = d[2] if len(d) > 2 else ""
            if a == "set":
                awaiting[uid] = "fsub"
                return await show(cq, ui_prompt("📢", "قناة الاشتراك الإجباري", "ابعت يوزر القناة العامة، مثلًا <code>@mychannel</code>",
                                                "لازم البوت يكون أدمن فيها"),
                                  KB([B("⬅️ رجوع", "ad|fs")]))
            if a == "off":
                cfg_set("fsub", ""); _sub_cache.clear()
                await cq.answer("اتقفل")
            return await show(cq, fs_text(), fs_kb())
        if sub == "lg":
            return await show(cq, log_text(), KB([B("🔄 تحديث", "ad|lg", S.SUCCESS)], [B("⬅️ رجوع", "ad")]))
        if sub == "bk":
            await cq.answer("بجهّز النسخة...")
            tmp = os.path.join(tempfile.gettempdir(), f"dl_backup_{int(time.time())}.db")
            try:
                await asyncio.to_thread(make_db_backup, tmp)
                await app.send_document(cq.message.chat.id, tmp, caption="💾 نسخة احتياطية من قاعدة بيانات البوت\n🕒 " + _dt.now(_TZ).strftime("%Y-%m-%d %H:%M") if _TZ else "💾 نسخة احتياطية من قاعدة بيانات البوت")
            except Exception as e:
                await cq.message.reply_text(ui_note("err", "فشلت النسخة الاحتياطية", esc_t(clean_err(e), 150)))
            finally:
                try: os.remove(tmp)
                except OSError: pass
            return
        if sub == "sp":
            await cq.answer("بدأ الاختبار ⚡")
            return asyncio.create_task(speed_test(cq))
        if sub == "cc":
            if len(d) == 2:
                return await show(cq, ui_note("warn", "تمسح الكاش كله؟", "الفيديوهات هتتحمل من الأول."),
                                  KB([B("✅ أيوه امسح", "ad|cc|ok", S.DANGER)], [B("🔙 لأ، رجوع", "ad")]))
            db_exec("DELETE FROM cache")
            await cq.answer("✅ اتمسح")
            return await show(cq, admin_home_text(), admin_kb())
    await cq.answer()

# ───────────── التشغيل ─────────────
async def batch_gc_loop():
    """بيمسح الطلبات اللي اتفحصت ومحدش اختار لها جودة/فيديوهات (بتفضل في الذاكرة وفي ملف المعاينة للأبد)."""
    last_db_prune = 0.0
    while True:
        await asyncio.sleep(600)
        try:
            prune_user_gates()
            probe_cache_trim()
            WATCH_MEMO.clear() if len(WATCH_MEMO) > 200 else None
            await asyncio.to_thread(clean_stale_tmp, 21600)         # بقايا تحميلات أقدم من 6 ساعات
            if time.time() - last_db_prune > 86400:                  # مرة كل يوم: روابط قديمة جدًا من urlmap
                last_db_prune = time.time()
                await asyncio.to_thread(db_exec, "DELETE FROM urlmap WHERE ts < ?", (int(time.time()) - 120 * 86400,))
            for bid, bb in list(batches.items()):
                if not bb.started and not bb.done and time.time() - bb.created > 3600:
                    batches.pop(bid, None)
                    psel_wait.pop(bb.user_id, None) if psel_wait.get(bb.user_id) == bid else None
                    await drop_preview(bb)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            log.debug("batch gc: %s", e)

async def engine_update_loop():
    """يحدّث yt-dlp تلقائيًا كل ENGINE_UPDATE_HOURS ساعة (الافتراضي 24؛ 0 = إيقاف). لو نزلت نسخة جديدة
    بيستنى لحد ما مفيش تحميلات شغّالة وبعدين يعيد تشغيل نفسه (exec) عشان النسخة الجديدة تتفعّل."""
    try: hours = float(os.getenv("ENGINE_UPDATE_HOURS", "24") or 0)
    except ValueError: hours = 24
    if hours <= 0: return
    await asyncio.sleep(900)
    while True:
        try:
            before = yt_dlp.version.__version__
            proc = await asyncio.create_subprocess_exec(
                sys.executable, "-m", "pip", "install", "--user", "-U", "-q", "--disable-pip-version-check",
                "yt-dlp[default,curl-cffi]", stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE)
            await asyncio.wait_for(proc.communicate(), 300)
            out = await asyncio.to_thread(lambda: subprocess.run(
                [sys.executable, "-c", "import yt_dlp.version as v; print(v.__version__)"],
                capture_output=True, text=True, timeout=60).stdout.strip())
            if out and out != before:
                log.info("yt-dlp updated %s -> %s; restarting when idle", before, out)
                for _ in range(360):          # لحد 30 دقيقة نستنى التحميلات الجارية
                    if not batches: break
                    await asyncio.sleep(5)
                for aid in ADMIN_IDS:
                    try: await app.send_message(aid, pe_html(ui_note("ok", "اتحدّث محرك التحميل", f"yt-dlp {before} ← {out} — بيعيد التشغيل ثواني")))
                    except Exception: pass
                await asyncio.sleep(2)
                os.execv(sys.executable, [sys.executable] + sys.argv)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            log.info("engine auto-update skipped: %s", e)
        await asyncio.sleep(hours * 3600)

async def main():
    # الافتراضي (cpu+4 خيوط) كان بيحدّد كام فيديو بيتحمّلوا فعلاً مع بعض؛ نكبّره عشان التحميل المتزامن يبقى حقيقي
    asyncio.get_running_loop().set_default_executor(
        ThreadPoolExecutor(max_workers=int(os.getenv("THREADS", str(DEFAULT_THREADS))), thread_name_prefix="bot"))
    pe_reload()
    clean_stale_tmp(max_age=0)      # أي بقايا من تشغيل سابق (البوت لسه مبدأش يحمّل حاجة)
    await app.start()
    try:
        user_cmds = [BotCommand("start", "🏠 القائمة الرئيسية"), BotCommand("history", "📜 سجل تحميلاتي"),
                     BotCommand("favorites", "⭐ المفضلة"), BotCommand("settings", "⚙️ الإعدادات"),
                     BotCommand("watch", "🔔 مراقبة قناة"), BotCommand("watches", "📋 قنواتي المراقبة"),
                     BotCommand("help", "❓ المساعدة")]
        await app.set_bot_commands(user_cmds)
        for aid in ADMIN_IDS:
            try: await app.set_bot_commands(user_cmds + [BotCommand("admin", "🛠 لوحة الأدمن"),
                                                         BotCommand("speed", "⚡ اختبار السرعة")],
                                            scope=BotCommandScopeChat(chat_id=aid))
            except Exception as e: log.info("admin commands for %s: %s", aid, e)
    except Exception as e: log.info("set_bot_commands: %s", e)
    log.info("sites: %s | aria2c: %s | impersonate: %s | gallery-dl: %s | uvloop: %s | upload-workers: %s | colors: %s | db: %s | cookies: %s | proxy: %s",
             SITE_COUNT, HAS_ARIA2, bool(IMPERSONATE), HAS_GALLERY, HAS_UVLOOP,
             UPLOAD_WORKERS if UPLOAD_TUNED else 4, COLORS, DB_PATH, has_cookies(), bool(PROXY))
    report_task = asyncio.create_task(daily_report_loop())
    update_task = asyncio.create_task(engine_update_loop())
    watch_task = asyncio.create_task(watch_loop())
    gc_task = asyncio.create_task(batch_gc_loop())
    await idle()
    report_task.cancel(); update_task.cancel(); watch_task.cancel(); gc_task.cancel()
    await app.stop()

if __name__ == "__main__":
    # في kurigram الحديثة app.run() مبقاش بياخد coroutine؛ بنشغّل main على نفس لوب العميل (اللي اتسجّلت عليه الهاندلرز)
    app.loop.run_until_complete(main())
