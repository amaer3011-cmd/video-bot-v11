"""
نقل سريع لتليجرام:
  • HttpSource  : بيقرا الفيديو مباشرةً من رابط المصدر (Range متوازي) ويرفعه لتليجرام أثناء ما بيتقرا،
                  من غير ما يتحفظ على القرص — زمن العملية ≈ أبطأ طرف (تنزيل أو رفع) بدل مجموعهم.
  • FileSource  : نفس الرفع المتوازي لملف محلي (للحالات اللي لازم فيها دمج/علامة مائية قبل الرفع).
  • الرفع نفسه  : عدة جلسات Media منفصلة × عدة طلبات متوازية (بدل جلسة واحدة)، وكل جزء 512KB مستقل.
أي فشل بيترفع كاستثناء؛ والمتصل (bot.py) هو اللي بيرجع للمسار القديم.
"""
import asyncio, functools, inspect, io, logging, math, os, re, threading, time
from urllib.parse import urljoin

import requests
from pyrogram import raw
from pyrogram.errors import FloodWait

log = logging.getLogger("vidbot.fastio")

PART = 512 * 1024                 # أقصى حجم جزء يقبله تليجرام
BIG = 10 * 1024 * 1024            # فوق ده بيتعامل كملف كبير (SaveBigFilePart)
SEG_PARTS = 8                     # كل طلب Range = 8 أجزاء = 4 MiB
SETTINGS = {"workers": 16, "sessions": 4}
_REDIRECTS = (301, 302, 303, 307, 308)
_BAD_CTYPE = ("text/", "application/json", "application/vnd.apple", "application/x-mpegurl",
              "application/dash", "application/xml")
_tls = threading.local()


class DirectError(Exception):
    """المصدر مينفعش يتبث مباشرة (مفيش Range / حجم مجهول / رابط غير آمن ...)."""


def configure(workers=None, sessions=None):
    if workers: SETTINGS["workers"] = max(1, int(workers))
    if sessions: SETTINGS["sessions"] = max(1, int(sessions))


def _http():
    s = getattr(_tls, "s", None)
    if s is None:
        s = requests.Session()
        ad = requests.adapters.HTTPAdapter(pool_connections=4, pool_maxsize=8, max_retries=0)
        s.mount("https://", ad)
        s.mount("http://", ad)
        _tls.s = s
    return s


# ───────────── مصادر البيانات ─────────────
class Source:
    """مصدر بيقرا نطاق بايتات (sync — بيتشغّل في thread). له .name و .size (Pyrogram بيستخدمهم)."""
    name = "file.mp4"
    size = 0
    cancelled = None            # callable → True لو المستخدم ألغى

    def read_range(self, start, n):
        raise NotImplementedError

    def close(self):
        pass


class FileSource(Source):
    def __init__(self, path, name=None):
        self.path = path
        self.name = name or os.path.basename(path)
        self.size = os.path.getsize(path)

    def read_range(self, start, n):
        with open(self.path, "rb") as f:
            f.seek(start)
            return f.read(n)


class HttpSource(Source):
    def __init__(self, url, size, name, headers=None, proxy=None):
        self.url, self.size, self.name = url, int(size), name
        self.headers = dict(headers or {})
        self.headers["Accept-Encoding"] = "identity"
        self.proxies = {"http": proxy, "https": proxy} if proxy else None

    @classmethod
    def open(cls, url, name, headers=None, proxy=None, check=None, max_size=None):
        """sync: يتتبع التحويلات (وبيفحص كل قفزة بـ check) ويتأكد إن السيرفر بيدعم Range ومعروف الحجم."""
        h = dict(headers or {})
        h["Accept-Encoding"] = "identity"
        px = {"http": proxy, "https": proxy} if proxy else None
        cur = url
        for _ in range(6):
            if check and not check(cur):
                raise DirectError("unsafe url")
            r = _http().get(cur, headers={**h, "Range": "bytes=0-0"}, stream=True,
                            allow_redirects=False, timeout=(10, 20), proxies=px)
            try:
                if r.status_code in _REDIRECTS and r.headers.get("location"):
                    cur = urljoin(cur, r.headers["location"])
                    continue
                if r.status_code != 206:
                    raise DirectError(f"range unsupported (HTTP {r.status_code})")
                ctype = (r.headers.get("content-type") or "").lower()
                if ctype.startswith(_BAD_CTYPE):
                    raise DirectError(f"not a media stream ({ctype})")
                m = re.match(r"bytes\s+\d+-\d+/(\d+)", r.headers.get("content-range", ""))
                if not m:
                    raise DirectError("unknown size")
                size = int(m.group(1))
            finally:
                r.close()
            if size <= 0:
                raise DirectError("empty")
            if max_size and size > max_size:
                raise DirectError("too big")
            return cls(cur, size, name, headers, proxy)
        raise DirectError("too many redirects")

    def read_range(self, start, n):
        end = min(start + n, self.size) - 1
        want = end - start + 1
        last = None
        for attempt in range(5):
            if self.cancelled and self.cancelled():
                raise DirectError("cancelled")
            try:
                r = _http().get(self.url, headers={**self.headers, "Range": f"bytes={start}-{end}"},
                                allow_redirects=False, timeout=(10, 60), proxies=self.proxies)
                if r.status_code == 206 and len(r.content) == want:
                    return r.content
                last = DirectError(f"HTTP {r.status_code}, got {len(r.content)}/{want} bytes")
                if r.status_code in (301, 302, 303, 307, 308, 401, 403, 404, 410):
                    break                  # الرابط انتهى/اتمنع — إعادة المحاولة ملهاش لازمة
            except requests.RequestException as e:
                last = e
            time.sleep(0.4 * (attempt + 1))
        raise DirectError(f"read failed @{start}: {last}")


# ───────────── الرفع المتوازي ─────────────
async def _call_progress(progress, current, total, args):
    try:
        if inspect.iscoroutinefunction(progress):
            await progress(current, total, *args)
        else:
            progress(current, total, *args)
    except Exception as e:                     # شاشة التقدم مش مبرر نفشل الرفع بسببها
        log.debug("progress callback failed: %s", e)


async def _send_part(sess, file_id, idx, total, chunk):
    for attempt in range(4):
        try:
            ok = await sess.invoke(raw.functions.upload.SaveBigFilePart(
                file_id=file_id, file_part=idx, file_total_parts=total, bytes=chunk))
            if ok is False:
                raise RuntimeError("SaveBigFilePart returned False")
            return
        except FloodWait as e:
            await asyncio.sleep(min(e.value + 1, 30))
        except asyncio.CancelledError:
            raise
        except Exception:
            if attempt == 3:
                raise
            await asyncio.sleep(0.5 * (attempt + 1))
    raise RuntimeError("flood wait persisted")


async def upload_source(client, src, progress=None, progress_args=(), workers=None, sessions=None):
    """يرفع src لتليجرام بالتوازي ويرجّع InputFileBig جاهز لـ SendMedia."""
    size = src.size
    if size <= 0:
        raise ValueError("empty source")
    workers = workers or SETTINGS["workers"]
    sessions = max(1, min(sessions or SETTINGS["sessions"], workers))
    total_parts = int(math.ceil(size / PART))
    loop = asyncio.get_running_loop()
    file_id = client.rnd_id()
    dc_id = await client.storage.dc_id()

    opened = []
    res = await asyncio.gather(*[client.get_session(dc_id, is_media=True, temporary=True)
                                 for _ in range(sessions)], return_exceptions=True)
    for r in res:
        if isinstance(r, Exception):
            log.warning("extra media session failed: %s", r)
        else:
            opened.append(r)
    if not opened:                              # آخر حل: الجلسة المشتركة
        opened = [await client.get_session(dc_id, is_media=True)]
        shared = True
    else:
        shared = False

    seg_bytes = SEG_PARTS * PART
    segments = iter(range(int(math.ceil(size / seg_bytes))))
    state = {"done": 0}
    stop = {"flag": False}

    def is_cancelled():
        return bool(src.cancelled and src.cancelled())

    async def worker(k):
        sess = opened[k % len(opened)]
        for seg in segments:                   # iterator مشترك: asyncio أحادي الخيط فمفيش تضارب
            if stop["flag"] or is_cancelled():
                return
            start = seg * seg_bytes
            n = min(seg_bytes, size - start)
            data = await loop.run_in_executor(None, src.read_range, start, n)
            for off in range(0, n, PART):
                if stop["flag"] or is_cancelled():
                    return
                chunk = data[off:off + PART]
                await _send_part(sess, file_id, (start + off) // PART, total_parts, chunk)
                state["done"] += len(chunk)
                if progress:
                    await _call_progress(progress, state["done"], size, progress_args)

    tasks = [loop.create_task(worker(k)) for k in range(workers)]
    try:
        await asyncio.gather(*tasks)
    except BaseException:
        stop["flag"] = True
        for t in tasks:
            t.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        raise
    finally:
        if not shared:
            await asyncio.gather(*[s.stop() for s in opened], return_exceptions=True)
    if is_cancelled() and state["done"] < size:
        raise DirectError("cancelled")
    if state["done"] < size:
        raise RuntimeError(f"incomplete upload {state['done']}/{size}")
    return raw.types.InputFileBig(id=file_id, parts=total_parts, name=src.name)


def install(client_cls, enabled=lambda: True):
    """بيلفّ Client.save_file: أي Source (أو مسار ملف كبير) بيروح للرفع المتوازي، والباقي للأصلي."""
    orig = client_cls.save_file

    async def save_file(self, path, file_id=None, file_part=0, progress=None, progress_args=()):
        if isinstance(path, Source):
            if file_id is not None:            # جزء ناقص طلبه تليجرام
                dc_id = await self.storage.dc_id()
                sess = await self.get_session(dc_id, is_media=True)
                data = await asyncio.get_running_loop().run_in_executor(
                    None, path.read_range, file_part * PART, PART)
                await _send_part(sess, file_id, file_part, int(math.ceil(path.size / PART)), data)
                return None
            if path.size <= BIG:               # ملف صغير: المسار الأصلي (md5) بعد قراءته كله
                data = await asyncio.get_running_loop().run_in_executor(None, path.read_range, 0, path.size)
                bio = io.BytesIO(data)
                bio.name = path.name
                return await orig(self, bio, None, 0, progress, progress_args)
            return await upload_source(self, path, progress, progress_args)
        if (isinstance(path, (str, os.PathLike)) and file_id is None and file_part == 0
                and enabled() and os.path.isfile(path)):
            try:
                size = os.path.getsize(path)
            except OSError:
                size = 0
            if size > BIG:
                try:
                    return await upload_source(self, FileSource(os.fspath(path)), progress, progress_args)
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    log.warning("fast upload failed (%s); falling back to stock uploader", e)
        return await orig(self, path, file_id, file_part, progress, progress_args)

    client_cls.save_file = save_file
    return orig
