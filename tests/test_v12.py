"""اختبارات v12 — بتشتغل من غير تليجرام ولا إنترنت:  python -m pytest -q tests"""
import asyncio, math, os, sys, tempfile, time

os.environ.setdefault("API_ID", "1"); os.environ.setdefault("API_HASH", "x"); os.environ.setdefault("BOT_TOKEN", "1:x")
os.environ["DB_PATH"] = os.path.join(tempfile.mkdtemp(), "t.db")
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pytest
import bot, fastio
from pyrogram import raw
from pyrogram.errors import BadRequest


def run(coro):
    return asyncio.run(coro)


# ───────────── Gate / user_sem ─────────────
def test_gate_limits_concurrency():
    async def go(n, jobs):
        g, cur, peak = bot.Gate(n), [0], [0]
        async def job():
            async with g:
                cur[0] += 1; peak[0] = max(peak[0], cur[0])
                await asyncio.sleep(0.03)
                cur[0] -= 1
        await asyncio.gather(*[job() for _ in range(jobs)])
        assert g.active == 0 and g.waiting == 0
        return peak[0]
    assert run(go(2, 8)) == 2
    assert run(go(0, 8)) == 8            # 0 = بلا سقف


def test_gate_cancel_while_waiting_does_not_leak():
    async def go():
        g = bot.Gate(1)
        async def holder():
            async with g: await asyncio.sleep(0.2)
        async def waiter():
            async with g: pass
        h = asyncio.create_task(holder()); await asyncio.sleep(0.01)
        w = asyncio.create_task(waiter()); await asyncio.sleep(0.01)
        assert g.waiting == 1
        w.cancel()
        await asyncio.gather(w, return_exceptions=True)
        await h
        assert (g.active, g.waiting) == (0, 0)
        async with g: pass               # لسه قابل للاستخدام (مفيش slot ضايع)
    run(go())


def test_user_sem_same_gate_and_prune(monkeypatch):
    monkeypatch.setattr(bot, "MAX_PER_USER", 2)
    g1, g2 = bot.user_sem(111), bot.user_sem(111)
    assert g1 is g2 and g1.n == 2 and bot.user_sem(222) is not g1
    bot.prune_user_gates()
    assert 111 not in bot._USER_GATES
    monkeypatch.setattr(bot, "MAX_PER_USER", 0)
    assert bot.user_sem(1) is bot.UNLIMITED


# ───────────── probe cache + single flight ─────────────
def _info(**kw):
    d = {"id": "v1", "title": "T", "formats": [{"format_id": "18", "url": "https://x/y.mp4"}], "extractor_key": "Youtube"}
    d.update(kw); return d


def test_probe_shared_single_flight_and_cache(monkeypatch):
    calls = []
    def fake_probe(url):
        calls.append(url); time.sleep(0.15)
        return [bot.Item(url, "T", "youtube:v1", info=_info())], None
    monkeypatch.setattr(bot, "probe", fake_probe)
    monkeypatch.setattr(bot, "PROBE_TTL", 600)
    bot.PROBE_CACHE.clear()
    async def go():
        rs = await asyncio.gather(*[bot.probe_shared("https://y/1") for _ in range(6)])
        assert len(calls) == 1                                  # 6 طلبات = فحص واحد
        items = [r[0][0] for r in rs]
        assert len({id(i) for i in items}) == 6                 # كل واحد ليه Item مستقل (الحالة بتتغيّر)
        assert all(i.info is items[0].info for i in items)      # والـ info مشتركة للقراءة
        items[0].status = "done"; items[0].key = "changed"
        again = await bot.probe_shared("https://y/1")           # كاش
        assert len(calls) == 1 and again[0][0].status == "wait" and again[0][0].key == "youtube:v1"
        bot.PROBE_CACHE["https://y/1"] = (time.monotonic() - 10_000, *bot.PROBE_CACHE["https://y/1"][1:])
        await bot.probe_shared("https://y/1")                   # انتهت صلاحيته → فحص جديد
        assert len(calls) == 2
    run(go())


def test_probe_not_cached_for_live_playlist_or_errors(monkeypatch):
    bot.PROBE_CACHE.clear()
    state = {"mode": "live", "n": 0}
    def fake_probe(url):
        state["n"] += 1
        if state["mode"] == "live":
            return [bot.Item(url, "T", "k", info=_info(is_live=True))], None
        if state["mode"] == "pl":
            return [bot.Item(url, "a", "k1", info=_info()), bot.Item(url, "b", "k2", info=_info())], "PL"
        raise RuntimeError("boom")
    monkeypatch.setattr(bot, "probe", fake_probe)
    async def go():
        for mode in ("live", "pl"):
            state["mode"] = mode
            await bot.probe_shared("https://y/" + mode); await bot.probe_shared("https://y/" + mode)
        assert state["n"] == 4 and not bot.PROBE_CACHE
        state["mode"] = "err"
        rs = await asyncio.gather(*[bot.probe_shared("https://y/e") for _ in range(3)], return_exceptions=True)
        assert all(isinstance(r, RuntimeError) for r in rs) and state["n"] == 5   # الخطأ اتشارك ومتخزّنش
        await asyncio.gather(bot.probe_shared("https://y/e"), return_exceptions=True)
        assert state["n"] == 6                                                    # المحاولة اللي بعدها بتعيد الفحص
        assert not bot.PROBE_FLIGHTS
    run(go())


def test_probe_cache_is_bounded(monkeypatch):
    monkeypatch.setattr(bot, "PROBE_CACHE_MAX", 5)
    monkeypatch.setattr(bot, "probe", lambda u: ([bot.Item(u, "T", "k:" + u, info=_info())], None))
    bot.PROBE_CACHE.clear()
    async def go():
        for i in range(20): await bot.probe_shared(f"https://y/{i}")
    run(go())
    assert len(bot.PROBE_CACHE) <= 5


# ───────────── run_item: دمج التحميلات المتطابقة ─────────────
def _batch(uid=1, **kw):
    return bot.Batch(id=os.urandom(3).hex(), user_id=uid, chat_id=uid, items=[], mode="720", **kw)


def _setup_run_item(monkeypatch, fetch):
    bot.db_exec("DELETE FROM cache")
    sent = []
    async def fake_send(b, it, src, info, thumb=None, progress=None):
        sent.append((it.key, src)); return "FID"
    monkeypatch.setattr(bot, "send_media", fake_send)
    monkeypatch.setattr(bot, "_fetch_and_send", fetch)
    return sent


def test_same_video_downloaded_once(monkeypatch):
    fetches = []
    async def fetch(b, it, cm, wm):
        fetches.append(it.key); await asyncio.sleep(0.15)
        bot.cache_put(it.key, cm, "FILEID"); it.status = "done"
    sent = _setup_run_item(monkeypatch, fetch)
    async def go():
        items = [bot.Item("https://y/1", "T", "youtube:same") for _ in range(4)]
        await asyncio.gather(*[bot.run_item(_batch(uid=i), it) for i, it in enumerate(items)])
        return items
    items = run(go())
    assert len(fetches) == 1                                   # تحميل واحد بس
    assert sorted(i.route for i in items).count("cache") == 3  # والتلاتة التانيين اتبعتوا من الكاش
    assert all(i.status == "done" for i in items) and len(sent) == 3
    assert not bot.FLIGHTS


def test_followers_share_leader_failure_fast(monkeypatch):
    fetches = []
    async def fetch(b, it, cm, wm):
        fetches.append(1); await asyncio.sleep(0.1); raise RuntimeError("sign in to confirm you're not a bot")
    _setup_run_item(monkeypatch, fetch)
    async def go():
        items = [bot.Item("https://y/2", "T", "youtube:bad") for _ in range(5)]
        t0 = time.monotonic()
        await asyncio.gather(*[bot.run_item(_batch(uid=i), it) for i, it in enumerate(items)])
        return items, time.monotonic() - t0
    items, took = run(go())
    assert len(fetches) == 1 and took < 0.5                    # مش 5 محاولات ورا بعض
    assert all(i.status == "err" and i.detail == items[0].detail and i.detail for i in items)
    assert not bot.FLIGHTS


def test_cancelled_leader_does_not_poison_followers(monkeypatch):
    fetches = []
    async def fetch(b, it, cm, wm):
        fetches.append(b.cancelled); await asyncio.sleep(0.05)
        if b.cancelled: raise RuntimeError("أُلغي")
        bot.cache_put(it.key, cm, "F"); it.status = "done"
    _setup_run_item(monkeypatch, fetch)
    async def go():
        b1, b2 = _batch(1), _batch(2)
        i1, i2 = bot.Item("https://y/3", "T", "youtube:c"), bot.Item("https://y/3", "T", "youtube:c")
        t1 = asyncio.create_task(bot.run_item(b1, i1)); await asyncio.sleep(0.01)
        t2 = asyncio.create_task(bot.run_item(b2, i2)); await asyncio.sleep(0.01)
        b1.cancelled = True
        await asyncio.gather(t1, t2)
        return i1, i2
    i1, i2 = run(go())
    assert i1.status == "err" and i2.status == "done" and len(fetches) == 2


def test_stale_cache_entry_is_deleted_on_bad_request(monkeypatch):
    async def fetch(b, it, cm, wm):
        bot.cache_put(it.key, cm, "NEW"); it.status = "done"
    _setup_run_item(monkeypatch, fetch)
    async def bad_send(b, it, src, info, thumb=None, progress=None):
        if src == "OLD": raise BadRequest()
        return "x"
    monkeypatch.setattr(bot, "send_media", bad_send)
    bot.cache_put("youtube:stale", "720", "OLD")
    it = bot.Item("https://y/4", "T", "youtube:stale")
    run(bot.run_item(_batch(), it))
    assert it.status == "done" and bot.cache_get("youtube:stale", "720") == "NEW"


# ───────────── watch memo ─────────────
def test_watch_fetch_cached(monkeypatch):
    n = [0]
    def fake_fetch(url, limit=10):
        n[0] += 1; return "name", [("1", "u", "t", False, "youtube")]
    monkeypatch.setattr(bot, "watch_fetch", fake_fetch)
    bot.WATCH_MEMO.clear()
    async def go():
        await bot.watch_fetch_cached("c"); await bot.watch_fetch_cached("c")
        assert n[0] == 1
        await bot.watch_fetch_cached("c", fresh=True)
        assert n[0] == 2
    run(go())


# ───────────── DB ─────────────
def test_indexes_exist():
    names = {r[0] for r in bot.db_exec("SELECT name FROM sqlite_master WHERE type='index'")}
    assert {"idx_history_user_ts", "idx_history_ts", "idx_urlmap_ts"} <= names


# ───────────── fastio ─────────────
class FakeSession:
    def __init__(self, log): self.log, self.stopped = log, False
    async def invoke(self, req):
        assert isinstance(req, raw.functions.upload.SaveBigFilePart)
        self.log[req.file_part] = self.log.get(req.file_part, 0) + 1
        self.log.setdefault("data", {})[req.file_part] = req.bytes
        self.log.setdefault("total", set()).add(req.file_total_parts)
        return True
    async def stop(self): self.stopped = True


class FakeClient:
    def __init__(self): self.log, self.sessions = {}, []
    def rnd_id(self): return 777
    @property
    def storage(self):
        class S:
            async def dc_id(_): return 2
        return S()
    async def get_session(self, dc, is_media=False, temporary=False):
        s = FakeSession(self.log); self.sessions.append(s); return s


class PatternSource(fastio.Source):
    def __init__(self, size): self.size, self.name = size, "v.mp4"
    def read_range(self, start, n):
        return bytes((start + i) % 251 for i in range(n))


@pytest.mark.parametrize("size,workers,sessions", [
    (11 * 1024 * 1024, 64, 6), (12 * 1024 * 1024 + 123, 12, 6), (50 * 1024 * 1024 + 7, 12, 4), (10 * 1024 * 1024 + 1, 1, 1)])
def test_upload_source_sends_every_part_exactly_once(size, workers, sessions):
    c, src = FakeClient(), PatternSource(size)
    res = run(fastio.upload_source(c, src, workers=workers, sessions=sessions))
    total = math.ceil(size / fastio.PART)
    assert res.parts == total and c.log["total"] == {total}
    assert all(c.log[i] == 1 for i in range(total))            # كل جزء اتبعت مرة واحدة بالظبط
    assert b"".join(c.log["data"][i] for i in range(total)) == src.read_range(0, size)
    assert all(s.stopped for s in c.sessions)
    assert len(c.sessions) <= min(sessions, workers)


def test_upload_medium_file_uses_all_workers_and_few_sessions():
    c = FakeClient()
    run(fastio.upload_source(c, PatternSource(12 * 1024 * 1024), workers=12, sessions=6))
    assert len(c.sessions) == 6                                # كان بيفتح 6 حتى لو الملف 3 قطع بس
    c2 = FakeClient()
    run(fastio.upload_source(c2, PatternSource(10 * 1024 * 1024 + 1), workers=2, sessions=6))
    assert len(c2.sessions) == 2                               # مش أكتر من الـ workers اللي هتشتغل


def test_upload_cancel_and_failure_cleanup():
    c, src = FakeClient(), PatternSource(30 * 1024 * 1024)
    src.cancelled = lambda: True
    with pytest.raises(fastio.DirectError):
        run(fastio.upload_source(c, src, workers=8, sessions=4))
    assert all(s.stopped for s in c.sessions)

    class Boom(FakeSession):
        async def invoke(self, req): raise RuntimeError("net down")
    class BoomClient(FakeClient):
        async def get_session(self, dc, is_media=False, temporary=False):
            s = Boom(self.log); self.sessions.append(s); return s
    bc = BoomClient()
    t0 = time.monotonic()
    with pytest.raises(RuntimeError):
        run(fastio.upload_source(bc, PatternSource(20 * 1024 * 1024), workers=6, sessions=3))
    assert all(s.stopped for s in bc.sessions)


def test_http_source_read_range_uses_dedicated_pool():
    assert fastio._IO_POOL is not None and fastio._IO_THREADS >= 4


# ───────────── مسارات run_item الحقيقية (بعد إعادة الهيكلة) ─────────────
def _wire_paths(monkeypatch, xfer):
    bot.db_exec("DELETE FROM cache")
    bot.cfg_set("xfer", xfer)
    sent, order = [], []
    async def fake_send(b, it, src, info, thumb=None, progress=None):
        sent.append(src); return "FID"
    async def fake_thumb(*a, **k): return None
    def fake_dl(it, mode, outdir, hook=None):
        p = os.path.join(outdir, "v.mp4"); open(p, "wb").write(b"x" * 2048)
        order.append("dl"); return p, {"title": "T"}, mode
    monkeypatch.setattr(bot, "send_media", fake_send)
    monkeypatch.setattr(bot, "get_thumb", fake_thumb)
    monkeypatch.setattr(bot, "make_thumb", fake_thumb)
    monkeypatch.setattr(bot, "do_download_fit", fake_dl)
    return sent, order


def test_disk_path_end_to_end(monkeypatch):
    sent, order = _wire_paths(monkeypatch, "disk")
    it = bot.Item("https://y/d", "T", "youtube:disk")
    b = _batch(); b.items = [it]
    run(bot.run_item(b, it))
    assert it.status == "done" and it.route == "disk" and order == ["dl"] and len(sent) == 1
    assert bot.cache_get("youtube:disk", "720") == "FID"
    assert (bot.DL_SEM.active, bot.UP_SEM.active, bot.DL_SEM.waiting) == (0, 0, 0)


def test_direct_path_and_fallback_to_disk(monkeypatch):
    sent, order = _wire_paths(monkeypatch, "direct")
    plan = bot.DirectPlan("https://cdn/x.mp4", {}, "x.mp4", {"title": "T"})
    monkeypatch.setattr(bot, "plan_direct", lambda it, mode: plan)
    state = {"fail": False}
    async def fake_direct(b, it, p):
        if state["fail"]: raise RuntimeError("range broke")
        return "DIRECTFID"
    monkeypatch.setattr(bot, "send_direct", fake_direct)
    it = bot.Item("https://y/e", "T", "youtube:dir")
    run(bot.run_item(_batch(), it))
    assert it.status == "done" and it.route == "direct" and order == []
    assert bot.cache_get("youtube:dir", "720") == "DIRECTFID"
    state["fail"] = True
    it2 = bot.Item("https://y/f", "T", "youtube:dir2")
    run(bot.run_item(_batch(), it2))
    assert it2.status == "done" and it2.route == "disk" and order == ["dl"]      # فشل المباشر → رجع للتنزيل العادي
    assert (bot.UP_SEM.active, bot.DL_SEM.active) == (0, 0)


def test_caps_hold_under_load_and_all_finish(monkeypatch):
    sent, order = _wire_paths(monkeypatch, "disk")
    monkeypatch.setattr(bot, "DL_SEM", bot.Gate(2))
    cur, peak = [0], [0]
    def slow_dl(it, mode, outdir, hook=None):
        import threading
        cur[0] += 1; peak[0] = max(peak[0], cur[0]); time.sleep(0.08); cur[0] -= 1
        p = os.path.join(outdir, "v.mp4"); open(p, "wb").write(b"x" * 100); return p, {"title": "T"}, mode
    monkeypatch.setattr(bot, "do_download_fit", slow_dl)
    monkeypatch.setattr(bot, "MAX_PER_USER", 0)
    async def go():
        items = [bot.Item(f"https://y/{i}", "T", f"youtube:load{i}") for i in range(7)]
        await asyncio.gather(*[bot.run_item(_batch(uid=i), it) for i, it in enumerate(items)])
        return items
    items = run(go())
    assert all(i.status == "done" for i in items) and peak[0] == 2


def test_cancel_while_queued_skips_download(monkeypatch):
    sent, order = _wire_paths(monkeypatch, "disk")
    monkeypatch.setattr(bot, "DL_SEM", bot.Gate(1))
    def slow_dl(it, mode, outdir, hook=None):
        time.sleep(0.15); order.append("dl")
        p = os.path.join(outdir, "v.mp4"); open(p, "wb").write(b"x" * 10); return p, {"title": "T"}, mode
    monkeypatch.setattr(bot, "do_download_fit", slow_dl)
    monkeypatch.setattr(bot, "MAX_PER_USER", 0)
    async def go():
        b1, b2 = _batch(1), _batch(2)
        i1, i2 = bot.Item("https://y/q1", "T", "youtube:q1"), bot.Item("https://y/q2", "T", "youtube:q2")
        t1 = asyncio.create_task(bot.run_item(b1, i1)); await asyncio.sleep(0.03)
        t2 = asyncio.create_task(bot.run_item(b2, i2)); await asyncio.sleep(0.03)
        assert i2.status == "wait"                              # واقف في الطابور
        b2.cancelled = True
        await asyncio.gather(t1, t2)
        return i1, i2
    i1, i2 = run(go())
    assert i1.status == "done" and i2.status == "err" and order == ["dl"]   # التاني اتلغى قبل ما يبدأ تنزيل
