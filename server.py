#!/usr/bin/env python3
"""
Davomat dashboard — Hikvision Face Recognition terminallari (ISAPI) uchun.
Bir nechta terminal (masalan SKLAD, OFIS), xodimlar va terminal ID larini xodimga bog'lash.

Ishga tushirish:   python server.py          (haqiqiy terminallar bilan)
                   python server.py --demo   (terminalsiz, sinov ma'lumotlari bilan)
Qo'shimcha:        --no-browser   --port=8090

Faqat Python standart kutubxonasi ishlatiladi — hech narsa o'rnatish shart emas.
"""
import base64
import calendar
import csv
import hashlib
import hmac
import html
import html.parser
import http.client
import io
import queue
import json
import os
import random
import re
import secrets
import select
import socket
import sqlite3
import sys
import tempfile
import threading
import time
import uuid
import webbrowser
from datetime import datetime, timedelta
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlsplit

BASE = os.path.dirname(os.path.abspath(__file__))
# Bulut (Railway va h.k.): PORT beriladi, ma'lumotlar doimiy diskka (DATA_DIR, masalan /data volume) yoziladi
CLOUD = bool(os.environ.get("PORT"))
DATA = os.environ.get("DATA_DIR") or os.path.join(BASE, "data")
PHOTOS = os.path.join(DATA, "photos")
FACES = os.path.join(DATA, "faces")
WEB = os.path.join(BASE, "web")
CONFIG_PATH = os.path.join(DATA, "config.json") if os.environ.get("DATA_DIR") else os.path.join(BASE, "config.json")

DEFAULTS = {
    "listen_host": "127.0.0.1",
    "listen_port": 8080,
    "poll_seconds": 2,
    "work_start": "09:00",
    "repeat_gap_seconds": 60,
    "backfill_days": 31,
}

DEMO = "--demo" in sys.argv
IN_ST = ("checkIn", "breakIn", "overtimeIn")
OUT_ST = ("checkOut", "breakOut", "overtimeOut")
TSTATE = {}     # terminal_id -> holat
POLLERS = {}    # terminal_id -> Poller
LOGIN_LOCK = threading.Lock()
TERM_LOCK = threading.Lock()


# ----------------------------------------------------------------- config / vaqt
def load_config():
    cfg = dict(DEFAULTS)
    if os.path.exists(CONFIG_PATH):
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg.update(json.load(f))
    else:
        save_config(cfg)
    return cfg


def save_config(cfg):
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)


def now_local():
    return datetime.now().astimezone()


def parse_time(s):
    dt = datetime.fromisoformat(s)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=now_local().tzinfo)
    return dt


def fmt_time(dt):
    z = dt.strftime("%z")
    return dt.strftime("%Y-%m-%dT%H:%M:%S") + (z[:3] + ":" + z[3:] if z else "")


# ----------------------------------------------------------------- terminal (ISAPI + Digest auth)
class AuthError(Exception):
    pass


class Device:
    def __init__(self, host, port, user, password, timeout=10):
        self.host, self.port, self.user, self.password = host, int(port or 80), user, password
        self.timeout = timeout
        self.chal = None
        self.nc = 0
        self.lock = threading.Lock()
        self.disabled = False

    @staticmethod
    def _md5(s):
        return hashlib.md5(s.encode("utf-8")).hexdigest()

    def _auth(self, method, uri):
        c = self.chal
        self.nc += 1
        nc = f"{self.nc:08x}"
        cnonce = os.urandom(8).hex()
        ha1 = self._md5(f"{self.user}:{c['realm']}:{self.password}")
        ha2 = self._md5(f"{method}:{uri}")
        if "qop" in c:
            resp = self._md5(f"{ha1}:{c['nonce']}:{nc}:{cnonce}:auth:{ha2}")
            extra = f', qop=auth, nc={nc}, cnonce="{cnonce}"'
        else:
            resp = self._md5(f"{ha1}:{c['nonce']}:{ha2}")
            extra = ""
        h = (f'Digest username="{self.user}", realm="{c["realm"]}", nonce="{c["nonce"]}", '
             f'uri="{uri}", algorithm=MD5, response="{resp}"{extra}')
        if c.get("opaque"):
            h += f', opaque="{c["opaque"]}"'
        return h

    def request(self, method, path, body=None, ctype="application/json", fatal=True):
        if self.disabled:
            raise AuthError("Login yoki parol noto'g'ri")
        with self.lock:
            # Terminal bitta nonce'ni bir necha marta qabul qiladi, keyin sarlavhasiz 401 qaytaradi.
            # Shunda yangi nonce olib qayta urinamiz. Faqat YANGI nonce bilan ham 401 bo'lsa — parol xato.
            for attempt in range(3):
                conn = http.client.HTTPConnection(self.host, self.port, timeout=self.timeout)
                headers = {}
                if body is not None:
                    headers["Content-Type"] = ctype
                fresh = bool(self.chal) and self.nc == 0
                if self.chal:
                    headers["Authorization"] = self._auth(method, path)
                try:
                    conn.request(method, path, body=body, headers=headers)
                    r = conn.getresponse()
                    data = r.read()
                finally:
                    conn.close()
                if r.status == 401:
                    wa = r.getheader("WWW-Authenticate") or ""
                    chal = {k: (v1 or v2) for k, v1, v2 in re.findall(r'(\w+)=(?:"([^"]*)"|([^,\s]*))', wa)}
                    self.chal = chal if "nonce" in chal else None
                    self.nc = 0
                    if not fresh and attempt < 2:
                        continue
                    print(f"[401] {self.host} {method} {path}", flush=True)
                    if fatal:
                        self.disabled = True  # terminal akkauntni bloklamasligi uchun to'xtaymiz
                    raise AuthError("Login yoki parol noto'g'ri")
                return r.status, r.getheader("Content-Type") or "", data

    def post_json(self, path, obj, fatal=True):
        st, _, data = self.request("POST", path, json.dumps(obj).encode("utf-8"), fatal=fatal)
        return st, json.loads(data.decode("utf-8", "replace") or "{}")

    def info(self):
        st, _, data = self.request("GET", "/ISAPI/System/deviceInfo")
        if st != 200:
            raise RuntimeError(f"HTTP {st}")
        x = data.decode("utf-8", "replace")
        g = lambda tag: (re.search(f"<{tag}>(.*?)</{tag}>", x) or [None, ""])[1]
        return {"name": g("deviceName"), "model": g("model"), "serial": g("serialNumber"),
                "firmware": g("firmwareVersion"), "mac": g("macAddress")}


# ----------------------------------------------------------------- baza
class DB:
    def __init__(self, path):
        self.conn = sqlite3.connect(path, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self.lock = threading.Lock()
        with self.lock:
            c = self.conn
            cols = [r[1] for r in c.execute("PRAGMA table_info(events)").fetchall()]
            legacy = bool(cols) and "terminal_id" not in cols
            if legacy:
                c.execute("ALTER TABLE events RENAME TO events_old")
                c.execute("DROP INDEX IF EXISTS ev_date")
            c.executescript("""
            CREATE TABLE IF NOT EXISTS terminals(
                id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, host TEXT, port INTEGER,
                username TEXT, password TEXT, created TEXT);
            CREATE TABLE IF NOT EXISTS events(
                id INTEGER PRIMARY KEY AUTOINCREMENT, terminal_id INTEGER, serial INTEGER,
                time TEXT, date TEXT, emp TEXT, name TEXT, att_status TEXT, verify TEXT, picture_url TEXT,
                UNIQUE(terminal_id, serial));
            CREATE INDEX IF NOT EXISTS ev_date2 ON events(date, time);
            CREATE TABLE IF NOT EXISTS term_users(terminal_id INTEGER, emp TEXT, name TEXT,
                PRIMARY KEY(terminal_id, emp));
            CREATE TABLE IF NOT EXISTS staff(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, code TEXT,
                dept TEXT, created TEXT);
            CREATE TABLE IF NOT EXISTS links(terminal_id INTEGER, emp TEXT, staff_id INTEGER,
                PRIMARY KEY(terminal_id, emp));
            CREATE TABLE IF NOT EXISTS accounts(username TEXT PRIMARY KEY, salt TEXT, hash TEXT, created TEXT);
            CREATE TABLE IF NOT EXISTS sessions(token TEXT PRIMARY KEY, username TEXT, expires REAL);
            CREATE TABLE IF NOT EXISTS billz_days(date TEXT PRIMARY KEY, data TEXT, fetched REAL, final INTEGER);
            CREATE TABLE IF NOT EXISTS jobs(id INTEGER PRIMARY KEY AUTOINCREMENT, kind TEXT, terminal_id INTEGER,
                payload TEXT, status TEXT, result TEXT, created REAL, taken REAL);
            CREATE TABLE IF NOT EXISTS term_groups(terminal_id INTEGER, group_id INTEGER, name TEXT,
                PRIMARY KEY(terminal_id, group_id));
            CREATE TABLE IF NOT EXISTS expenses(id INTEGER PRIMARY KEY, date TEXT, fund TEXT, article TEXT,
                cashbox TEXT, amount REAL, currency TEXT, comment TEXT, created TEXT, author TEXT, fetched REAL);
            CREATE INDEX IF NOT EXISTS exp_date ON expenses(date);
            """)
            tcols = [r[1] for r in c.execute("PRAGMA table_info(terminals)")]
            if "active" not in tcols:
                # o'chirib qo'yilgan terminal: tarixi qoladi, lekin server unga ulanmaydi
                c.execute("ALTER TABLE terminals ADD COLUMN active INTEGER NOT NULL DEFAULT 1")
            if "dept_id" not in [r[1] for r in c.execute("PRAGMA table_info(term_users)")]:
                c.execute("ALTER TABLE term_users ADD COLUMN dept_id INTEGER")  # terminaldagi departament
            for col in ("mac", "serial"):  # IP o'zgarsa terminalni tarmoqdan shu bo'yicha topamiz
                if col not in tcols:
                    c.execute(f"ALTER TABLE terminals ADD COLUMN {col} TEXT")
            if legacy:
                # eski (bitta terminalli) bazani ko'chirish: hamma eski o'tishlar 1-terminalga tegishli
                c.execute("INSERT INTO events(id, terminal_id, serial, time, date, emp, name, att_status, verify, "
                          "picture_url) SELECT id, 1, serial, time, date, emp, name, att_status, verify, picture_url "
                          "FROM events_old")
                c.execute("DROP TABLE events_old")
                if c.execute("SELECT name FROM sqlite_master WHERE name='users'").fetchone():
                    c.execute("INSERT OR IGNORE INTO term_users(terminal_id, emp, name) SELECT 1, emp, name FROM users")
                    c.execute("DROP TABLE users")
                for f in os.listdir(PHOTOS):
                    if re.fullmatch(r"\d+\.jpg", f):
                        os.replace(os.path.join(PHOTOS, f), os.path.join(PHOTOS, "1_" + f))
                for f in os.listdir(FACES):
                    os.remove(os.path.join(FACES, f))
                print("Baza yangi formatga ko'chirildi (eski o'tishlar 1-terminalga biriktirildi).")
            c.commit()

    def q(self, sql, args=()):
        with self.lock:
            return [dict(r) for r in self.conn.execute(sql, args).fetchall()]

    def x(self, sql, args=()):
        with self.lock:
            cur = self.conn.execute(sql, args)
            self.conn.commit()
            return cur.lastrowid


db = None
CFG = None


def terminals(with_password=False):
    cols = "id, name, host, port, username, created, active" + (", password" if with_password else "")
    return db.q(f"SELECT {cols} FROM terminals ORDER BY id")


def term_names():
    return {t["id"]: t["name"] for t in db.q("SELECT id, name FROM terminals")}


def upsert_term_user(tid, emp, name, dept_id=None):
    db.x("INSERT INTO term_users(terminal_id, emp, name) VALUES(?,?,?) ON CONFLICT(terminal_id, emp) DO UPDATE "
         "SET name=CASE WHEN excluded.name!='' THEN excluded.name ELSE term_users.name END", (tid, emp, name or ""))
    if dept_id is not None:
        db.x("UPDATE term_users SET dept_id=? WHERE terminal_id=? AND emp=?", (int(dept_id or 0), tid, emp))


def store_term_groups(tid, groups):
    """Terminal departamentlari ro'yxatini bazada yangilash: [[id, nom], ...]"""
    clean = []
    for g in groups or []:
        try:
            gid, name = int(g[0]), str(g[1] or "").strip()[:32]
        except (IndexError, TypeError, ValueError):
            continue
        if gid > 0 and name:
            clean.append((tid, gid, name))
    if not clean:
        return
    with db.lock:
        db.conn.execute("DELETE FROM term_groups WHERE terminal_id=?", (tid,))
        db.conn.executemany("INSERT OR REPLACE INTO term_groups(terminal_id, group_id, name) VALUES(?,?,?)", clean)
        db.conn.commit()


def term_groups(tid):
    return [[r["group_id"], r["name"]] for r in
            db.q("SELECT group_id, name FROM term_groups WHERE terminal_id=? ORDER BY group_id", (tid,))]


def fetch_term_groups(dev):
    """Terminaldagi departamentlar (Hikvision: LocalAttendance group). Topilmasa — None."""
    out, pos, sid = [], 0, uuid.uuid4().hex[:16]
    for _ in range(20):
        st, j = dev.post_json("/ISAPI/AccessControl/LocalAttendance/groupSearch?format=json",
                              {"GroupSearchCond": {"searchID": sid, "searchResultPosition": pos, "maxResults": 15,
                                                   "searchType": "all"}}, fatal=False)
        if st != 200 or not isinstance(j, dict):
            return out or None
        r = j.get("GroupSearchResult") or {}
        lst = r.get("GroupInfo") or []
        out += [[g.get("groupId"), g.get("groupName", "")] for g in lst if g.get("groupId")]
        pos += len(lst)
        if not lst or pos >= int(r.get("totalMatches") or 0):
            break
    return out


def add_event(tid, ev):
    emp = str(ev.get("employeeNoString") or ev.get("employeeNo") or "").strip()
    t = ev.get("time")
    if not emp or not t:
        return None
    serial = ev.get("serialNo")
    if serial is None:
        serial = int(hashlib.md5(f"{t}|{emp}".encode()).hexdigest()[:12], 16)
    if db.q("SELECT 1 FROM events WHERE terminal_id=? AND serial=?", (tid, serial)):
        return None
    name = (ev.get("name") or "").strip()
    upsert_term_user(tid, emp, name)
    return db.x("INSERT OR IGNORE INTO events(terminal_id, serial, time, date, emp, name, att_status, verify, "
                "picture_url) VALUES(?,?,?,?,?,?,?,?,?)",
                (tid, serial, t, t[:10], emp, name, ev.get("attendanceStatus") or "",
                 ev.get("currentVerifyMode") or "", ev.get("pictureURL") or ""))


# ----------------------------------------------------------------- terminal kuzatuvchisi
class Poller(threading.Thread):
    daemon = True

    def __init__(self, t):
        super().__init__()
        self.tid = t["id"]
        self.device = Device(t["host"], t["port"], t["username"], t["password"])
        self.combos = [(5, 0)]
        self.users_at = 0
        self.stopped = False
        self.primed = False   # birinchi so'rov — eski o'tishlarni yuklash (Telegram'ga yuborilmaydi)
        self.fails = 0
        self.searched_at = 0
        self.state = TSTATE.setdefault(self.tid, {})
        self.state.update(connected=False, error=None, need_login=False, last_poll=None)

    def search(self, start, end):
        out = []
        for major, minor in self.combos:
            pos = 0
            sid = uuid.uuid4().hex[:16]
            while True:
                body = {"AcsEventCond": {"searchID": sid, "searchResultPosition": pos, "maxResults": 30,
                                         "major": major, "minor": minor,
                                         "startTime": fmt_time(start), "endTime": fmt_time(end)}}
                st, j = self.device.post_json("/ISAPI/AccessControl/AcsEvent?format=json", body)
                if st != 200:
                    if self.combos == [(5, 0)]:
                        self.combos = [(5, 75), (5, 1), (5, 38)]  # ba'zi proshivkalar minor=0 ni qabul qilmaydi
                        return self.search(start, end)
                    raise RuntimeError(f"AcsEvent HTTP {st}")
                a = j.get("AcsEvent", {})
                info = a.get("InfoList") or []
                out += info
                pos += len(info)
                if a.get("responseStatusStrg") != "MORE" or not info:
                    break
        return out

    def sync_users(self):
        pos = 0
        sid = uuid.uuid4().hex[:16]
        seen = []
        while True:
            st, j = self.device.post_json("/ISAPI/AccessControl/UserInfo/Search?format=json",
                                          {"UserInfoSearchCond": {"searchID": sid, "searchResultPosition": pos,
                                                                  "maxResults": 30}})
            if st != 200:
                return
            s = j.get("UserInfoSearch", {})
            lst = s.get("UserInfo") or []
            for u in lst:
                emp = str(u.get("employeeNo", "")).strip()
                if emp:
                    gid = int(u.get("groupId") or 0)
                    upsert_term_user(self.tid, emp, u.get("name", ""), gid)
                    seen.append([emp, u.get("name", ""), gid])
            pos += len(lst)
            if s.get("responseStatusStrg") != "MORE" or not lst:
                break
        self.users_at = time.time()
        try:
            store_term_groups(self.tid, fetch_term_groups(self.device))
        except Exception:
            pass
        if seen and CFG.get("cloud_url") and not CLOUD:
            threading.Thread(target=send_users_to_cloud, args=(self.tid, seen, term_groups(self.tid)),
                             daemon=True).start()

    def poll_once(self):
        if not self.state.get("device"):
            self.state["device"] = self.device.info()
            remember_identity(self.tid, self.state["device"])
        # bulut ishlatilsa — terminalga yangi qo'shilgan odamlar serverda tezroq ko'rinsin
        if time.time() - self.users_at > (90 if CFG.get("cloud_url") else 600):
            self.sync_users()
        last = db.q("SELECT MAX(time) t FROM events WHERE terminal_id=?", (self.tid,))[0]["t"]
        now = now_local()
        start = parse_time(last) if last else \
            (now - timedelta(days=CFG.get("backfill_days", 31))).replace(hour=0, minute=0, second=0)
        evs = self.search(start, now + timedelta(days=1))
        evs.sort(key=lambda e: (e.get("time", ""), e.get("serialNo") or 0))
        new_ids = [i for i in (add_event(self.tid, e) for e in evs if not self.stopped) if i]
        if len(new_ids) <= 5:
            for i in new_ids:
                try:
                    get_photo(i)
                except Exception:
                    pass
        if self.primed:
            tg_notify(new_ids)
        self.primed = True

    def moved(self):
        """Terminal javob bermasa — IP o'zgargan bo'lishi mumkin: tarmoqdan MAC/seriya bo'yicha qidiramiz."""
        if time.time() - self.searched_at < 60:
            return False
        self.searched_at = time.time()
        new = relocate_terminal(self.tid)
        if not new:
            return False
        d = self.device
        self.device = Device(new[0], new[1], d.user, d.password)
        self.state["device"] = None
        self.fails = 0
        return True

    def run(self):
        while not self.stopped:
            try:
                self.poll_once()
                self.fails = 0
                self.state.update(connected=True, error=None, need_login=False, last_poll=fmt_time(now_local()))
            except AuthError as e:
                # IP boshqa qurilmaga o'tib qolgan bo'lishi mumkin — avval terminalimizni qidirib ko'ramiz
                if self.moved():
                    continue
                self.state.update(connected=False, need_login=True,
                                  error=f"{e}. Sozlamalar → Terminallar bo'limida login/parolni yangilang.")
                return
            except Exception as e:
                self.fails += 1
                if self.fails >= 3 and self.moved():
                    continue
                self.state.update(connected=False, error=f"Terminalga ulanib bo'lmadi: {e}")
                time.sleep(5)
            time.sleep(CFG.get("poll_seconds", 2))


def start_poller(t):
    stop_poller(t["id"])
    if not t.get("active", 1):
        return
    if CLOUD and not DEMO:
        # Bulutdan ofis tarmog'idagi terminalga ulanib bo'lmaydi — terminal o'zi hodisa yuboradi (/hook/...)
        TSTATE[t["id"]] = {"connected": False, "need_login": False, "last_poll": None, "device": None, "push": True,
                           "error": "Terminaldan hali signal kelmadi (terminal internetga ulanganini tekshiring)"}
        return
    if DEMO:
        TSTATE[t["id"]] = {"connected": True, "error": None, "need_login": False,
                           "last_poll": fmt_time(now_local()), "device": {"model": "DS-K1T343MFWX (demo)"}}
        return
    if not t.get("password"):
        TSTATE[t["id"]] = {"connected": False, "need_login": True, "last_poll": None, "device": None,
                           "error": "Parol kiritilmagan. Sozlamalar → Terminallar bo'limida kiriting."}
        return
    p = Poller(t)
    POLLERS[t["id"]] = p
    p.start()


def stop_poller(tid):
    p = POLLERS.pop(tid, None)
    if p:
        p.stopped = True
    TSTATE.pop(tid, None)


def device_of(tid):
    p = POLLERS.get(tid)
    # ulanmagan terminaldan rasm so'rab sahifani kuttirmaymiz
    return p.device if p and TSTATE.get(tid, {}).get("connected") else None


# ----------------------------------------------------------------- shaxs aniqlash (terminal ID -> xodim)
def make_ctx():
    return {
        "staff": {s["id"]: s for s in db.q("SELECT id, name, code, dept FROM staff")},
        "links": {(l["terminal_id"], l["emp"]): l["staff_id"] for l in db.q("SELECT * FROM links")},
        "tusers": {(u["terminal_id"], u["emp"]): u["name"] for u in db.q("SELECT * FROM term_users")},
        "tnames": term_names(),
        "tdept": {(r["terminal_id"], r["emp"]): r["name"] for r in db.q(
            "SELECT u.terminal_id, u.emp, g.name FROM term_users u JOIN term_groups g "
            "ON g.terminal_id = u.terminal_id AND g.group_id = u.dept_id")},
    }


def dept_of(sid, ctx):
    """Xodim departamenti: terminaldagisi (bir nechta bo'lsa — birinchisi), bo'lmasa dashboarddagi bo'limi."""
    if "sdept" not in ctx:
        sd = {}
        for k in sorted(ctx["links"]):
            v = ctx["links"][k]
            if v not in sd and ctx["tdept"].get(k):
                sd[v] = ctx["tdept"][k]
        ctx["sdept"] = sd
    s = ctx["staff"].get(sid) or {}
    return ctx["sdept"].get(sid) or s.get("dept") or ""


def person_of(tid, emp, ctx, ev_name=""):
    sid = ctx["links"].get((tid, emp))
    s = ctx["staff"].get(sid)
    if s:
        return {"key": f"s{sid}", "name": s["name"], "code": s["code"] or "", "dept": dept_of(sid, ctx), "linked": True}
    return {"key": f"t{tid}-{emp}", "name": ctx["tusers"].get((tid, emp)) or ev_name or "",
            "code": f"{ctx['tnames'].get(tid, '?')} · ID {emp}", "dept": ctx["tdept"].get((tid, emp), ""),
            "linked": False}


def key_pairs(key, ctx):
    """Shaxs kaliti -> [(terminal_id, emp), ...]"""
    if key.startswith("s"):
        sid = int(key[1:])
        return [k for k, v in ctx["links"].items() if v == sid]
    m = re.fullmatch(r"t(\d+)-(.+)", key)
    return [(int(m.group(1)), m.group(2))] if m else []


def classify(evs):
    """Bir kishining bir kundagi o'tishlari (vaqt bo'yicha) -> keldi/ketdi/takror."""
    gap = CFG.get("repeat_gap_seconds", 60)
    prev_t, last_real = None, None
    for e in evs:
        t = parse_time(e["time"])
        if prev_t is not None and (t - prev_t).total_seconds() < gap:
            k = "repeat"
        elif e["att_status"] in IN_ST:
            k = "in"
        elif e["att_status"] in OUT_ST:
            k = "out"
        else:
            k = "out" if last_real == "in" else "in"
        if k != "repeat":
            last_real = k
        prev_t = t
        e["kind"] = k


def day_groups(d, ctx, tid=None):
    sql = "SELECT id, terminal_id, time, emp, name, att_status FROM events WHERE date=?"
    args = [d]
    if tid:
        sql += " AND terminal_id=?"
        args.append(tid)
    groups = {}
    for e in db.q(sql + " ORDER BY time, id", args):
        p = person_of(e["terminal_id"], e["emp"], ctx, e["name"])
        g = groups.setdefault(p["key"], {"p": p, "evs": []})
        e["terminal"] = ctx["tnames"].get(e["terminal_id"], "—")
        g["evs"].append(e)
    for g in groups.values():
        classify(g["evs"])
    return groups


def roster(ctx, tid=None):
    """Kutilayotgan odamlar: ro'yxatdagi xodimlar + hali bog'lanmagan terminal foydalanuvchilari."""
    out = {}
    for sid, s in ctx["staff"].items():
        if tid and not any(v == sid and k[0] == tid for k, v in ctx["links"].items()):
            continue
        out[f"s{sid}"] = {"key": f"s{sid}", "name": s["name"], "code": s["code"] or "", "dept": s["dept"] or "",
                          "linked": True}
    for (t, emp), name in ctx["tusers"].items():
        if (t, emp) in ctx["links"] and ctx["links"][(t, emp)] in ctx["staff"]:
            continue
        if tid and t != tid:
            continue
        if t not in ctx["tnames"]:
            continue
        p = person_of(t, emp, ctx)
        out[p["key"]] = p
    return out


def unlinked_count(ctx):
    return sum(1 for (t, emp) in ctx["tusers"] if t in ctx["tnames"]
               and ctx["links"].get((t, emp)) not in ctx["staff"])


# ----------------------------------------------------------------- hisobotlar
def day_summary(d, tid=None, ctx=None):
    ctx = ctx or make_ctx()
    groups = day_groups(d, ctx, tid)
    now = now_local()
    is_today = d == now.strftime("%Y-%m-%d")
    ws = CFG.get("work_start", "09:00")
    wh, wm = map(int, ws.split(":"))
    rows = []
    for key, g in groups.items():
        lst = g["evs"]
        real = [e for e in lst if e["kind"] != "repeat"]
        ins = [e for e in real if e["kind"] == "in"]
        outs = [e for e in real if e["kind"] == "out"]
        worked, cur = 0.0, None
        for e in real:
            if e["kind"] == "in" and cur is None:
                cur = parse_time(e["time"])
            elif e["kind"] == "out" and cur is not None:
                worked += (parse_time(e["time"]) - cur).total_seconds()
                cur = None
        inside = bool(real) and real[-1]["kind"] == "in"
        if cur is not None and is_today:
            worked += max(0, (now - cur).total_seconds())
        first = ins[0] if ins else (real[0] if real else lst[0])
        last_out = outs[-1] if outs else None
        hh, mm = map(int, first["time"][11:16].split(":"))
        late = max(0, hh * 60 + mm - (wh * 60 + wm))
        p = g["p"]
        rows.append({**p, "first_in": first["time"], "first_id": first["id"], "first_term": first["terminal"],
                     "last_out": last_out["time"] if last_out else None,
                     "last_out_term": last_out["terminal"] if last_out else None,
                     "inside": inside and is_today, "worked_min": int(worked // 60), "late_min": late,
                     "count": len(lst), "terminals": sorted({e["terminal"] for e in lst})})
    rows.sort(key=lambda r: r["first_in"])
    present = {r["key"] for r in rows}
    ros = roster(ctx, tid)
    absent = sorted([p for k, p in ros.items() if k not in present],
                    key=lambda p: (not p["linked"], (p["name"] or "").lower(), p["key"]))
    return {"date": d, "work_start": ws, "rows": rows, "absent": absent,
            "stats": {"total": len(present | set(ros)), "came": len(rows),
                      "inside": sum(r["inside"] for r in rows),
                      "late": sum(1 for r in rows if r["late_min"] > 0), "absent": len(absent)}}


def month_summary(m, tid=None):
    y, mo = map(int, m.split("-"))
    ndays = calendar.monthrange(y, mo)[1]
    today = now_local().strftime("%Y-%m-%d")
    ctx = make_ctx()
    people = {}
    for d in range(1, ndays + 1):
        ds = f"{y:04d}-{mo:02d}-{d:02d}"
        if ds > today:
            break
        for r in day_summary(ds, tid, ctx)["rows"]:
            p = people.setdefault(r["key"], {k: r[k] for k in ("key", "name", "code", "dept", "linked")} | {"days": {}})
            p["days"][str(d)] = {"w": r["worked_min"], "late": r["late_min"], "in": r["first_in"][11:16],
                                 "out": r["last_out"][11:16] if r["last_out"] else None,
                                 "terms": r["terminals"]}
    for k, p in roster(ctx, tid).items():
        people.setdefault(k, {**p, "days": {}})
    rows = sorted(people.values(), key=lambda p: (not p["linked"], (p["name"] or "").lower(), p["key"]))
    for p in rows:
        p["total_days"] = len(p["days"])
        p["total_min"] = sum(v["w"] for v in p["days"].values())
        p["late_days"] = sum(1 for v in p["days"].values() if v["late"] > 0)
    return {"month": m, "days": ndays, "today": today, "work_start": CFG.get("work_start"), "rows": rows}


def export_csv(d1, d2, tid=None):
    out = io.StringIO()
    out.write("﻿")  # Excel UTF-8 ni to'g'ri o'qishi uchun
    w = csv.writer(out, delimiter=";")
    w.writerow(["Sana", "Xodim", "Tabel / ID", "Departament", "Keldi", "Keldi (terminal)", "Ketdi", "Ketdi (terminal)",
                "Ishlagan (soat)", "Kechikish (daq)", "Terminallar"])
    dt = datetime.strptime(d1, "%Y-%m-%d")
    end = datetime.strptime(d2, "%Y-%m-%d")
    ctx = make_ctx()
    while dt <= end:
        s = day_summary(dt.strftime("%Y-%m-%d"), tid, ctx)
        for r in s["rows"]:
            w.writerow([s["date"], r["name"], r["code"], r["dept"], r["first_in"][11:16], r["first_term"],
                        r["last_out"][11:16] if r["last_out"] else "", r["last_out_term"] or "",
                        f"{r['worked_min'] // 60}:{r['worked_min'] % 60:02d}", r["late_min"], ", ".join(r["terminals"])])
        dt += timedelta(days=1)
    return out.getvalue().encode("utf-8")


def feed(after):
    if after <= 0:
        evs = db.q("SELECT id, terminal_id, time, date, emp, name FROM events ORDER BY time DESC, id DESC LIMIT 40")
    else:
        evs = db.q("SELECT id, terminal_id, time, date, emp, name FROM events WHERE id>? ORDER BY id LIMIT 50",
                   (after,))
    ctx = make_ctx()
    kinds = {}
    for d in {e["date"] for e in evs}:
        for g in day_groups(d, ctx).values():
            for e in g["evs"]:
                kinds[e["id"]] = e["kind"]
    out = []
    for e in evs:
        p = person_of(e["terminal_id"], e["emp"], ctx, e["name"])
        out.append({"id": e["id"], "time": e["time"], "kind": kinds.get(e["id"], "in"), **p,
                    "terminal": ctx["tnames"].get(e["terminal_id"], "—")})
    mx = db.q("SELECT COALESCE(MAX(id),0) m FROM events")[0]["m"]
    return {"events": out, "max_id": mx}


# ----------------------------------------------------------------- rasmlar
def demo_avatar(seed, label):
    hue = int(hashlib.md5(seed.encode()).hexdigest()[:2], 16) * 360 // 256
    initials = "".join(w[0] for w in (label or "?").split()[:2]).upper() or "?"
    return f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 300 400">
<rect width="300" height="400" fill="hsl({hue},45%,38%)"/>
<circle cx="150" cy="150" r="70" fill="hsl({hue},40%,70%)"/>
<rect x="60" y="240" width="180" height="200" rx="90" fill="hsl({hue},40%,70%)"/>
<text x="150" y="172" font-family="Arial" font-size="60" font-weight="700" text-anchor="middle" fill="hsl({hue},45%,25%)">{initials}</text>
</svg>""".encode()


def _download(dev, url_or_path):
    if not dev:
        return None
    u = urlsplit(url_or_path)
    path = (u.path or "/") + ("?" + u.query if u.query else "")
    try:
        st, ct, data = dev.request("GET", path, fatal=False)
    except Exception:
        return None
    if st == 200 and (data[:2] == b"\xff\xd8" or "image" in ct):
        return data
    return None


def get_photo(event_id):
    r = db.q("SELECT terminal_id, serial, emp, name, picture_url FROM events WHERE id=?", (event_id,))
    if not r:
        return None
    r = r[0]
    if DEMO:
        p = person_of(r["terminal_id"], r["emp"], make_ctx(), r["name"])
        return demo_avatar(p["key"], p["name"]), "image/svg+xml"
    fp = os.path.join(PHOTOS, f"{r['terminal_id']}_{r['serial']}.jpg")
    if os.path.exists(fp):
        with open(fp, "rb") as f:
            return f.read(), "image/jpeg"
    if not r["picture_url"]:
        return None
    data = _download(device_of(r["terminal_id"]), r["picture_url"])
    if data:
        with open(fp, "wb") as f:
            f.write(data)
        return data, "image/jpeg"
    return None


def _face_of(tid, emp):
    safe = re.sub(r"[^\w-]", "_", emp)
    fp = os.path.join(FACES, f"{tid}_{safe}.jpg")
    if os.path.exists(fp):
        with open(fp, "rb") as f:
            return f.read()
    miss = fp + ".none"
    if os.path.exists(miss) and time.time() - os.path.getmtime(miss) < 3600:
        return None
    dev = device_of(tid)
    if not dev:
        return None
    data = None
    try:
        st, j = dev.post_json("/ISAPI/Intelligent/FDLib/FDSearch?format=json",
                              {"searchResultPosition": 0, "maxResults": 1, "faceLibType": "blackFD",
                               "FDID": "1", "FPID": emp}, fatal=False)
        url = ((j.get("MatchList") or [{}])[0]).get("faceURL") if st == 200 else None
        data = _download(dev, url) if url else None
    except Exception:
        data = None
    if data:
        with open(fp, "wb") as f:
            f.write(data)
        return data
    open(miss, "w").close()
    return None


def get_face(key):
    ctx = make_ctx()
    pairs = key_pairs(key, ctx)
    if DEMO:
        name = ctx["staff"][int(key[1:])]["name"] if key.startswith("s") and int(key[1:]) in ctx["staff"] else \
            (ctx["tusers"].get(pairs[0]) if pairs else "?")
        return demo_avatar(key, name), "image/svg+xml"
    for tid, emp in pairs:
        data = _face_of(tid, emp)
        if data:
            return data, "image/jpeg"
    return None


# ----------------------------------------------------------------- demo
DEMO_PEOPLE = ["Aziz Karimov", "Dilnoza Rahimova", "Jasur Toshmatov", "Malika Yusupova", "Sardor Aliyev",
               "Nodira Ismoilova", "Bekzod Ergashev", "Gulnora Saidova"]


def demo_setup():
    if db.q("SELECT 1 FROM terminals"):
        for t in terminals():
            start_poller(t)
        return
    now = fmt_time(now_local())
    db.x("INSERT INTO terminals(id, name, host, port, username, password, created) VALUES(1,'SKLAD','demo-sklad',80,'admin','x',?)", (now,))
    db.x("INSERT INTO terminals(id, name, host, port, username, password, created) VALUES(2,'OFIS','demo-ofis',80,'admin','x',?)", (now,))
    for i, n in enumerate(DEMO_PEOPLE):
        upsert_term_user(1, str(i + 1), n)
    for i, n in enumerate(DEMO_PEOPLE[:5]):
        upsert_term_user(2, str(101 + i), n)
    depts = ["Moliya", "Savdo", "IT", "Moliya", "Sklad"]
    for i, n in enumerate(DEMO_PEOPLE[:5]):
        sid = db.x("INSERT INTO staff(name, code, dept, created) VALUES(?,?,?,?)", (n, f"W{i + 1:03d}", depts[i], now))
        db.x("INSERT INTO links VALUES(1, ?, ?)", (str(i + 1), sid))
        db.x("INSERT INTO links VALUES(2, ?, ?)", (str(101 + i), sid))
    base = now_local().replace(hour=8, minute=30, second=0, microsecond=0)
    serial = 1000
    for i, n in enumerate(DEMO_PEOPLE[:7]):
        tid, emp = (2, str(101 + i)) if i < 3 else (1, str(i + 1))
        t = base + timedelta(minutes=random.randint(0, 55), seconds=random.randint(0, 59))
        if t < now_local():
            serial += 1
            add_event(tid, {"employeeNoString": emp, "name": n, "time": fmt_time(t), "serialNo": serial})
    for i in (0, 3):
        t = base.replace(hour=13) + timedelta(minutes=random.randint(0, 30))
        if t < now_local():
            serial += 1
            add_event(1, {"employeeNoString": str(i + 1), "name": DEMO_PEOPLE[i], "time": fmt_time(t), "serialNo": serial})
    for t in terminals():
        start_poller(t)


class DemoGen(threading.Thread):
    daemon = True

    def run(self):
        serial = int(time.time())
        while True:
            time.sleep(random.randint(6, 12))
            ts = [t for t in terminals() if t["active"]]
            if not ts:
                continue
            tid = random.choice(ts)["id"]
            us = db.q("SELECT emp, name FROM term_users WHERE terminal_id=?", (tid,))
            if not us:
                continue
            u = random.choice(us)
            serial += 1
            eid = add_event(tid, {"employeeNoString": u["emp"], "name": u["name"], "time": fmt_time(now_local()),
                                  "serialNo": serial})
            if eid:
                tg_notify([eid])
            if tid in TSTATE:
                TSTATE[tid]["last_poll"] = fmt_time(now_local())


# ----------------------------------------------------------------- Telegram xabarnomalari
TG_HOST = "api.telegram.org"
TG_Q = queue.Queue()
TG_STATE = {"sent": 0, "last_ok": None, "last_error": None}
TOKEN_RE = re.compile(r"^\d{5,15}:[\w-]{30,60}$")
CHAT_RE = re.compile(r"^(-?\d{3,20}|@\w{4,64})$")


def tg_cfg():
    c = {"enabled": False, "token": "", "bot": "", "chats": [], "terminals": [], "skip_repeat": True}
    c.update(CFG.get("telegram") or {})
    return c


class TgError(Exception):
    pass


def tg_call(token, method, fields=None, files=None, timeout=25):
    """Bot API so'rovi (multipart). Xato bo'lsa Telegram javobini qaytaradi; tarmoq xatosida TgError."""
    b = uuid.uuid4().hex
    parts = [f'--{b}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'.encode("utf-8")
             for k, v in (fields or {}).items()]
    for k, (fname, data, ctype) in (files or {}).items():
        parts.append(f'--{b}\r\nContent-Disposition: form-data; name="{k}"; filename="{fname}"\r\n'
                     f'Content-Type: {ctype}\r\n\r\n'.encode() + data + b"\r\n")
    if parts:
        body, hdr = b"".join(parts) + f"--{b}--\r\n".encode(), {"Content-Type": f"multipart/form-data; boundary={b}"}
    else:
        body, hdr = b"", {"Content-Length": "0"}
    try:
        conn = http.client.HTTPSConnection(TG_HOST, timeout=timeout)
        try:
            conn.request("POST", f"/bot{token}/{method}", body, hdr)
            r = conn.getresponse()
            raw = r.read()
        finally:
            conn.close()
    except Exception as e:
        raise TgError(f"Telegram serveriga ulanib bo'lmadi ({type(e).__name__}). Internetni tekshiring.")
    try:
        return json.loads(raw.decode("utf-8"))
    except Exception:
        return {"ok": False, "error_code": r.status, "description": f"HTTP {r.status}"}


def tg_send(token, chat, text, photo=None):
    """Bitta chatga yuborish. (ok, xato_matni, yangi_chat_id)"""
    new_chat = None
    for _ in range(4):
        if photo:
            j = tg_call(token, "sendPhoto", {"chat_id": chat, "caption": text, "parse_mode": "HTML"},
                        {"photo": ("photo.jpg", photo, "image/jpeg")})
        else:
            j = tg_call(token, "sendMessage", {"chat_id": chat, "text": text, "parse_mode": "HTML"})
        if j.get("ok"):
            return True, None, new_chat
        prm = j.get("parameters") or {}
        if prm.get("migrate_to_chat_id"):          # guruh supergroup ga aylangan
            chat = new_chat = str(prm["migrate_to_chat_id"])
            continue
        if j.get("error_code") == 429 and prm.get("retry_after"):
            time.sleep(min(int(prm["retry_after"]), 60) + 1)
            continue
        if photo and j.get("error_code") == 400 and "photo" in str(j.get("description", "")).lower():
            photo = None                            # rasm qabul qilinmadi — matn bilan yuboramiz
            continue
        return False, j.get("description") or f"xato {j.get('error_code')}", new_chat
    return False, "Telegram javob bermadi", new_chat


def tg_event_info(eid):
    r = db.q("SELECT id, terminal_id, time, date, emp, name FROM events WHERE id=?", (eid,))
    if not r:
        return None
    e = r[0]
    ctx = make_ctx()
    p = person_of(e["terminal_id"], e["emp"], ctx, e["name"])
    kind, late = "in", 0
    g = day_groups(e["date"], ctx).get(p["key"])
    if g:
        kind = next((x["kind"] for x in g["evs"] if x["id"] == eid), "in")
        first_in = next((x for x in g["evs"] if x["kind"] == "in"), None)
        if kind == "in" and first_in and first_in["id"] == eid:
            wh, wm = map(int, CFG.get("work_start", "09:00").split(":"))
            hh, mm = map(int, e["time"][11:16].split(":"))
            late = max(0, hh * 60 + mm - (wh * 60 + wm))
    return {"id": eid, "terminal_id": e["terminal_id"], "terminal": ctx["tnames"].get(e["terminal_id"], "—"),
            "emp": e["emp"], "name": p["name"] or "Nomsiz", "time": e["time"], "kind": kind, "late": late}


def tg_caption(i):
    icon, title, st = {"in": ("🟢", "Hodim kirdi", "Kirdi"), "out": ("🔴", "Hodim chiqdi", "Chiqdi"),
                       "repeat": ("🔁", "Hodim qayta o'tdi", "Takroriy o'tish")}[i["kind"]]
    t = i["time"]
    lines = [f"{icon} <b>{title}</b>", "",
             f"👤 Hodim: <b>{html.escape(i['name'])}</b>",
             f"🆔 ID raqami: {html.escape(i['emp'])}",
             f"📍 Holati: {st}",
             f"📅 Sanasi: {t[8:10]}.{t[5:7]}.{t[0:4]}",
             f"🕒 Soati: {t[11:16]}",
             f"🏢 Terminal: {html.escape(i['terminal'])}"]
    if i["late"] > 0:
        lines.append(f"⏰ Kechikdi: {i['late'] // 60} soat {i['late'] % 60} daqiqa" if i["late"] >= 60
                     else f"⏰ Kechikdi: {i['late']} daqiqa")
    return "\n".join(lines)


def tg_photo(eid, wait=True):
    """Terminal olgan rasm (JPEG). Terminal rasmni biroz kechikib berishi mumkin — bir necha marta urinamiz."""
    for k in range(4 if wait else 1):
        try:
            r = get_photo(eid)
        except Exception:
            r = None
        if r and r[1] == "image/jpeg":
            return r[0]
        if DEMO or not wait:
            return None
        time.sleep(1.5)
    return None


def tg_deliver(c, info, photo):
    """Hamma tanlangan chatlarga yuboradi. Natija: [(chat, ok, xato)]"""
    out, changed = [], False
    for ch in c["chats"]:
        ok, err, new_chat = tg_send(c["token"], ch["id"], tg_caption(info), photo)
        if new_chat:
            ch["id"], changed = new_chat, True
        out.append((ch, ok, err))
        if ok:
            TG_STATE["sent"] += 1
            TG_STATE["last_ok"] = fmt_time(now_local())
        else:
            TG_STATE["last_error"] = f"{now_local().strftime('%d.%m %H:%M')} · {ch.get('title') or ch['id']}: {err}"
    if changed:
        CFG["telegram"] = {**tg_cfg(), "chats": c["chats"]}
        save_config(CFG)
    return out


def tg_notify(ids):
    c = tg_cfg()
    if c["enabled"] and c["token"] and c["chats"]:
        for i in ids:
            TG_Q.put(i)


class TgWorker(threading.Thread):
    daemon = True

    def run(self):
        while True:
            eid = TG_Q.get()
            try:
                c = tg_cfg()
                if not (c["enabled"] and c["token"] and c["chats"]):
                    continue
                info = tg_event_info(eid)
                if not info or (c["terminals"] and info["terminal_id"] not in c["terminals"]):
                    continue
                if info["kind"] == "repeat" and c["skip_repeat"]:
                    continue
                tg_deliver(c, info, tg_photo(eid))
            except Exception as e:
                TG_STATE["last_error"] = f"{now_local().strftime('%d.%m %H:%M')} · {e}"


def tg_public():
    c = tg_cfg()
    tok = c["token"]
    return {"enabled": c["enabled"], "has_token": bool(tok), "token_hint": (tok.split(":")[0] + ":…" + tok[-4:]) if tok else "",
            "bot": c["bot"], "chats": c["chats"], "terminals": c["terminals"], "skip_repeat": c["skip_repeat"],
            "queue": TG_Q.qsize(), **TG_STATE}


def tg_save(b):
    c = tg_cfg()
    tok = str(b.get("token") or "").strip()
    if tok:
        if not TOKEN_RE.match(tok):
            return 400, {"error": "Token noto'g'ri ko'rinishda. BotFather bergan tokenni to'liq nusxalang "
                                  "(masalan 123456789:AAH...)."}
        j = tg_call(tok, "getMe")
        if not j.get("ok"):
            return 400, {"error": "Telegram bu tokenni qabul qilmadi: " + str(j.get("description") or "")}
        c["token"], c["bot"] = tok, j["result"].get("username") or ""
    chats = []
    for ch in b.get("chats", c["chats"]) or []:
        cid = str(ch.get("id") or "").strip()
        if not CHAT_RE.match(cid):
            return 400, {"error": f"Chat ID noto'g'ri: {cid}"}
        if cid not in [x["id"] for x in chats]:
            chats.append({"id": cid, "title": str(ch.get("title") or cid)[:80]})
    c["chats"] = chats
    c["terminals"] = [int(t) for t in (b.get("terminals", c["terminals"]) or []) if str(t).isdigit()]
    c["skip_repeat"] = bool(b.get("skip_repeat", c["skip_repeat"]))
    c["enabled"] = bool(b.get("enabled", c["enabled"]))
    if c["enabled"] and not c["token"]:
        return 400, {"error": "Avval bot tokenini kiriting"}
    CFG["telegram"] = c
    save_config(CFG)
    return 200, {"ok": True, **tg_public()}


def tg_find_chats():
    c = tg_cfg()
    if not c["token"]:
        return 400, {"error": "Avval bot tokenini kiriting va saqlang"}
    j = tg_call(c["token"], "getUpdates", {"limit": 100, "timeout": 0})
    if not j.get("ok"):
        return 400, {"error": "Telegram: " + str(j.get("description") or "")}
    found = {}
    for u in j.get("result") or []:
        for k in ("message", "edited_message", "channel_post", "my_chat_member", "chat_member"):
            ch = (u.get(k) or {}).get("chat")
            if ch:
                name = ch.get("title") or " ".join(x for x in (ch.get("first_name"), ch.get("last_name")) if x) \
                    or ch.get("username") or str(ch["id"])
                found[str(ch["id"])] = {"id": str(ch["id"]), "title": name,
                                        "type": {"private": "shaxsiy", "group": "guruh", "supergroup": "guruh",
                                                 "channel": "kanal"}.get(ch.get("type"), ch.get("type") or "")}
    return 200, {"chats": list(found.values()), "bot": c["bot"]}


def tg_test():
    c = tg_cfg()
    if not c["token"]:
        return 400, {"error": "Avval bot tokenini kiriting va saqlang"}
    if not c["chats"]:
        return 400, {"error": "Avval kamida bitta chat qo'shing"}
    last = db.q("SELECT id FROM events ORDER BY time DESC, id DESC LIMIT 1")
    if last:
        info, photo = tg_event_info(last[0]["id"]), tg_photo(last[0]["id"], wait=False)
    else:
        n = fmt_time(now_local())
        info, photo = {"name": "Sinov xodim", "emp": "0", "time": n, "kind": "in", "late": 0,
                       "terminal": "SINOV"}, None
    res = tg_deliver(c, info, photo)
    bad = [f"{ch.get('title') or ch['id']}: {err}" for ch, ok, err in res if not ok]
    if bad:
        return 400, {"error": "Yuborilmadi — " + "; ".join(bad)}
    return 200, {"ok": True, "sent": len(res)}


# ----------------------------------------------------------------- BILLZ (savdo tizimi) ulanishi
BILLZ_HOST = "api-admin.billz.ai"
BILLZ_AUTH = {"token": None, "at": 0, "secret": None}
BILLZ_LOCK = threading.Lock()


class BillzError(Exception):
    pass


def billz_cfg():
    c = {"secret": "", "company": "", "connected_at": None}
    c.update(CFG.get("billz") or {})
    return c


def _billz_http(method, path, body=None, token=None, timeout=30):
    hdr = {"Accept": "application/json"}
    data = None
    if body is not None:
        data = json.dumps(body).encode("utf-8")
        hdr["Content-Type"] = "application/json"
    if token:
        hdr["Authorization"] = f"Bearer {token}"
    try:
        conn = http.client.HTTPSConnection(BILLZ_HOST, timeout=timeout)
        try:
            conn.request(method, path, data, hdr)
            r = conn.getresponse()
            raw = r.read()
        finally:
            conn.close()
    except Exception as e:
        raise BillzError(f"BILLZ serveriga ulanib bo'lmadi ({type(e).__name__}). Internetni tekshiring.")
    try:
        j = json.loads(raw.decode("utf-8")) if raw else {}
    except Exception:
        j = {"raw": raw[:300].decode("utf-8", "ignore")}
    return r.status, j


def billz_login(secret):
    st, j = _billz_http("POST", "/v1/auth/login", {"secret_token": secret})
    d = j.get("data") if isinstance(j, dict) else None
    if st != 200 or not d or not d.get("access_token"):
        msg = (j.get("message") or j.get("error") or "") if isinstance(j, dict) else ""
        raise BillzError("BILLZ kalitni qabul qilmadi" + (f": {msg}" if msg else ". Kalitni to'liq nusxalaganingizni tekshiring."))
    return d


def billz_token(force=False):
    secret = billz_cfg()["secret"]
    if not secret:
        raise BillzError("BILLZ ulanmagan. Sozlamalar → BILLZ bo'limida kalitni kiriting.")
    with BILLZ_LOCK:
        if force or BILLZ_AUTH["secret"] != secret or not BILLZ_AUTH["token"] or time.time() - BILLZ_AUTH["at"] > 3000:
            d = billz_login(secret)
            BILLZ_AUTH.update(token=d["access_token"], at=time.time(), secret=secret)
        return BILLZ_AUTH["token"]


def billz_get(path, params=None):
    """GET so'rov; token eskirgan bo'lsa bir marta yangilaydi. (status, json)"""
    q = ""
    if params:
        from urllib.parse import urlencode
        q = ("&" if "?" in path else "?") + urlencode({k: v for k, v in params.items() if v is not None}, doseq=True)
    st, j = _billz_http("GET", path + q, token=billz_token())
    if st == 401:
        st, j = _billz_http("GET", path + q, token=billz_token(force=True))
    return st, j


def billz_post(path, body):
    st, j = _billz_http("POST", path, body, token=billz_token())
    if st == 401:
        st, j = _billz_http("POST", path, body, token=billz_token(force=True))
    return st, j


BILLZ_CACHE = {}


def billz_cached(key, fn, ttl=60):
    hit = BILLZ_CACHE.get(key)
    if hit and time.time() - hit[0] < ttl:
        return hit[1]
    v = fn()
    BILLZ_CACHE[key] = (time.time(), v)
    return v


def _ok(st, j, what):
    if st != 200 or not isinstance(j, dict):
        msg = (j.get("message") or j.get("error")) if isinstance(j, dict) else ""
        raise BillzError(f"BILLZ {what} ma'lumotini bermadi (HTTP {st}{': ' + str(msg) if msg else ''})")
    return j


def _norm_name(s):
    s = (s or "").lower().replace("ʻ", "").replace("'", "").replace("`", "").replace("ʼ", "")
    return " ".join(sorted(re.findall(r"\w+", s)))


def billz_company_id():
    """Kompaniya ID (cheklar qidiruvi uchun kerak) — mijozlar ro'yxatidan olinadi va saqlanadi."""
    c = billz_cfg()
    if c.get("company_id"):
        return c["company_id"]
    j = _ok(*billz_get("/v1/customers-list", {"limit": 1, "page": 1}), "mijozlar")
    cid = ((j.get("customers") or [{}])[0]).get("company_id") or ""
    if cid:
        CFG["billz"] = {**c, "company_id": cid}
        save_config(CFG)
    return cid


def _fetch_orders(d):
    cid = billz_company_id()
    orders, page = [], 1
    while page <= 60:
        j = _ok(*billz_get("/v3/order-search", {"company_id": cid, "start_date": d, "end_date": d, "page": page,
                                                "limit": 500, "epos_flag": 0, "only_deleted": "false"}), "savdo")
        batch = [o for g in (j.get("orders_sorted_by_date_list") or []) for o in (g.get("orders") or [])]
        orders += batch
        if not batch or len(orders) >= (j.get("count") or 0):
            break
        page += 1
    return orders


def _agg_day(d, orders):
    a = {"date": d, "total": 0, "checks": 0, "refunds": 0, "exchanges": 0, "items": 0, "hours": [0] * 24,
         "shops": {}, "payments": {}, "sellers": {}, "products": {}}
    for o in orders:
        od = o.get("order_detail") or {}
        typ = o.get("order_type") or ""
        tp = od.get("total_price") or 0
        a["total"] += tp
        if typ == "SALE":
            a["checks"] += 1
        elif typ == "RETURN":
            a["refunds"] += 1
        elif typ == "EXCHANGE":
            a["exchanges"] += 1
        ts = o.get("display_sold_at") or od.get("created_at") or o.get("created_at") or ""
        if len(ts) >= 13 and ts[11:13].isdigit():
            a["hours"][int(ts[11:13]) % 24] += tp
        shop = (od.get("shop") or {}).get("name") or "—"
        a["shops"][shop] = a["shops"].get(shop, 0) + tp
        for p in od.get("order_payments") or []:
            n = (p.get("company_payment_type") or {}).get("name") or "—"
            a["payments"][n] = a["payments"].get(n, 0) + (p.get("paid_amount") or 0) - (p.get("returned_amount") or 0)
        for it in od.get("order_items") or []:
            itp = it.get("total_price") or 0
            mv = it.get("measurement_value") or 0
            sellers = [s.get("seller", {}).get("name") or "" for s in it.get("sellers") or []] or \
                [(od.get("user") or {}).get("name") or "—"]
            for sname in sellers:
                a["sellers"][sname or "—"] = a["sellers"].get(sname or "—", 0) + itp / len(sellers)
            pr = it.get("product") or {}
            pid = it.get("product_id") or pr.get("id") or pr.get("name")
            if pid:
                cur = a["products"].setdefault(pid, [pr.get("name") or it.get("name") or "—", 0, 0])
                cur[1] += -mv if itp < 0 else mv
                cur[2] += itp
            if itp > 0:
                a["items"] += mv
    return a


DAY_LOCK = threading.Lock()


def billz_day(d):
    """Bir kunlik savdo yig'indisi. O'tgan kunlar bazada saqlanadi, bugungisi har daqiqada yangilanadi."""
    today = now_local().strftime("%Y-%m-%d")
    if d > today:
        return _agg_day(d, [])
    r = db.q("SELECT data, fetched, final FROM billz_days WHERE date=?", (d,))
    if r and (r[0]["final"] or time.time() - r[0]["fetched"] < 60):
        return json.loads(r[0]["data"])
    a = _agg_day(d, _fetch_orders(d))
    final = 1 if d < today and now_local().hour >= 1 else 0     # o'tgan kun — endi o'zgarmaydi
    db.x("INSERT OR REPLACE INTO billz_days(date, data, fetched, final) VALUES(?,?,?,?)",
         (d, json.dumps(a, ensure_ascii=False), time.time(), final))
    return a


def sales_report(d1, d2):
    one_day = d1 == d2
    days = []
    x = datetime.fromisoformat(d1)
    while x.strftime("%Y-%m-%d") <= d2 and len(days) < 62:
        days.append(x.strftime("%Y-%m-%d"))
        x += timedelta(days=1)
    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(4) as ex:
        aggs = list(ex.map(billz_day, days))
    total = sum(a["total"] for a in aggs)
    merge = lambda key: {k: sum(a[key].get(k, 0) for a in aggs) for a2 in aggs for k in a2[key]}
    shops, payments, sellers_sum = merge("shops"), merge("payments"), merge("sellers")
    prods = {}
    for a in aggs:
        for pid, (name, q, s) in a["products"].items():
            cur = prods.setdefault(pid, [name, 0, 0])
            cur[1] += q
            cur[2] += s
    if one_day:
        series = [{"t": f"{d1} {h:02d}:00:00", "v": v} for h, v in enumerate(aggs[0]["hours"])]
    else:
        series = [{"t": f"{a['date']} 00:00:00", "v": a["total"]} for a in aggs]
    # sotuvchilar + davomat
    links = billz_cfg().get("sellers") or {}
    ctx = make_ctx()
    staff_by_norm = {_norm_name(s["name"]): sid for sid, s in ctx["staff"].items()}
    att = {}
    for d in days:
        if d > now_local().strftime("%Y-%m-%d"):
            break
        for r in day_summary(d, None, ctx)["rows"]:
            a = att.setdefault(r["key"], {"days": 0, "worked": 0, "late_days": 0})
            a["days"] += 1
            a["worked"] += r["worked_min"]
            a["late_days"] += 1 if r["late_min"] > 0 else 0
            if one_day:
                a.update(first_in=r["first_in"], last_out=r["last_out"], inside=r["inside"], late=r["late_min"],
                         first_term=r["first_term"])
    sellers = []
    for name, tot in sorted(sellers_sum.items(), key=lambda kv: -kv[1]):
        if abs(tot) < 1:
            continue
        sid = links.get(name)
        if sid is None:
            sid = staff_by_norm.get(_norm_name(name))
        sid = sid if sid in ctx["staff"] else None
        sellers.append({"name": name, "total": tot, "share": tot / total if total else 0,
                        "staff_id": sid, "staff_name": ctx["staff"][sid]["name"] if sid else None,
                        "auto": sid is not None and name not in links, "att": att.get(f"s{sid}") if sid else None})
    top = sorted(prods.values(), key=lambda p: -p[2])[:15]
    return {"connected": True, "from": d1, "to": d2, "one_day": one_day, "total": total,
            "checks": sum(a["checks"] for a in aggs), "items": sum(a["items"] for a in aggs),
            "refunds": sum(a["refunds"] for a in aggs), "exchanges": sum(a["exchanges"] for a in aggs),
            "series": series,
            "shops": [{"name": k, "total": v} for k, v in sorted(shops.items(), key=lambda kv: -kv[1])],
            "payments": [{"name": k, "total": v} for k, v in sorted(payments.items(), key=lambda kv: -kv[1])],
            "sellers": sellers,
            "products": [{"name": n, "qty": q, "total": s} for n, q, s in top],
            "staff": [{"id": sid, "name": s["name"]} for sid, s in sorted(ctx["staff"].items(), key=lambda kv: kv[1]["name"])],
            "fetched": fmt_time(now_local())}


def _search_body(status, limit=1, page=1, statistics=False):
    return {"status": status, "order": [""], "group_variations": False, "product_field_filters": [],
            "field_search_key": "", "archived_list": False, "brand_ids": [], "plu_codes": [], "supplier_ids": [],
            "measurement_unit_ids": [], "is_free_price": None, "statistics": statistics, "limit": limit, "page": page}


def stock_report():
    def load():
        shop_names = {}
        try:
            st, j = billz_get("/v1/shop", {"limit": 100})
            for s in (j.get("shops") or []) if isinstance(j, dict) else []:
                shop_names[s.get("id")] = s.get("name")
        except BillzError:
            pass
        prods, page, count = [], 1, 0
        while page <= 30:
            j = _ok(*billz_post("/v2/product-search-with-filters", _search_body("all", limit=1000, page=page)), "ombor")
            lst = j.get("products") or []
            count = j.get("count") or 0
            prods += lst
            if not lst or len(prods) >= count:
                break
            page += 1
        units, qty, retail, supply, zero, neg = {}, 0, 0, 0, 0, 0
        rows = {}
        for p in prods:
            unit = (p.get("measurement_unit") or {}).get("short_name") or ""
            q = (p.get("measurement_values") or {}).get("total_active_measurement_value") or 0
            prices = {sp.get("shop_id"): sp for sp in p.get("shop_prices") or []}
            per_shop = []
            for sm in p.get("shop_measurement_values") or []:
                sq = sm.get("total_active_measurement_value") or 0
                pr = prices.get(sm.get("shop_id")) or {}
                if sq > 0:
                    retail += sq * (pr.get("retail_price") or 0)
                    supply += sq * (pr.get("supply_price") or 0)
                if sq:
                    per_shop.append({"name": shop_names.get(sm.get("shop_id")) or sm.get("shop_name") or "", "qty": sq})
            qty += q
            units[unit] = units.get(unit, 0) + q
            if q == 0:
                zero += 1
            elif q < 0:
                neg += 1
            rows[p.get("id")] = {"name": p.get("name"), "sku": p.get("sku"), "unit": unit, "qty": q, "shops": per_shop}
        # oxirgi 7 kunda sotilgan, lekin kam qolgan (≤3) mahsulotlar
        sold = {}
        today = now_local()
        for k in range(7):
            try:
                a = billz_day((today - timedelta(days=k)).strftime("%Y-%m-%d"))
            except BillzError:
                continue
            for pid, (name, q, s) in a["products"].items():
                sold[pid] = sold.get(pid, 0) + q
        low = []
        for pid, q in sold.items():
            r = rows.get(pid)
            if r and q > 0 and r["qty"] <= 3:
                low.append({**r, "sold7": q})
        low.sort(key=lambda r: (r["qty"], -r["sold7"]))
        return {"connected": True, "products": count, "qty": qty,
                "units": [{"measurement_unit": k or "—", "measurement_value": v} for k, v in units.items() if v],
                "retail": retail, "supply": supply, "small_left": len(low), "zero_left": zero, "negative": neg,
                "low": low[:100], "fetched": fmt_time(now_local())}
    return billz_cached(("stock",), load, ttl=1800)


def debts_report():
    def load():
        out, page, count = [], 1, None
        while page <= 40:
            j = _ok(*billz_get("/v1/customers-list", {"limit": 100, "page": page}), "mijozlar")
            lst = j.get("customers") or []
            count = j.get("count") or 0
            for c in lst:
                debt = c.get("debt_amount") or 0
                if debt > 0:
                    out.append({"name": " ".join(x for x in (c.get("first_name"), c.get("last_name")) if x).strip() or "—",
                                "phone": (c.get("phone_numbers") or [""])[0], "debt": debt,
                                "purchases": c.get("purchase_amount") or 0,
                                "shop": (c.get("registered_shop") or {}).get("name") or "",
                                "last": c.get("last_purchase_date") or ""})
            if not lst or page * 100 >= count:
                break
            page += 1
        out.sort(key=lambda r: -r["debt"])
        return {"connected": True, "customers": count or 0, "debtors": len(out),
                "total": sum(r["debt"] for r in out), "rows": out, "fetched": fmt_time(now_local())}
    return billz_cached(("debts",), load, ttl=300)


def billz_link_seller(b):
    name = str(b.get("name") or "").strip()
    if not name:
        return 400, {"error": "Sotuvchi nomi yo'q"}
    c = billz_cfg()
    sellers = dict(c.get("sellers") or {})
    sid = b.get("staff_id")
    if sid in (None, ""):
        sellers[name] = 0          # 0 = ataylab bog'lanmagan
    else:
        sellers[name] = int(sid)
    CFG["billz"] = {**c, "sellers": sellers}
    save_config(CFG)
    BILLZ_CACHE.clear()
    return 200, {"ok": True}


def billz_public():
    c = billz_cfg()
    return {"connected": bool(c["secret"]), "company": c["company"], "connected_at": c["connected_at"],
            "secret_hint": ("…" + c["secret"][-4:]) if c["secret"] else ""}


def billz_save(b):
    if b.get("disconnect"):
        CFG["billz"] = {}
        save_config(CFG)
        BILLZ_AUTH.update(token=None, secret=None)
        return 200, {"ok": True, **billz_public()}
    secret = str(b.get("secret") or "").strip()
    if not secret or len(secret) < 20 or len(secret) > 4096 or any(ch.isspace() for ch in secret):
        return 400, {"error": "Kalit noto'g'ri ko'rinishda. BILLZ bergan maxfiy kalitni to'liq nusxalang."}
    d = billz_login(secret)
    company = ""
    try:
        st, j = _billz_http("GET", "/v1/shop?limit=100", token=d["access_token"])
        shops = (j.get("shops") or (j.get("data") or {}).get("shops") or []) if isinstance(j, dict) else []
        company = ", ".join(s.get("name", "") for s in shops[:5] if s.get("name"))
    except BillzError:
        pass
    CFG["billz"] = {**billz_cfg(), "secret": secret, "company": company, "connected_at": fmt_time(now_local())}
    BILLZ_CACHE.clear()
    save_config(CFG)
    BILLZ_AUTH.update(token=d["access_token"], at=time.time(), secret=secret)
    return 200, {"ok": True, **billz_public()}


# ----------------------------------------------------------------- SalesDoc rasxodlari (faqat o'qish)
# SalesDoc'da API yo'q: dashboard foydalanuvchi logini bilan kirib, "Расходы" sahifasidagi jadvalni o'qiydi.
# Hech qanday forma yuborilmaydi (kirishdan tashqari) — SalesDoc'dagi ma'lumot o'zgarmaydi.
SD_LOCK = threading.Lock()
SD_SESS = {"cookies": {}, "user": None, "host": None}
SD_CACHE = {}
SD_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Davomat-dashboard"


class SalesDocError(Exception):
    pass


def sd_cfg():
    c = {"host": "rafiq.salesdoc.io", "username": "", "password": "", "connected_at": None}
    c.update(CFG.get("salesdoc") or {})
    return c


def _sd_http(host, method, path, form=None, cookies=None, timeout=60):
    hdr = {"User-Agent": SD_UA, "Accept": "text/html,*/*"}
    data = None
    if form is not None:
        from urllib.parse import urlencode
        data = urlencode(form).encode("utf-8")
        hdr["Content-Type"] = "application/x-www-form-urlencoded"
    if cookies:
        hdr["Cookie"] = "; ".join(f"{k}={v}" for k, v in cookies.items())
    try:
        conn = http.client.HTTPSConnection(host, timeout=timeout)
        try:
            conn.request(method, path, data, hdr)
            r = conn.getresponse()
            raw = r.read()
            got = {}
            for k, v in r.getheaders():
                if k.lower() == "set-cookie":
                    nv = v.split(";", 1)[0]
                    if "=" in nv:
                        n, val = nv.split("=", 1)
                        got[n.strip()] = val.strip()
            return r.status, r.getheader("Location"), got, raw.decode("utf-8", "ignore")
        finally:
            conn.close()
    except Exception as e:
        raise SalesDocError(f"SalesDoc serveriga ulanib bo'lmadi ({type(e).__name__}). Internetni tekshiring.")


def _sd_is_login(page):
    return "LoginForm[username]" in page


def sd_login(host, username, password):
    st, _, ck, _ = _sd_http(host, "GET", "/site/login")
    cookies = {k: v for k, v in ck.items() if v and v != "deleted"}
    st, loc, ck, page = _sd_http(host, "POST", "/site/login", {
        "LoginForm[username]": username, "LoginForm[password]": password, "LoginForm[rememberMe]": "1"}, cookies)
    for k, v in ck.items():
        if v and v != "deleted":
            cookies[k] = v
        else:
            cookies.pop(k, None)
    if st not in (301, 302, 303) and (_sd_is_login(page) or st >= 400):
        raise SalesDocError("SalesDoc login yoki parolni qabul qilmadi. SalesDoc saytiga kiradigan login/parolni tekshiring.")
    return cookies


class _SdTables(html.parser.HTMLParser):
    """Sahifadagi hamma jadvallarni (sarlavha + qatorlar matni) yig'adi."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.tables, self.stack = [], []

    def handle_starttag(self, tag, attrs):
        if tag == "table":
            self.stack.append({"head": [], "rows": [], "row": None, "cell": None, "in_head": False})
            return
        if not self.stack:
            return
        t = self.stack[-1]
        if tag == "thead":
            t["in_head"] = True
        elif tag == "tr":
            t["row"] = {"cells": [], "id": None, "summa": None}
        elif tag in ("td", "th") and t["row"] is not None:
            t["cell"] = []
        elif tag == "input" and t["row"] is not None:
            a = dict(attrs)
            if a.get("data-consumption-id"):
                t["row"]["id"] = a["data-consumption-id"]
        elif tag == "a" and t["row"] is not None:
            a = dict(attrs)
            if "update" in (a.get("class") or "").split() and a.get("summa"):
                t["row"]["summa"] = a["summa"]  # aniq summa (tiyinlari bilan)

    def handle_endtag(self, tag):
        if not self.stack:
            return
        t = self.stack[-1]
        if tag == "table":
            self.tables.append(self.stack.pop())
        elif tag == "thead":
            t["in_head"] = False
        elif tag in ("td", "th") and t["row"] is not None and t["cell"] is not None:
            t["row"]["cells"].append(" ".join("".join(t["cell"]).split()))
            t["cell"] = None
        elif tag == "tr" and t["row"] is not None:
            if t["in_head"]:
                t["head"] = t["row"]["cells"]
            else:
                t["rows"].append(t["row"])
            t["row"] = None

    def handle_data(self, data):
        if self.stack and self.stack[-1]["cell"] is not None:
            self.stack[-1]["cell"].append(data)


def _sd_num(s):
    s = (s or "").replace("\xa0", "").replace(" ", "").replace(",", "")
    try:
        return float(s)
    except ValueError:
        return 0.0


def _sd_date(s):
    m = re.match(r"(\d{2})\.(\d{2})\.(\d{4})(?:\s+(\d{2}:\d{2}(?::\d{2})?))?", s or "")
    if not m:
        return ""
    d = f"{m.group(3)}-{m.group(2)}-{m.group(1)}"
    return d + (" " + m.group(4) if m.group(4) else "")


def sd_parse(page):
    p = _SdTables()
    p.feed(page)
    cols = {"ИД": "id", "Фонд": "fund", "Статья расхода": "article", "Касса": "cashbox", "Сумма": "amount",
            "Валюта": "currency", "Дата расхода": "date", "Дата создания": "created", "Кто добавил": "author",
            "Комментарий": "comment"}
    for t in p.tables:
        if not {"Фонд", "Сумма", "Дата расхода"} <= set(t["head"]):
            continue
        idx = {cols[h]: i for i, h in enumerate(t["head"]) if h in cols}
        out = []
        for r in t["rows"]:
            c = r["cells"]
            g = lambda k: c[idx[k]] if k in idx and idx[k] < len(c) else ""
            rid = r["id"] or g("id")
            if not (rid and rid.isdigit()):
                continue
            out.append({"id": int(rid), "fund": g("fund"), "article": g("article"), "cashbox": g("cashbox"),
                        "amount": _sd_num(r["summa"] or g("amount")), "currency": g("currency"), "date": _sd_date(g("date")),
                        "created": _sd_date(g("created")), "author": g("author"), "comment": g("comment")})
        return out
    raise SalesDocError("SalesDoc'dagi rasxodlar jadvali topilmadi (sahifa tuzilishi o'zgargan bo'lishi mumkin).")


def sd_fetch(d1, d2):
    c = sd_cfg()
    if not c["username"]:
        raise SalesDocError("SalesDoc ulanmagan. Sozlamalar → SalesDoc bo'limida login/parolni kiriting.")
    path = f"/finans/consumption?dateType=DATE&datestart={d1}&endstart={d2}"
    with SD_LOCK:
        if SD_SESS["user"] != c["username"] or SD_SESS["host"] != c["host"]:
            SD_SESS.update(cookies={}, user=c["username"], host=c["host"])
        for attempt in range(2):
            if not SD_SESS["cookies"]:
                SD_SESS["cookies"] = sd_login(c["host"], c["username"], c["password"])
            st, loc, ck, page = _sd_http(c["host"], "GET", path, cookies=SD_SESS["cookies"], timeout=90)
            if st == 200 and not _sd_is_login(page):
                return sd_parse(page)
            SD_SESS["cookies"] = {}  # sessiya eskirgan — qayta kiramiz
        raise SalesDocError(f"SalesDoc rasxodlar sahifasini bermadi (HTTP {st}).")


def sd_store(d1, d2, rows):
    """Davr uchun bazadagi nusxani SalesDoc'dagisi bilan bir xil qiladi (o'chirilganlar ham o'chadi)."""
    with db.lock:
        c = db.conn
        c.execute("DELETE FROM expenses WHERE date BETWEEN ? AND ?", (d1, d2))
        c.executemany("INSERT OR REPLACE INTO expenses(id, date, fund, article, cashbox, amount, currency, comment, "
                      "created, author, fetched) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                      [(r["id"], r["date"], r["fund"], r["article"], r["cashbox"], r["amount"], r["currency"],
                        r["comment"], r["created"], r["author"], time.time()) for r in rows])
        c.commit()


def expenses_report(d1, d2, fresh=False):
    key = (d1, d2)
    hit = SD_CACHE.get(key)
    err = None
    if fresh or not hit or time.time() - hit[0] > 120:
        try:
            rows = sd_fetch(d1, d2)
            rows = [r for r in rows if d1 <= r["date"] <= d2]
            sd_store(d1, d2, rows)
            SD_CACHE[key] = hit = (time.time(), rows)
        except SalesDocError as e:
            err = str(e)
    if hit and not err:
        at, rows = hit
    else:
        rows = db.q("SELECT id, date, fund, article, cashbox, amount, currency, comment, created, author "
                    "FROM expenses WHERE date BETWEEN ? AND ? ORDER BY date, id", (d1, d2))
        f = db.q("SELECT MAX(fetched) AS f FROM expenses WHERE date BETWEEN ? AND ?", (d1, d2))
        at = f[0]["f"] if f and f[0]["f"] else None
        if err:
            err += (" Oxirgi saqlangan ma'lumot ko'rsatilmoqda." if rows else "")
    rows = sorted(rows, key=lambda r: (r["date"], r["id"]), reverse=True)
    return {"connected": True, "from": d1, "to": d2, "rows": rows, "error": err,
            "fetched": fmt_time(datetime.fromtimestamp(at)) if at else None}


def sd_public():
    c = sd_cfg()
    return {"connected": bool(c["username"] and c["password"]), "host": c["host"], "username": c["username"],
            "connected_at": c["connected_at"]}


def sd_save(b):
    if b.get("disconnect"):
        CFG["salesdoc"] = {}
        save_config(CFG)
        SD_SESS.update(cookies={}, user=None, host=None)
        SD_CACHE.clear()
        return 200, {"ok": True, **sd_public()}
    host = str(b.get("host") or "rafiq.salesdoc.io").strip().lower()
    host = re.sub(r"^https?://", "", host).split("/")[0]
    user = str(b.get("username") or "").strip()
    pw = str(b.get("password") or "")
    if not re.fullmatch(r"[a-z0-9-]+\.salesdoc\.io", host):
        return 400, {"error": "Manzil noto'g'ri. Masalan: rafiq.salesdoc.io"}
    if not user or len(user) > 128:
        return 400, {"error": "SalesDoc loginini kiriting"}
    if not pw:
        if sd_cfg()["password"] and sd_cfg()["username"] == user and sd_cfg()["host"] == host:
            pw = sd_cfg()["password"]
        else:
            return 400, {"error": "SalesDoc parolini kiriting"}
    if len(pw) > 256:
        return 400, {"error": "Parol juda uzun"}
    cookies = sd_login(host, user, pw)
    st, _, _, page = _sd_http(host, "GET", "/finans/consumption?dateType=DATE", cookies=cookies, timeout=90)
    if st != 200 or _sd_is_login(page):
        raise SalesDocError("SalesDoc'ga kirildi, lekin rasxodlar sahifasi ochilmadi — bu foydalanuvchida "
                            "«Расходы» bo'limiga ruxsat bormi?")
    sd_parse(page)
    CFG["salesdoc"] = {"host": host, "username": user, "password": pw, "connected_at": fmt_time(now_local())}
    save_config(CFG)
    with SD_LOCK:
        SD_SESS.update(cookies=cookies, user=user, host=host)
    SD_CACHE.clear()
    return 200, {"ok": True, **sd_public()}


# ----------------------------------------------------------------- dashboard foydalanuvchilari
SESSION_DAYS = 30
FAILS = {}
USERNAME_RE = re.compile(r"^[\w.@-]{3,32}$")
HOST_RE = re.compile(r"^[A-Za-z0-9.\-]{1,253}$")


def hash_pw(pw, salt=None):
    salt = salt or secrets.token_hex(16)
    return salt, hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), bytes.fromhex(salt), 200_000).hex()


def check_pw(username, pw):
    r = db.q("SELECT salt, hash FROM accounts WHERE username=?", (username,))
    if not r:
        hash_pw(pw)
        return False
    return secrets.compare_digest(hash_pw(pw, r[0]["salt"])[1], r[0]["hash"])


def add_account(username, pw):
    salt, h = hash_pw(pw)
    db.x("INSERT INTO accounts(username, salt, hash, created) VALUES(?,?,?,?)",
         (username, salt, h, fmt_time(now_local())))


def validate_new(username, pw):
    if not USERNAME_RE.match(username):
        return "Login 3–32 belgi bo'lsin: harf, raqam, _ . @ - (bo'sh joysiz)"
    if len(pw) < 6:
        return "Parol kamida 6 belgi bo'lsin"
    return None


def session_cookie(tok, max_age):
    sec = "; Secure" if CLOUD else ""   # bulutda faqat HTTPS orqali
    return {"Set-Cookie": f"dsid={tok}; HttpOnly; SameSite=Strict; Path=/; Max-Age={max_age}{sec}"}


# ----------------------------------------------------------------- terminal / xodim boshqaruvi
def test_terminal(host, port, user, pw):
    if DEMO:
        return 200, {"model": "DS-K1T343MFWX (demo)"}
    try:
        return 200, Device(host, port, user, pw).info()
    except AuthError:
        return 403, {"error": "Terminal login yoki paroli noto'g'ri. Diqqat: ko'p marta xato kiritilsa terminal "
                              "akkauntni bir muddat bloklaydi."}
    except Exception as e:
        return 502, {"error": f"Terminalga ulanib bo'lmadi ({host}:{port}): {e}"}


def save_terminal(b):
    tid = b.get("id")
    name = str(b.get("name") or "").strip()
    host = str(b.get("host") or "").strip()
    user = str(b.get("username") or "").strip()
    pw = str(b.get("password") or "")
    try:
        port = int(b.get("port") or 80)
    except ValueError:
        return 400, {"error": "Port raqam bo'lsin"}
    if not 1 <= len(name) <= 40:
        return 400, {"error": "Terminal nomini kiriting (masalan SKLAD)"}
    if not HOST_RE.match(host):
        return 400, {"error": "IP manzil noto'g'ri (masalan 192.168.1.15)"}
    if not user:
        return 400, {"error": "Terminal loginini kiriting"}
    if db.q("SELECT 1 FROM terminals WHERE lower(name)=lower(?) AND id!=?", (name, tid or 0)):
        return 409, {"error": "Bunday nomli terminal bor"}
    if db.q("SELECT 1 FROM terminals WHERE host=? AND port=? AND id!=?", (host, port, tid or 0)):
        return 409, {"error": "Bu IP manzildagi terminal allaqachon qo'shilgan"}
    with TERM_LOCK:
        if tid:
            old = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
            if not old:
                return 404, {"error": "Terminal topilmadi"}
            old = old[0]
            pw = pw or old["password"]
            changed = (host, port, user, pw) != (old["host"], old["port"], old["username"], old["password"])
            if changed or TSTATE.get(tid, {}).get("need_login"):
                code, res = test_terminal(host, port, user, pw)
                if code != 200:
                    return code, res
                if (host, port) != (old["host"], old["port"]):  # boshqa qurilma bo'lishi mumkin — qayta tanib olamiz
                    db.x("UPDATE terminals SET mac=NULL, serial=NULL WHERE id=?", (tid,))
                remember_identity(tid, res)
            db.x("UPDATE terminals SET name=?, host=?, port=?, username=?, password=? WHERE id=?",
                 (name, host, port, user, pw, tid))
            if changed or not TSTATE.get(tid, {}).get("connected"):
                start_poller(db.q("SELECT * FROM terminals WHERE id=?", (tid,))[0])
            return 200, {"ok": True, "id": tid}
        if not pw:
            return 400, {"error": "Terminal parolini kiriting"}
        code, res = test_terminal(host, port, user, pw)
        if code != 200:
            return code, res
        tid = db.x("INSERT INTO terminals(name, host, port, username, password, created) VALUES(?,?,?,?,?,?)",
                   (name, host, port, user, pw, fmt_time(now_local())))
        remember_identity(tid, res)
        t = db.q("SELECT * FROM terminals WHERE id=?", (tid,))[0]
        start_poller(t)
        TSTATE.setdefault(tid, {})["device"] = res
        return 200, {"ok": True, "id": tid}


def delete_terminal(tid):
    with TERM_LOCK:
        stop_poller(tid)
        for sql in ("DELETE FROM terminals WHERE id=?", "DELETE FROM events WHERE terminal_id=?",
                    "DELETE FROM term_users WHERE terminal_id=?", "DELETE FROM links WHERE terminal_id=?"):
            db.x(sql, (tid,))
    return 200, {"ok": True}


def set_terminal_active(tid, active):
    with TERM_LOCK:
        if not db.q("SELECT 1 FROM terminals WHERE id=?", (tid,)):
            return 404, {"error": "Terminal topilmadi"}
        db.x("UPDATE terminals SET active=? WHERE id=?", (1 if active else 0, tid))
        start_poller(db.q("SELECT * FROM terminals WHERE id=?", (tid,))[0])  # o'chirilgan bo'lsa faqat to'xtatadi
    return 200, {"ok": True}


# ----------------------------------------------------------------- terminalni tarmoqdan topish (SADP)
def _norm_mac(m):
    return re.sub(r"[^0-9a-f]", "", str(m or "").lower())


def _same_serial(a, b):
    # SADP va deviceInfo seriyani turlicha uzunlikda beradi, lekin oxirgi 9 belgi (masalan LA2086631) bir xil.
    # MAC ham har doim mos kelmaydi (terminalda bir nechta tarmoq interfeysi bor), shuning uchun asosiysi — seriya.
    a, b = str(a or "").strip().upper(), str(b or "").strip().upper()
    return len(a) >= 9 and len(b) >= 9 and a[-9:] == b[-9:]


def _local_ips():
    ips = set()
    try:
        ips |= {a[4][0] for a in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET)}
    except OSError:
        pass
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ips.add(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    return sorted(i for i in ips if not i.startswith(("127.", "169.254.")))


DISCOVER_LOCK = threading.Lock()


def discover(wait=2.5):
    """Hikvision SADP: lokal tarmoqdagi hamma Hikvision qurilmalari o'z IP, MAC va seriyasini aytadi."""
    if DEMO:
        return [{"ip": t["host"], "port": t["port"], "model": "DS-K1T343MFWX (demo)", "mac": "", "serial": "",
                 "activated": True} for t in terminals()]
    probe = (f'<?xml version="1.0" encoding="utf-8"?><Probe><Uuid>{str(uuid.uuid4()).upper()}</Uuid>'
             f'<Types>inquiry</Types></Probe>').encode()
    with DISCOVER_LOCK:
        socks = []
        for ip in _local_ips():
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
                s.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(ip))
                s.bind((ip, 0))
                s.setblocking(False)
                for _ in range(2):
                    s.sendto(probe, ("239.255.255.250", 37020))
                socks.append(s)
            except OSError:
                continue
        found = {}
        end = time.time() + wait
        try:
            while socks and time.time() < end:
                ready, _, _ = select.select(socks, [], [], 0.3)
                for s in ready:
                    try:
                        data, _ = s.recvfrom(65535)
                    except OSError:
                        continue
                    x = data.decode("utf-8", "ignore")
                    g = lambda k: (re.search(f"<{k}>([^<]*)</{k}>", x) or [None, ""])[1].strip()
                    mac, ip = _norm_mac(g("MAC")), g("IPv4Address")
                    if not ip or (mac or ip) in found:
                        continue
                    try:
                        port = int(g("HttpPort") or 80)
                    except ValueError:
                        port = 80
                    found[mac or ip] = {"ip": ip, "port": port, "model": g("DeviceDescription") or g("DeviceType"),
                                        "mac": mac, "serial": g("DeviceSN"),
                                        "activated": g("Activated").lower() != "false"}
        finally:
            for s in socks:
                s.close()
    return sorted(found.values(), key=lambda d: tuple(int(p) if p.isdigit() else 0 for p in d["ip"].split(".")))


def remember_identity(tid, info):
    mac, serial = _norm_mac((info or {}).get("mac")), str((info or {}).get("serial") or "").strip()
    if mac or serial:
        db.x("UPDATE terminals SET mac=COALESCE(NULLIF(?, ''), mac), serial=COALESCE(NULLIF(?, ''), serial) "
             "WHERE id=?", (mac, serial, tid))


def relocate_terminal(tid):
    """Terminal IP si o'zgargan bo'lsa (DHCP) — yangi IP ni topib, bazada yangilaydi. (host, port) yoki None."""
    if DEMO:
        return None
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not rows:
        return None
    t = rows[0]
    found = discover()
    mac = _norm_mac(t.get("mac"))
    cand = [d for d in found if (mac and d["mac"] == mac) or _same_serial(d["serial"], t.get("serial"))]
    if not cand and not mac and not t.get("serial"):
        # bu terminal hali "tanib olinmagan" (eski yozuv): boshqa terminalga tegishli bo'lmagan qurilmalardan
        # qaysi biri bizning login/parolni qabul qilsa — o'sha
        used = {(x["host"], x["port"]) for x in terminals() if x["id"] != tid}
        others = db.q("SELECT serial FROM terminals WHERE id!=?", (tid,))
        for d in found[:5]:
            if (d["ip"], d["port"]) in used or (d["ip"], d["port"]) == (t["host"], t["port"]) or \
                    any(_same_serial(o["serial"], d["serial"]) for o in others):
                continue
            try:
                info = Device(d["ip"], d["port"], t["username"], t["password"], timeout=5).info()
            except Exception:
                continue
            remember_identity(tid, info)
            cand = [d]
            break
    if not cand or (cand[0]["ip"], cand[0]["port"]) == (t["host"], t["port"]):
        return None
    d = cand[0]
    db.x("UPDATE terminals SET host=?, port=? WHERE id=?", (d["ip"], d["port"], tid))
    print(f"[IP] {t['name']}: {t['host']} -> {d['ip']} (terminal IP si o'zgargan, avtomatik yangilandi)", flush=True)
    return d["ip"], d["port"]


def discover_info():
    rows = db.q("SELECT id, name, host, port, mac, serial FROM terminals")
    out = []
    for d in discover():
        t = next((r for r in rows if _same_serial(r["serial"], d["serial"])), None) or \
            next((r for r in rows if r["mac"] and _norm_mac(r["mac"]) == d["mac"]), None) or \
            next((r for r in rows if (r["host"], r["port"]) == (d["ip"], d["port"])), None)
        out.append({**{k: d[k] for k in ("ip", "port", "model", "activated")},
                    "mac": "-".join(d["mac"][i:i + 2] for i in range(0, len(d["mac"]), 2)),
                    "terminal": t["name"] if t else None})
    return {"devices": out}


# ----------------------------------------------------------------- terminal -> bulut (HTTP push)
# Terminal har bir o'tishni (rasmi bilan) internet orqali to'g'ridan-to'g'ri shu serverga yuboradi —
# ofis kompyuteri o'chiq bo'lsa ham. Manzil: /hook/<terminal_id>/<token>. Token terminal parolidan
# hisoblanadi (HMAC), shuning uchun alohida maxfiy kalit saqlash/kiritish shart emas.
def push_token(t):
    key = f"{t.get('password') or ''}|{t.get('serial') or ''}".encode("utf-8")
    return hmac.new(key, f"davomat-push:{t['id']}".encode(), hashlib.sha256).hexdigest()[:32]


def _push_parts(ctype, body):
    """multipart / JSON / XML so'rovdan (hodisa-dict, rasm-bytes) ajratish."""
    from email.parser import BytesParser
    from email.policy import default as email_default
    event, pic = None, None
    parts = []
    if "multipart/" in ctype.lower():
        msg = BytesParser(policy=email_default).parsebytes(
            f"Content-Type: {ctype}\r\nMIME-Version: 1.0\r\n\r\n".encode() + body)
        for p in msg.iter_parts():
            parts.append((p.get_content_type(), p.get_param("name", header="content-disposition") or "",
                          p.get_payload(decode=True) or b""))
    else:
        parts.append((ctype, "", body))
    for ct, name, data in parts:
        if data[:2] == b"\xff\xd8" or ct.startswith("image/"):
            pic = pic or data
            continue
        txt = data.decode("utf-8", "replace").strip()
        if txt.startswith("{"):
            try:
                event = json.loads(txt)
            except ValueError:
                pass
        elif txt.startswith("<") and event is None:
            def g(k):
                m = re.search(f"<{k}>([^<]*)</{k}>", txt)
                return html.unescape(m.group(1)).strip() if m else None
            event = {"eventType": g("eventType"), "dateTime": g("dateTime"),
                     "AccessControllerEvent": {k: g(k) for k in ("majorEventType", "subEventType", "name",
                                                                 "employeeNoString", "serialNo", "attendanceStatus",
                                                                 "currentVerifyMode")}}
    return event, pic


# Uzatish (relay): terminal faqat bitta manzilga yubora oladi. Agar u ilgari boshqa tizimga (masalan oyliklar
# hisoblash) yuborgan bo'lsa — dashboard har bir so'rovni O'ZGARTIRMASDAN o'sha manzilga ham uzatadi.
FWD_Q = queue.Queue(maxsize=5000)
FWD_STATE = {}   # tid -> {"ok": n, "fail": n, "last_status": .., "last_at": ..}


def forward_url(tid):
    return (CFG.get("forward") or {}).get(str(tid))


class Forwarder(threading.Thread):
    daemon = True

    def run(self):
        while True:
            tid, url, ctype, body, tries = FWD_Q.get()
            st = FWD_STATE.setdefault(tid, {"ok": 0, "fail": 0})
            try:
                u = urlsplit(url)
                conn = (http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection)(
                    u.hostname, u.port, timeout=20)
                conn.request("POST", (u.path or "/") + ("?" + u.query if u.query else ""), body,
                             {"Content-Type": ctype, "Content-Length": str(len(body))})
                r = conn.getresponse()
                r.read()
                conn.close()
                code = r.status
            except Exception as e:
                code = f"xato: {e.__class__.__name__}"
            st.update(last_status=code, last_at=fmt_time(now_local()))
            if isinstance(code, int) and code < 500:
                st["ok" if code < 400 else "fail"] += 1
            elif tries < 5:
                threading.Timer(5 * (tries + 1), lambda a=(tid, url, ctype, body, tries + 1): FWD_Q.put(a)).start()
            else:
                st["fail"] += 1
                print(f"[uzatish] {url.split('?')[0][:40]}… yetkazilmadi: {code}", flush=True)


def set_forward(tid, token, b):
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not rows or not hmac.compare_digest(push_token(rows[0]), token):
        return 404, {"error": "topilmadi"}
    url = str(b.get("url") or "").strip()
    if url and not re.fullmatch(r"https://[\w.-]+(:\d+)?/[^\s]{0,200}", url):
        return 400, {"error": "Manzil https://... ko'rinishida bo'lsin"}
    fw = dict(CFG.get("forward") or {})
    if url:
        fw[str(tid)] = url
    else:
        fw.pop(str(tid), None)
    CFG["forward"] = fw
    save_config(CFG)
    return 200, {"ok": True, "forward": bool(url)}


class CloudSync(threading.Thread):
    """Ofisdagi nusxa -> bulut: terminaldan olingan o'tishlarni (rasmi bilan) bulut serveriga yetkazadi.
    Bulut qaysi vaqtgacha bilishini so'raydi va undan keyingilarni yuboradi — shuning uchun ofis kompyuteri
    yoki bulut bir muddat o'chiq bo'lsa ham, yoqilgach hammasi o'zi to'ldiriladi. Telegram'ni ofis yuboradi."""
    daemon = True

    def run(self):
        n = 0
        while True:
            try:
                if CFG.get("cloud_url") and not CLOUD and not DEMO:
                    for t in terminals(with_password=True):
                        if not t["active"]:
                            continue
                        self.jobs(t)                 # telefondan kelgan buyruqlar — har 4 soniyada
                        if n % 5 == 0:
                            self.sync(t)             # o'tishlar — har ~20 soniyada
            except Exception as e:
                print(f"[bulut] sinxron xatosi: {e}", flush=True)
            n += 1
            time.sleep(4)

    def jobs(self, t):
        t = {**t, **db.q("SELECT mac, serial FROM terminals WHERE id=?", (t["id"],))[0]}
        base = f"/hook/{t['id']}/{push_token(t)}"
        st, data = self._post(base + "/jobs", b"{}", {"Content-Type": "application/json"})
        if st != 200:
            return
        for j in json.loads(data or b"{}").get("jobs") or []:
            p = {**j["payload"], "terminal_id": t["id"]}
            try:
                code, res = enroll_person(p) if j["kind"] == "enroll" else remove_person(p)
            except Exception as e:
                code, res = 500, {"error": f"Ofis kompyuterida xato: {e}"}
            print(f"[bulut] buyruq #{j['id']} ({j['kind']} ID {p.get('emp')}): {code}", flush=True)
            self._post(base + "/jobresult", json.dumps({"id": j["id"], "code": code, "result": res},
                                                       ensure_ascii=False).encode("utf-8"),
                       {"Content-Type": "application/json"})

    @staticmethod
    def _post(path, body, headers):
        u = urlsplit(CFG["cloud_url"])
        conn = http.client.HTTPSConnection(u.hostname, u.port, timeout=60)
        conn.request("POST", path, body, headers)
        r = conn.getresponse()
        data = r.read()
        conn.close()
        return r.status, data

    def sync(self, t):
        t = {**t, **db.q("SELECT mac, serial FROM terminals WHERE id=?", (t["id"],))[0]}
        base = f"/hook/{t['id']}/{push_token(t)}"
        st, data = self._post(base + "/status", b'{"office": true}', {"Content-Type": "application/json"})
        if st != 200:
            return
        last = (json.loads(data or b"{}").get("last_event") or {}).get("time") or ""
        evs = db.q("SELECT * FROM events WHERE terminal_id=? AND time>? ORDER BY time LIMIT 200", (t["id"], last))
        for e in evs:
            ev = {"dateTime": e["time"], "eventType": "AccessControllerEvent",
                  "AccessControllerEvent": {"majorEventType": 5, "name": e["name"], "employeeNoString": e["emp"],
                                            "serialNo": e["serial"], "attendanceStatus": e["att_status"],
                                            "currentVerifyMode": e["verify"]}}
            b = "----sync" + uuid.uuid4().hex
            body = (f"--{b}\r\nContent-Disposition: form-data; name=\"event_log\"\r\n"
                    f"Content-Type: application/json\r\n\r\n{json.dumps(ev, ensure_ascii=False)}\r\n").encode()
            try:
                ph = get_photo(e["id"])
            except Exception:
                ph = None
            if ph and ph[1] == "image/jpeg":
                body += (f"--{b}\r\nContent-Disposition: form-data; name=\"Picture\"; filename=\"p.jpg\"\r\n"
                         f"Content-Type: image/jpeg\r\n\r\n").encode() + ph[0] + b"\r\n"
            body += f"--{b}--\r\n".encode()
            st, _ = self._post(base, body, {"Content-Type": f"multipart/form-data; boundary={b}",
                                            "X-Davomat-Replay": "1"})
            if st != 200:
                return


CLOUD_USERS_SENT = {}   # tid -> oxirgi yuborilgan ro'yxat (o'zgarmasa qayta yubormaymiz)


def send_users_to_cloud(tid, users, groups=None):
    """Ofisdagi nusxa: terminal foydalanuvchilari (va departamentlar) ro'yxatini bulut serveriga yuboradi."""
    key = json.dumps([sorted(users), groups or []], ensure_ascii=False)
    if CLOUD_USERS_SENT.get(tid) == key:
        return
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    u = urlsplit(CFG.get("cloud_url") or "")
    if not rows or u.scheme != "https" or not u.hostname:
        return
    try:
        conn = http.client.HTTPSConnection(u.hostname, u.port, timeout=20)
        conn.request("POST", f"/hook/{tid}/{push_token(rows[0])}/users",
                     json.dumps({"users": users, "groups": groups or []}, ensure_ascii=False).encode("utf-8"),
                     {"Content-Type": "application/json"})
        r = conn.getresponse()
        r.read()
        conn.close()
        if r.status == 200:
            CLOUD_USERS_SENT[tid] = key
    except Exception as e:
        print(f"[bulut] xodimlar ro'yxati yuborilmadi: {e}", flush=True)


def receive_users(tid, token, b):
    """Bulut: ofisdagi nusxadan terminal foydalanuvchilari ro'yxatini qabul qilish (to'liq ro'yxat)."""
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not rows or not hmac.compare_digest(push_token(rows[0]), token):
        return 404, {"error": "topilmadi"}
    users = b.get("users")
    if not isinstance(users, list) or len(users) > 5000:
        return 400, {"error": "noto'g'ri ro'yxat"}
    if isinstance(b.get("groups"), list) and len(b["groups"]) <= 256:
        store_term_groups(tid, b["groups"])
    keep = set()
    for item in users:
        try:
            emp, name = str(item[0]).strip()[:32], str(item[1] or "")[:64]
            gid = int(item[2]) if len(item) > 2 and item[2] is not None else None
        except (IndexError, TypeError, ValueError):
            continue
        if emp:
            upsert_term_user(tid, emp, name, gid)
            keep.add(emp)
    if keep:   # terminaldan o'chirilganlar ro'yxatdan ham olinadi (o'tishlari qoladi)
        for r in db.q("SELECT emp FROM term_users WHERE terminal_id=?", (tid,)):
            if r["emp"] not in keep:
                db.x("DELETE FROM term_users WHERE terminal_id=? AND emp=?", (tid, r["emp"]))
    return 200, {"ok": True, "count": len(keep)}


def add_term_user_manual(b):
    """Terminal ID sini qo'lda qo'shish (bulutda terminalga ulanib bo'lmaganda)."""
    try:
        tid = int(b.get("terminal_id") or 0)
    except ValueError:
        return 400, {"error": "Terminalni tanlang"}
    emp = str(b.get("emp") or "").strip()
    name = re.sub(r"\s+", " ", str(b.get("name") or "")).strip()[:64]
    if not db.q("SELECT 1 FROM terminals WHERE id=?", (tid,)):
        return 404, {"error": "Terminal topilmadi"}
    if not EMP_RE.match(emp):
        return 400, {"error": "Terminaldagi ID raqamini kiriting (masalan 8)"}
    upsert_term_user(tid, emp, name)
    return 200, {"ok": True}


def push_status(tid, token, office=False):
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not rows or not hmac.compare_digest(push_token(rows[0]), token):
        return 404, {"error": "topilmadi"}
    st = TSTATE.get(tid, {})
    if office:   # ofisdagi nusxa terminalni ko'rib turibdi va sinxronlayapti
        st = TSTATE.setdefault(tid, {})
        st.update(connected=True, error=None, need_login=False, push=True, office=True,
                  last_poll=fmt_time(now_local()))
    last = db.q("SELECT time, emp FROM events WHERE terminal_id=? ORDER BY time DESC LIMIT 1", (tid,))
    users = [r["emp"] for r in db.q("SELECT emp FROM term_users WHERE terminal_id=?", (tid,))]
    return 200, {"last_push": st.get("last_poll"), "connected": st.get("connected"), "forward": bool(forward_url(tid)),
                 "term_users": sorted(users),
                 "forward_state": FWD_STATE.get(tid, {}), "last_event": last[0] if last else None}


def handle_push(tid, token, ctype, body, replay=False):
    """replay=True — ofisdagi nusxadan yetishmagan eski o'tishni to'ldirish: uzatilmaydi, Telegram'ga yuborilmaydi."""
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not rows or not rows[0]["active"] or not hmac.compare_digest(push_token(rows[0]), token):
        return 404
    fwd = None if replay else forward_url(tid)
    if fwd and body:
        try:
            FWD_Q.put_nowait((tid, fwd, ctype, body, 0))
        except queue.Full:
            pass
    event, pic = _push_parts(ctype, body)
    if not replay:
        st = TSTATE.setdefault(tid, {})
        st.update(connected=True, error=None, need_login=False, push=True, last_poll=fmt_time(now_local()))
    if not event:
        return 200
    a = event.get("AccessControllerEvent") or {}
    emp = str(a.get("employeeNoString") or a.get("employeeNo") or "").strip()
    if event.get("eventType") != "AccessControllerEvent" or str(a.get("majorEventType")) != "5" or not emp:
        return 200   # yurak urishi (heartbeat) yoki o'tish bo'lmagan hodisa
    t = event.get("dateTime") or fmt_time(now_local())
    try:
        serial = int(a.get("serialNo"))
    except (TypeError, ValueError):
        serial = None
    eid = add_event(tid, {"employeeNoString": emp, "name": a.get("name") or "", "time": t, "serialNo": serial,
                          "attendanceStatus": a.get("attendanceStatus") or "",
                          "currentVerifyMode": a.get("currentVerifyMode") or ""})
    if eid:
        if pic and pic[:2] == b"\xff\xd8":
            s = db.q("SELECT serial FROM events WHERE id=?", (eid,))[0]["serial"]
            with open(os.path.join(PHOTOS, f"{tid}_{s}.jpg"), "wb") as f:
                f.write(pic)
        if not replay:
            tg_notify([eid])
    return 200


# ----------------------------------------------------------------- zaxira (boshqa kompyuter/serverga ko'chirish)
BACKUP_RE = re.compile(r"^(attendance\.db|config\.json|photos/[\w.-]+\.jpg|faces/[\w.-]+\.(jpg|none))$")


def make_backup():
    """Baza (izchil nusxa), config.json, rasmlar va yuzlar — bitta zip."""
    import zipfile
    buf = io.BytesIO()
    fd, tmp = tempfile.mkstemp(suffix=".db")
    os.close(fd)
    try:
        dst = sqlite3.connect(tmp)
        with db.lock:
            db.conn.backup(dst)
        dst.close()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
            z.write(tmp, "attendance.db")
            if os.path.exists(CONFIG_PATH):
                z.write(CONFIG_PATH, "config.json")
            for sub, folder in (("photos", PHOTOS), ("faces", FACES)):
                for f in sorted(os.listdir(folder)):
                    name = f"{sub}/{f}"
                    if BACKUP_RE.match(name):
                        z.write(os.path.join(folder, f), name, compress_type=zipfile.ZIP_STORED)
    finally:
        os.remove(tmp)
    return buf.getvalue()


def restore_backup(raw):
    """Zaxiradan tiklash: hozirgi baza, sozlamalar va rasmlar ALMASHTIRILADI."""
    import zipfile
    global db, CFG
    if DEMO:
        raise ValueError("Demo rejimida tiklab bo'lmaydi")
    try:
        z = zipfile.ZipFile(io.BytesIO(raw))
        names = [i.filename for i in z.infolist() if not i.is_dir()]
    except zipfile.BadZipFile:
        raise ValueError("Bu zaxira (zip) fayli emas")
    if "attendance.db" not in names:
        raise ValueError("Zaxirada attendance.db yo'q")
    bad = [n for n in names if not BACKUP_RE.match(n)]
    if bad:
        raise ValueError(f"Zaxirada notanish fayl bor: {bad[0]}")
    if sum(i.file_size for i in z.infolist()) > 2 * 1024 ** 3:
        raise ValueError("Zaxira juda katta")
    fd, tmp = tempfile.mkstemp(suffix=".db", dir=DATA)
    os.close(fd)
    with open(tmp, "wb") as f:
        f.write(z.read("attendance.db"))
    try:
        c = sqlite3.connect(tmp)
        ok = c.execute("PRAGMA integrity_check").fetchone()[0] == "ok" and \
            c.execute("SELECT 1 FROM sqlite_master WHERE name='terminals'").fetchone()
        accounts = c.execute("SELECT COUNT(*) FROM accounts").fetchone()[0] if ok else 0
        c.close()
    except sqlite3.DatabaseError:
        ok = False
    if not ok or not accounts:
        os.remove(tmp)
        raise ValueError("Zaxiradagi baza buzilgan yoki unda foydalanuvchi yo'q")
    with TERM_LOCK:
        for tid in list(POLLERS):
            stop_poller(tid)
        with db.lock:
            db.conn.close()
            os.replace(tmp, os.path.join(DATA, "attendance.db"))
        for sub, folder in (("photos", PHOTOS), ("faces", FACES)):
            for f in os.listdir(folder):
                os.remove(os.path.join(folder, f))
            for n in names:
                if n.startswith(sub + "/"):
                    with open(os.path.join(folder, n.split("/", 1)[1]), "wb") as f:
                        f.write(z.read(n))
        if "config.json" in names:
            cfg = dict(DEFAULTS)
            cfg.update(json.loads(z.read("config.json").decode("utf-8-sig")))
            save_config(cfg)
        CFG = load_config()
        db = DB(os.path.join(DATA, "attendance.db"))
        BILLZ_AUTH.update(token=None, at=0, secret=None)
        BILLZ_CACHE.clear()
        SD_SESS.update(cookies={}, user=None, host=None)
        SD_CACHE.clear()
        for t in terminals(with_password=True):
            start_poller(t)
    print(f"Zaxiradan tiklandi: {len(names)} ta fayl", flush=True)


# ----------------------------------------------------------------- terminalga xodim + Face ID yozish
EMP_RE = re.compile(r"^[0-9A-Za-z_-]{1,32}$")


def _isapi_err(j, st):
    sub = str(j.get("subStatusCode") or j.get("errorMsg") or j.get("statusString") or f"HTTP {st}")
    known = {
        "employeeNoAlreadyExist": "Bu ID terminalda band",
        "deviceUserAlreadyExistFace": "Bu odamning yuzi terminalda allaqachon bor",
        "faceDataModeling": "Rasmdan yuz modeli yasab bo'lmadi",
        "noFace": "Rasmda yuz topilmadi",
        "facePicQualityLow": "Rasm sifati past",
        "faceScoreLow": "Rasm sifati past",
        "multiFace": "Rasmda bir nechta yuz bor",
        "badPicSize": "Rasm o'lchami mos emas",
        "pictureSizeExceedLimit": "Rasm juda katta",
    }
    for k, v in known.items():
        if k.lower() in sub.lower():
            return f"{v} ({sub})"
    return sub


def _face_multipart(meta, img):
    b = "----davomat" + uuid.uuid4().hex
    body = (f"--{b}\r\nContent-Disposition: form-data; name=\"FaceDataRecord\"\r\n"
            f"Content-Type: application/json\r\n\r\n{json.dumps(meta)}\r\n"
            f"--{b}\r\nContent-Disposition: form-data; name=\"img\"; filename=\"face.jpg\"\r\n"
            f"Content-Type: image/jpeg\r\n\r\n").encode() + img + f"\r\n--{b}--\r\n".encode()
    return body, f"multipart/form-data; boundary={b}"


def _isapi_json(dev, method, path, obj=None, raw=None, ctype="application/json"):
    body = raw if raw is not None else json.dumps(obj).encode("utf-8")
    st, _, data = dev.request(method, path, body, ctype=ctype, fatal=False)
    try:
        j = json.loads(data.decode("utf-8", "replace") or "{}")
    except ValueError:
        j = {}
    return st, j


def _ok_isapi(st, j):
    return st == 200 and str(j.get("statusCode", 1)) == "1"


def _cache_face(tid, emp, img):
    safe = re.sub(r"[^\w-]", "_", emp)
    fp = os.path.join(FACES, f"{tid}_{safe}.jpg")
    for f in (fp, fp + ".none"):
        if os.path.exists(f):
            os.remove(f)
    if img:
        with open(fp, "wb") as f:
            f.write(img)


def enroll_person(b):
    """Terminalga yangi odam qo'shish yoki mavjudini yangilash (ism + yuz rasmi)."""
    try:
        tid = int(b.get("terminal_id") or 0)
    except ValueError:
        return 400, {"error": "Terminalni tanlang"}
    emp = str(b.get("emp") or "").strip()
    name = re.sub(r"\s+", " ", str(b.get("name") or "")).strip()
    edit = bool(b.get("edit"))
    try:
        gid = int(b.get("group_id") or 0)
    except (TypeError, ValueError):
        gid = 0
    img = None
    if b.get("photo"):
        try:
            img = base64.b64decode(str(b["photo"]).split(",", 1)[-1], validate=True)
        except Exception:
            return 400, {"error": "Rasm o'qilmadi"}
        if not img.startswith(b"\xff\xd8"):
            return 400, {"error": "Rasm JPEG formatida bo'lsin"}
        if len(img) > 200 * 1024:
            return 400, {"error": "Rasm 200 KB dan katta — kichikroq rasm tanlang"}
    t = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not t:
        return 404, {"error": "Terminal topilmadi"}
    t = t[0]
    if not t["active"]:
        return 409, {"error": f"{t['name']} terminali o'chirib qo'yilgan"}
    if not EMP_RE.match(emp):
        return 400, {"error": "ID raqami faqat raqam/harf bo'lsin (masalan 12)"}
    if not 1 <= len(name) <= 32:
        return 400, {"error": "Ism familiyani kiriting (32 belgigacha — terminal shuncha qabul qiladi)"}
    if not edit and not img:
        return 400, {"error": "Yuz rasmini qo'shing (kamera yoki fayl)"}
    groups = dict(term_groups(tid))
    if groups and gid not in groups:
        return 400, {"error": "Departamentni tanlang (xodim qaysi bo'limda ishlaydi)"}
    if not edit and db.q("SELECT 1 FROM term_users WHERE terminal_id=? AND emp=?", (tid, emp)):
        return 409, {"error": f"ID {emp} {t['name']} terminalida band. Boshqa raqam tanlang."}

    if CLOUD and not DEMO:
        # bulutdan terminalga ulanib bo'lmaydi — buyruq navbatga, uni ofis kompyuteri bajaradi
        return queue_job("enroll", tid, {**b, "emp": emp, "name": name, "group_id": gid})

    if not DEMO:
        dev = device_of(tid)
        if not dev or not TSTATE.get(tid, {}).get("connected"):
            return 502, {"error": f"{t['name']} terminaliga hozir ulanib bo'lmayapti. Biroz kutib qayta urining."}
        user = {"UserInfo": {"employeeNo": emp, "name": name, "userType": "normal",
                             "Valid": {"enable": True, "beginTime": "2020-01-01T00:00:00",
                                       "endTime": "2037-12-31T23:59:59", "timeType": "local"},
                             "doorRight": "1", "RightPlan": [{"doorNo": 1, "planTemplateNo": "1"}]}}
        if gid:
            user["UserInfo"]["groupId"] = gid   # departament (terminalda "Департамент")
        try:
            if edit:
                st, j = _isapi_json(dev, "PUT", "/ISAPI/AccessControl/UserInfo/Modify?format=json", user)
            else:
                st, j = _isapi_json(dev, "POST", "/ISAPI/AccessControl/UserInfo/Record?format=json", user)
            if not _ok_isapi(st, j):
                return 400, {"error": "Terminal xodimni qabul qilmadi: " + _isapi_err(j, st)}
            if img:
                meta = {"faceLibType": "blackFD", "FDID": "1", "FPID": emp}
                raw, ctype = _face_multipart(meta, img)
                st, j = _isapi_json(dev, "POST", "/ISAPI/Intelligent/FDLib/FaceDataRecord?format=json",
                                    raw=raw, ctype=ctype)
                if not _ok_isapi(st, j) and "exist" in str(j.get("subStatusCode", "")).lower():
                    raw, ctype = _face_multipart(meta, img)   # yuz bor edi — almashtiramiz
                    st, j = _isapi_json(dev, "PUT", "/ISAPI/Intelligent/FDLib/FDSetUp?format=json",
                                        raw=raw, ctype=ctype)
                if not _ok_isapi(st, j):
                    msg = "Xodim terminalga yozildi, lekin yuz rasmi qabul qilinmadi: " + _isapi_err(j, st) + \
                          ". Yuz aniq, yorug' joyda, to'g'ridan va yolg'iz tushgan rasm tanlang."
                    upsert_term_user(tid, emp, name, gid or None)
                    return 400, {"error": msg, "user_saved": True}
        except AuthError:
            return 403, {"error": "Terminal login/paroli noto'g'ri"}
        except Exception as e:
            return 502, {"error": f"Terminalga ulanib bo'lmadi: {e}"}
    _enroll_finish(tid, emp, name, img, b.get("staff_id"), gid)
    return 200, {"ok": True, "emp": emp}


def _enroll_finish(tid, emp, name, img, sid, gid=0):
    upsert_term_user(tid, emp, name, gid or None)
    if img:
        _cache_face(tid, emp, img)
    if sid == "new":
        dept = dict(term_groups(tid)).get(gid, "") if gid else ""
        sid = db.x("INSERT INTO staff(name, code, dept, created) VALUES(?,?,?,?)", (name, "", dept, fmt_time(now_local())))
    if sid not in (None, "", 0):
        db.x("INSERT OR REPLACE INTO links(terminal_id, emp, staff_id) VALUES(?,?,?)", (tid, emp, int(sid)))


# ----------------------------------------------------------------- bulut -> ofis buyruqlar navbati
# Bulut terminalga ulana olmaydi. Telefondan "terminalga yoz/o'chir" buyrug'i navbatga tushadi, ofisdagi nusxa
# uni olib terminalda bajaradi va natijani qaytaradi.
JOB_TTL = 30 * 60


def queue_job(kind, tid, payload):
    jid = db.x("INSERT INTO jobs(kind, terminal_id, payload, status, created) VALUES(?,?,?,?,?)",
               (kind, tid, json.dumps(payload, ensure_ascii=False), "pending", time.time()))
    return 202, {"queued": True, "job": jid}


def job_info(jid):
    db.x("UPDATE jobs SET status='error', result=? WHERE status='pending' AND created<?",
         (json.dumps({"error": "Ofis kompyuteri 30 daqiqa ichida javob bermadi. Kompyuter va dashboard yoqiqligini "
                               "tekshirib, qayta urining."}, ensure_ascii=False), time.time() - JOB_TTL))
    r = db.q("SELECT status, result, taken FROM jobs WHERE id=?", (jid,))
    if not r:
        return 404, {"error": "topilmadi"}
    r = r[0]
    return 200, {"status": r["status"], "taken": bool(r["taken"]), **json.loads(r["result"] or "{}")}


def jobs_for_office(tid, token):
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not rows or not hmac.compare_digest(push_token(rows[0]), token):
        return 404, {"error": "topilmadi"}
    now = time.time()
    out = []
    for j in db.q("SELECT id, kind, payload, taken FROM jobs WHERE terminal_id=? AND status='pending' AND created>? "
                  "ORDER BY id LIMIT 5", (tid, now - JOB_TTL)):
        if j["taken"] and now - j["taken"] < 120:
            continue
        db.x("UPDATE jobs SET taken=? WHERE id=?", (now, j["id"]))
        p = json.loads(j["payload"])
        p.pop("staff_id", None)   # xodimga bog'lash bulutda qilinadi
        out.append({"id": j["id"], "kind": j["kind"], "payload": p})
    return 200, {"jobs": out}


def job_result(tid, token, b):
    rows = db.q("SELECT * FROM terminals WHERE id=?", (tid,))
    if not rows or not hmac.compare_digest(push_token(rows[0]), token):
        return 404, {"error": "topilmadi"}
    j = db.q("SELECT * FROM jobs WHERE id=? AND terminal_id=?", (int(b.get("id") or 0), tid))
    if not j or j[0]["status"] != "pending":
        return 200, {"ok": True}
    j = j[0]
    p = json.loads(j["payload"])
    res = b.get("result") or {}
    ok = b.get("code") == 200
    if j["kind"] == "enroll" and (ok or res.get("user_saved")):
        img = base64.b64decode(str(p["photo"]).split(",", 1)[-1]) if p.get("photo") and ok else None
        _enroll_finish(tid, p["emp"], p["name"], img, p.get("staff_id"), int(p.get("group_id") or 0))
    if j["kind"] == "delete" and ok:
        db.x("DELETE FROM term_users WHERE terminal_id=? AND emp=?", (tid, p["emp"]))
        _cache_face(tid, p["emp"], None)
    db.x("UPDATE jobs SET status=?, result=? WHERE id=?",
         ("done" if ok else "error", json.dumps({"error": res.get("error")} if not ok else {}, ensure_ascii=False),
          j["id"]))
    return 200, {"ok": True}


def remove_person(b):
    """Terminaldan odamni (yuzi bilan) o'chiradi. Dashboarddagi eski o'tishlari qoladi."""
    try:
        tid, emp = int(b.get("terminal_id") or 0), str(b.get("emp") or "").strip()
    except ValueError:
        return 400, {"error": "Noto'g'ri so'rov"}
    if not EMP_RE.match(emp):
        return 400, {"error": "Noto'g'ri ID"}
    if CLOUD and not DEMO:
        return queue_job("delete", tid, {"terminal_id": tid, "emp": emp})
    if not DEMO:
        dev = device_of(tid)
        if not dev or not TSTATE.get(tid, {}).get("connected"):
            return 502, {"error": "Terminalga hozir ulanib bo'lmayapti"}
        try:
            st, j = _isapi_json(dev, "PUT", "/ISAPI/AccessControl/UserInfo/Delete?format=json",
                                {"UserInfoDelCond": {"EmployeeNoList": [{"employeeNo": emp}]}})
        except Exception as e:
            return 502, {"error": f"Terminalga ulanib bo'lmadi: {e}"}
        if not _ok_isapi(st, j):
            return 400, {"error": "Terminal o'chirmadi: " + _isapi_err(j, st)}
    db.x("DELETE FROM term_users WHERE terminal_id=? AND emp=?", (tid, emp))
    _cache_face(tid, emp, None)
    return 200, {"ok": True}


def terminals_info():
    out = []
    for t in terminals():
        st = TSTATE.get(t["id"], {})
        agg = db.q("SELECT COUNT(*) n, MAX(time) last FROM events WHERE terminal_id=?", (t["id"],))[0]
        users = db.q("SELECT COUNT(*) n FROM term_users WHERE terminal_id=?", (t["id"],))[0]["n"]
        out.append({**t, "connected": st.get("connected", False), "error": st.get("error"),
                    "need_login": st.get("need_login", False), "last_poll": st.get("last_poll"),
                    "model": (st.get("device") or {}).get("model", ""), "events_total": agg["n"],
                    "last_event": agg["last"], "users_total": users, "push": bool(st.get("push")),
                    "office": bool(st.get("office"))})
    return out


def staff_info():
    ctx = make_ctx()
    tn = ctx["tnames"]
    staff = []
    for s in db.q("SELECT id, name, code, dept FROM staff ORDER BY lower(name)"):
        s["links"] = [{"terminal_id": t, "terminal": tn.get(t, "?"), "emp": e, "tname": ctx["tusers"].get((t, e), "")}
                      for (t, e), sid in sorted(ctx["links"].items()) if sid == s["id"] and t in tn]
        s["tdept"] = dept_of(s["id"], ctx)
        staff.append(s)
    tusers = []
    for (t, e), name in sorted(ctx["tusers"].items(), key=lambda x: (x[0][0], x[0][1].zfill(12))):
        if t not in tn:
            continue
        sid = ctx["links"].get((t, e))
        tusers.append({"terminal_id": t, "terminal": tn[t], "emp": e, "name": name,
                       "staff_id": sid if sid in ctx["staff"] else None, "dept": ctx["tdept"].get((t, e), "")})
    act = {t["id"]: bool(t["active"]) for t in terminals()}
    return {"staff": staff, "term_users": tusers,
            "terminals": [{"id": k, "name": v, "active": act.get(k, True), "groups": term_groups(k)}
                          for k, v in sorted(tn.items())]}


def save_staff(b):
    sid = b.get("id")
    name = str(b.get("name") or "").strip()
    code = str(b.get("code") or "").strip()[:30]
    dept = str(b.get("dept") or "").strip()[:60]
    if not 1 <= len(name) <= 80:
        return 400, {"error": "Xodim ismini kiriting"}
    if sid:
        db.x("UPDATE staff SET name=?, code=?, dept=? WHERE id=?", (name, code, dept, sid))
    else:
        sid = db.x("INSERT INTO staff(name, code, dept, created) VALUES(?,?,?,?)",
                   (name, code, dept, fmt_time(now_local())))
    if isinstance(b.get("links"), list):
        db.x("DELETE FROM links WHERE staff_id=?", (sid,))
        for l in b["links"]:
            try:
                t, e = int(l["terminal_id"]), str(l["emp"])
            except Exception:
                continue
            db.x("INSERT OR REPLACE INTO links(terminal_id, emp, staff_id) VALUES(?,?,?)", (t, e, sid))
    return 200, {"ok": True, "id": sid}


def link_user(b):
    try:
        t, e = int(b["terminal_id"]), str(b["emp"])
    except Exception:
        return 400, {"error": "Noto'g'ri so'rov"}
    sid = b.get("staff_id")
    if sid == "new":
        name = (db.q("SELECT name FROM term_users WHERE terminal_id=? AND emp=?", (t, e)) or [{"name": ""}])[0]["name"]
        sid = db.x("INSERT INTO staff(name, code, dept, created) VALUES(?,?,?,?)",
                   (name or f"Xodim {e}", "", "", fmt_time(now_local())))
    if sid in (None, "", 0):
        db.x("DELETE FROM links WHERE terminal_id=? AND emp=?", (t, e))
    else:
        db.x("INSERT OR REPLACE INTO links(terminal_id, emp, staff_id) VALUES(?,?,?)", (t, e, int(sid)))
    return 200, {"ok": True}


def autolink():
    """Bog'lanmagan terminal foydalanuvchilarini ism bo'yicha mavjud xodimga ulaydi, bo'lmasa yangi xodim yaratadi."""
    ctx = make_ctx()
    by_name = {s["name"].strip().lower(): sid for sid, s in ctx["staff"].items()}
    n_link = n_new = 0
    for (t, e), name in sorted(ctx["tusers"].items()):
        if t not in ctx["tnames"] or ctx["links"].get((t, e)) in ctx["staff"]:
            continue
        key = (name or "").strip().lower()
        if key and key in by_name:
            sid = by_name[key]
            n_link += 1
        else:
            sid = db.x("INSERT INTO staff(name, code, dept, created) VALUES(?,?,?,?)",
                       (name or f"Xodim {e}", "", "", fmt_time(now_local())))
            if key:
                by_name[key] = sid
            n_new += 1
        db.x("INSERT OR REPLACE INTO links(terminal_id, emp, staff_id) VALUES(?,?,?)", (t, e, sid))
    return 200, {"ok": True, "linked": n_link, "created": n_new}


# ----------------------------------------------------------------- http
class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code, body, ctype="application/json; charset=utf-8", extra=None):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False).encode("utf-8")
        elif isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def token(self):
        c = SimpleCookie()
        try:
            c.load(self.headers.get("Cookie") or "")
        except Exception:
            return None
        return c["dsid"].value if "dsid" in c else None

    def session_user(self):
        tok = self.token()
        if not tok:
            return None
        r = db.q("SELECT s.username FROM sessions s JOIN accounts a ON a.username = s.username "
                 "WHERE s.token=? AND s.expires>?", (tok, time.time()))
        return r[0]["username"] if r else None

    def do_GET(self):
        u = urlsplit(self.path)
        p = u.path
        qs = {k: v[0] for k, v in parse_qs(u.query).items()}
        tid = int(qs["terminal"]) if qs.get("terminal", "").isdigit() else None
        try:
            if p in ("/", "/index.html"):
                with open(os.path.join(WEB, "index.html"), "rb") as f:
                    return self.send(200, f.read(), "text/html; charset=utf-8", {"Cache-Control": "no-cache"})
            user = self.session_user()
            if p == "/api/auth/status":
                has = bool(db.q("SELECT 1 FROM accounts LIMIT 1"))
                return self.send(200, {"authed": bool(user), "user": user, "setup_needed": not has})
            if not user:
                return self.send(401, {"error": "Avval tizimga kiring"})
            today = now_local().strftime("%Y-%m-%d")
            if p == "/api/state":
                return self.send(200, {"demo": DEMO, "today": today, "now": fmt_time(now_local()),
                                       "work_start": CFG.get("work_start"),
                                       "repeat_gap_seconds": CFG.get("repeat_gap_seconds"),
                                       "terminals": [{k: t[k] for k in ("id", "name", "host", "connected", "error",
                                                                         "need_login", "last_poll", "model",
                                                                         "events_total", "last_event", "active", "push",
                                                                         "office")}
                                                     for t in terminals_info()],
                                       "unlinked": unlinked_count(make_ctx())})
            if p == "/api/terminals":
                return self.send(200, {"terminals": [{k: v for k, v in t.items()} for t in terminals_info()]})
            if p == "/api/staff":
                return self.send(200, staff_info())
            if p == "/api/telegram":
                return self.send(200, tg_public())
            if p == "/api/billz":
                return self.send(200, billz_public())
            if p in ("/api/sales", "/api/sales/stock", "/api/sales/debts"):
                if not billz_cfg()["secret"]:
                    return self.send(200, {"connected": False})
                try:
                    if p == "/api/sales":
                        d1 = qs.get("from") or today
                        d2 = qs.get("to") or d1
                        if not (re.fullmatch(r"\d{4}-\d{2}-\d{2}", d1) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", d2)) or d2 < d1:
                            return self.send(400, {"error": "Sana noto'g'ri"})
                        return self.send(200, sales_report(d1, d2))
                    return self.send(200, stock_report() if p.endswith("stock") else debts_report())
                except BillzError as e:
                    return self.send(200, {"connected": True, "error": str(e)})
            if p == "/api/salesdoc":
                return self.send(200, sd_public())
            if p == "/api/expenses":
                if not sd_public()["connected"]:
                    return self.send(200, {"connected": False})
                d1 = qs.get("from") or today
                d2 = qs.get("to") or d1
                if not (re.fullmatch(r"\d{4}-\d{2}-\d{2}", d1) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", d2)) or d2 < d1:
                    return self.send(400, {"error": "Sana noto'g'ri"})
                if (datetime.strptime(d2, "%Y-%m-%d") - datetime.strptime(d1, "%Y-%m-%d")).days > 400:
                    return self.send(400, {"error": "Davr juda uzun (ko'pi bilan 1 yil)"})
                return self.send(200, expenses_report(d1, d2, fresh=qs.get("fresh") == "1"))
            if p == "/api/users":
                return self.send(200, {"users": db.q("SELECT username, created FROM accounts ORDER BY username"),
                                       "me": user})
            if p == "/api/feed":
                return self.send(200, feed(int(qs.get("after", 0))))
            if p == "/api/day":
                return self.send(200, day_summary(qs.get("date") or today, tid))
            if p == "/api/month":
                return self.send(200, month_summary(qs.get("month") or today[:7], tid))
            if p == "/api/person":
                g = day_groups(qs.get("date", ""), make_ctx(), tid).get(qs.get("key", ""))
                evs = [{"id": e["id"], "time": e["time"], "kind": e["kind"], "terminal": e["terminal"]}
                       for e in (g["evs"] if g else [])]
                return self.send(200, {"events": evs})
            m = re.fullmatch(r"/api/jobs/(\d+)", p)
            if m:
                return self.send(*job_info(int(m.group(1))))
            if p == "/api/backup.zip":
                data = make_backup()
                stamp = now_local().strftime("%Y-%m-%d_%H%M")
                return self.send(200, data, "application/zip",
                                 {"Content-Disposition": f'attachment; filename="davomat_zaxira_{stamp}.zip"',
                                  "Cache-Control": "no-store"})
            if p == "/api/export.csv":
                d1, d2 = qs.get("from") or today, qs.get("to") or today
                return self.send(200, export_csv(d1, d2, tid), "text/csv; charset=utf-8",
                                 {"Content-Disposition": f'attachment; filename="davomat_{d1}_{d2}.csv"'})
            m = re.fullmatch(r"/photo/(\d+)", p)
            if m:
                r = get_photo(int(m.group(1)))
                return self.send(200, r[0], r[1], {"Cache-Control": "private, max-age=86400"}) if r else self.send(404, b"", "text/plain")
            m = re.fullmatch(r"/face/([\w-]+)", p)
            if m:
                r = get_face(m.group(1))
                return self.send(200, r[0], r[1], {"Cache-Control": "private, max-age=600"}) if r else self.send(404, b"", "text/plain")
            self.send(404, {"error": "not found"})
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            self.send(500, {"error": str(e)})

    def client_ip(self):
        if CLOUD:  # proksi orqasida — haqiqiy IP X-Forwarded-For ning oxirgi (proksi qo'shgan) qiymati
            xff = [x.strip() for x in (self.headers.get("X-Forwarded-For") or "").split(",") if x.strip()]
            if xff:
                return xff[-1]
        return self.client_address[0]

    def do_POST(self):
        p = urlsplit(self.path).path
        if p == "/api/backup/restore":
            return self.restore_upload()
        m = re.fullmatch(r"/hook/(\d+)/([0-9a-f]{32})/(forward|status|users|jobs|jobresult)", p)
        if m:
            try:
                n = int(self.headers.get("Content-Length") or 0)
                b = json.loads(self.rfile.read(n).decode("utf-8") or "{}") if 0 <= n <= 1024 * 1024 else {}
            except Exception:
                return self.send(400, {"error": "Noto'g'ri so'rov"})
            tid, tok, what = int(m.group(1)), m.group(2), m.group(3)
            fn = {"forward": lambda: set_forward(tid, tok, b),
                  "status": lambda: push_status(tid, tok, office=b.get("office") is True),
                  "users": lambda: receive_users(tid, tok, b), "jobs": lambda: jobs_for_office(tid, tok),
                  "jobresult": lambda: job_result(tid, tok, b)}[what]
            return self.send(*fn())
        m = re.fullmatch(r"/hook/(\d+)/([0-9a-f]{32})", p)
        if m:
            try:
                n = int(self.headers.get("Content-Length") or 0)
                body = self.rfile.read(n) if 0 <= n <= 8 * 1024 * 1024 else b""
                code = handle_push(int(m.group(1)), m.group(2), self.headers.get("Content-Type") or "", body,
                                   replay=self.headers.get("X-Davomat-Replay") == "1")
            except Exception as e:
                print(f"[push] xato: {e}", flush=True)
                code = 200   # terminal qayta-qayta yubormasligi uchun
            return self.send(code, b"" if code != 200 else b"OK", "text/plain")
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(n).decode("utf-8") or "{}")
        except Exception:
            return self.send(400, {"error": "Noto'g'ri so'rov"})
        username = str(body.get("username") or "").strip()
        pw = str(body.get("password") or "")
        ip = self.client_ip()
        try:
            if p == "/api/auth/setup":
                with LOGIN_LOCK:
                    if db.q("SELECT 1 FROM accounts LIMIT 1"):
                        return self.send(403, {"error": "Foydalanuvchi allaqachon yaratilgan"})
                    err = validate_new(username, pw)
                    if err:
                        return self.send(400, {"error": err})
                    add_account(username, pw)
                return self.login_ok(username)
            if p == "/api/auth/login":
                cnt, until = FAILS.get(ip, [0, 0])
                if until > time.time():
                    return self.send(429, {"error": f"Ko'p xato urinish. {int(until - time.time()) + 1} soniyadan keyin qayta urining."})
                if not username or not pw:
                    return self.send(400, {"error": "Login va parolni kiriting"})
                if not check_pw(username, pw):
                    cnt += 1
                    FAILS[ip] = [0, time.time() + 60] if cnt >= 5 else [cnt, 0]
                    return self.send(401, {"error": "Login yoki parol noto'g'ri"})
                FAILS.pop(ip, None)
                return self.login_ok(username)
            if p == "/api/auth/logout":
                tok = self.token()
                if tok:
                    db.x("DELETE FROM sessions WHERE token=?", (tok,))
                return self.send(200, {"ok": True}, extra=session_cookie("", 0))

            me = self.session_user()
            if not me:
                return self.send(401, {"error": "Avval tizimga kiring"})
            if p == "/api/users/add":
                err = validate_new(username, pw)
                if err:
                    return self.send(400, {"error": err})
                if db.q("SELECT 1 FROM accounts WHERE username=?", (username,)):
                    return self.send(409, {"error": "Bunday login bor"})
                add_account(username, pw)
                return self.send(200, {"ok": True})
            if p == "/api/users/delete":
                if username == me:
                    return self.send(400, {"error": "O'zingizni o'chira olmaysiz"})
                db.x("DELETE FROM accounts WHERE username=?", (username,))
                db.x("DELETE FROM sessions WHERE username=?", (username,))
                return self.send(200, {"ok": True})
            if p == "/api/users/password":
                if not check_pw(me, str(body.get("old_password") or "")):
                    return self.send(403, {"error": "Joriy parol noto'g'ri"})
                if len(pw) < 6:
                    return self.send(400, {"error": "Yangi parol kamida 6 belgi bo'lsin"})
                salt, h = hash_pw(pw)
                db.x("UPDATE accounts SET salt=?, hash=? WHERE username=?", (salt, h, me))
                return self.send(200, {"ok": True})
            if p == "/api/terminals/save":
                if not LOGIN_LOCK.acquire(blocking=False):
                    return self.send(409, {"error": "Tekshirilmoqda, kuting…"})
                try:
                    return self.send(*save_terminal(body))
                finally:
                    LOGIN_LOCK.release()
            if p == "/api/terminals/delete":
                return self.send(*delete_terminal(int(body.get("id") or 0)))
            if p == "/api/terminals/active":
                return self.send(*set_terminal_active(int(body.get("id") or 0), bool(body.get("active"))))
            if p == "/api/terminals/discover":
                return self.send(200, discover_info())
            if p == "/api/terminals/person":
                return self.send(*enroll_person(body))
            if p == "/api/terminals/person/delete":
                return self.send(*remove_person(body))
            if p == "/api/terminals/user/add":
                return self.send(*add_term_user_manual(body))
            if p == "/api/staff/save":
                return self.send(*save_staff(body))
            if p == "/api/staff/delete":
                sid = int(body.get("id") or 0)
                db.x("DELETE FROM staff WHERE id=?", (sid,))
                db.x("DELETE FROM links WHERE staff_id=?", (sid,))
                return self.send(200, {"ok": True})
            if p == "/api/staff/link":
                return self.send(*link_user(body))
            if p == "/api/staff/autolink":
                return self.send(*autolink())
            if p == "/api/billz/link":
                return self.send(*billz_link_seller(body))
            if p == "/api/salesdoc/save":
                try:
                    return self.send(*sd_save(body))
                except SalesDocError as e:
                    return self.send(400, {"error": str(e)})
            if p == "/api/billz/save":
                try:
                    return self.send(*billz_save(body))
                except BillzError as e:
                    return self.send(400, {"error": str(e)})
            if p.startswith("/api/telegram/"):
                try:
                    if p == "/api/telegram/save":
                        return self.send(*tg_save(body))
                    if p == "/api/telegram/find_chats":
                        return self.send(*tg_find_chats())
                    if p == "/api/telegram/test":
                        return self.send(*tg_test())
                except TgError as e:
                    return self.send(502, {"error": str(e)})
            if p == "/api/settings":
                ws = str(body.get("work_start") or "")
                if not re.fullmatch(r"([01]\d|2[0-3]):[0-5]\d", ws):
                    return self.send(400, {"error": "Vaqt HH:MM ko'rinishida bo'lsin"})
                try:
                    gap = max(0, min(3600, int(body.get("repeat_gap_seconds", 60))))
                except ValueError:
                    return self.send(400, {"error": "Takror oralig'i raqam bo'lsin"})
                CFG["work_start"], CFG["repeat_gap_seconds"] = ws, gap
                save_config(CFG)
                return self.send(200, {"ok": True})
            self.send(404, {"error": "not found"})
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            self.send(500, {"error": str(e)})

    def restore_upload(self):
        # Yangi (hali foydalanuvchisi yo'q) serverga ko'chirish: birinchi zaxirani loginsiz qabul qilamiz —
        # xuddi "birinchi admin yaratish" sahifasi kabi. Foydalanuvchi bo'lgach — faqat login bilan.
        fresh = not db.q("SELECT 1 FROM accounts LIMIT 1")
        if not fresh and not self.session_user():
            return self.send(401, {"error": "Avval tizimga kiring"})
        try:
            n = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            n = 0
        if not 0 < n <= 500 * 1024 * 1024:
            return self.send(400, {"error": "Zaxira fayli bo'sh yoki juda katta"})
        raw = self.rfile.read(n)
        try:
            restore_backup(raw)
        except ValueError as e:
            return self.send(400, {"error": str(e)})
        return self.send(200, {"ok": True}, extra=session_cookie("", 0))

    def login_ok(self, username):
        tok = secrets.token_urlsafe(32)
        db.x("DELETE FROM sessions WHERE expires<?", (time.time(),))
        db.x("INSERT INTO sessions(token, username, expires) VALUES(?,?,?)",
             (tok, username, time.time() + SESSION_DAYS * 86400))
        return self.send(200, {"ok": True, "user": username}, extra=session_cookie(tok, SESSION_DAYS * 86400))


def main():
    global db, CFG
    os.makedirs(DATA, exist_ok=True)
    CFG = load_config()
    os.makedirs(PHOTOS, exist_ok=True)
    os.makedirs(FACES, exist_ok=True)
    db = DB(os.path.join(DATA, "demo.db" if DEMO else "attendance.db"))
    TgWorker().start()
    Forwarder().start()
    CloudSync().start()
    if DEMO:
        demo_setup()
        DemoGen().start()
    else:
        # eski config.json dagi bitta terminalni bazaga ko'chirish
        if not db.q("SELECT 1 FROM terminals") and CFG.get("device_host"):
            db.x("INSERT INTO terminals(id, name, host, port, username, password, created) VALUES(1,?,?,?,?,?,?)",
                 (CFG.get("device_name") or "SKLAD", CFG["device_host"], CFG.get("device_port", 80),
                  CFG.get("username") or "admin", CFG.get("password") or "", fmt_time(now_local())))
            for k in ("device_host", "device_port", "username", "password"):
                CFG.pop(k, None)
            save_config(CFG)
            print("Terminal sozlamalari bazaga ko'chirildi.")
        for t in terminals(with_password=True):
            start_poller(t)
    host, port = CFG["listen_host"], CFG["listen_port"]
    if CLOUD:
        host, port = "0.0.0.0", int(os.environ["PORT"])
    for a in sys.argv:
        if a.startswith("--port="):
            port = int(a.split("=", 1)[1])
    srv = ThreadingHTTPServer((host, port), Handler)
    url = f"http://{'localhost' if host in ('0.0.0.0', '127.0.0.1') else host}:{port}"
    print(f"Dashboard: {url}   (to'xtatish: Ctrl+C)")
    if "--no-browser" not in sys.argv and not CLOUD:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
