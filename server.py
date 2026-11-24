#!/usr/bin/env python3
"""
Davomat dashboard — Hikvision Face Recognition terminallari (ISAPI) uchun.
Bir nechta terminal (masalan SKLAD, OFIS), xodimlar va terminal ID larini xodimga bog'lash.

Ishga tushirish:   python server.py          (haqiqiy terminallar bilan)
                   python server.py --demo   (terminalsiz, sinov ma'lumotlari bilan)
Qo'shimcha:        --no-browser   --port=8090

Faqat Python standart kutubxonasi ishlatiladi — hech narsa o'rnatish shart emas.
"""
import calendar
import csv
import hashlib
import html
import http.client
import io
import queue
import json
import os
import random
import re
import secrets
import sqlite3
import sys
import threading
import time
import uuid
import webbrowser
from datetime import datetime, timedelta
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlsplit

BASE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(BASE, "data")
PHOTOS = os.path.join(DATA, "photos")
FACES = os.path.join(DATA, "faces")
WEB = os.path.join(BASE, "web")
CONFIG_PATH = os.path.join(BASE, "config.json")

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
                "firmware": g("firmwareVersion")}


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
            """)
            if legacy:
                # eski (bitta terminalli) bazani ko'chirish: hamma eski o'tishlar 1-terminalga tegishli
                c.execute("INSERT INTO events(id, terminal_id, serial, time, date, emp, name, att_status, verify, "
                          "picture_url) SELECT id, 1, serial, time, date, emp, name, att_status, verify, picture_url "
                          "FROM events_old")
                c.execute("DROP TABLE events_old")
                if c.execute("SELECT name FROM sqlite_master WHERE name='users'").fetchone():
                    c.execute("INSERT OR IGNORE INTO term_users SELECT 1, emp, name FROM users")
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
    cols = "id, name, host, port, username, created" + (", password" if with_password else "")
    return db.q(f"SELECT {cols} FROM terminals ORDER BY id")


def term_names():
    return {t["id"]: t["name"] for t in db.q("SELECT id, name FROM terminals")}


def upsert_term_user(tid, emp, name):
    db.x("INSERT INTO term_users(terminal_id, emp, name) VALUES(?,?,?) ON CONFLICT(terminal_id, emp) DO UPDATE "
         "SET name=CASE WHEN excluded.name!='' THEN excluded.name ELSE term_users.name END", (tid, emp, name or ""))


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
                    upsert_term_user(self.tid, emp, u.get("name", ""))
            pos += len(lst)
            if s.get("responseStatusStrg") != "MORE" or not lst:
                break
        self.users_at = time.time()

    def poll_once(self):
        if not self.state.get("device"):
            self.state["device"] = self.device.info()
        if time.time() - self.users_at > 600:
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

    def run(self):
        while not self.stopped:
            try:
                self.poll_once()
                self.state.update(connected=True, error=None, need_login=False, last_poll=fmt_time(now_local()))
            except AuthError as e:
                self.state.update(connected=False, need_login=True,
                                  error=f"{e}. Sozlamalar → Terminallar bo'limida login/parolni yangilang.")
                return
            except Exception as e:
                self.state.update(connected=False, error=f"Terminalga ulanib bo'lmadi: {e}")
                time.sleep(5)
            time.sleep(CFG.get("poll_seconds", 2))


def start_poller(t):
    stop_poller(t["id"])
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
    return p.device if p else None


# ----------------------------------------------------------------- shaxs aniqlash (terminal ID -> xodim)
def make_ctx():
    return {
        "staff": {s["id"]: s for s in db.q("SELECT id, name, code, dept FROM staff")},
        "links": {(l["terminal_id"], l["emp"]): l["staff_id"] for l in db.q("SELECT * FROM links")},
        "tusers": {(u["terminal_id"], u["emp"]): u["name"] for u in db.q("SELECT * FROM term_users")},
        "tnames": term_names(),
    }


def person_of(tid, emp, ctx, ev_name=""):
    sid = ctx["links"].get((tid, emp))
    s = ctx["staff"].get(sid)
    if s:
        return {"key": f"s{sid}", "name": s["name"], "code": s["code"] or "", "dept": s["dept"] or "", "linked": True}
    return {"key": f"t{tid}-{emp}", "name": ctx["tusers"].get((tid, emp)) or ev_name or "",
            "code": f"{ctx['tnames'].get(tid, '?')} · ID {emp}", "dept": "", "linked": False}


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
    w.writerow(["Sana", "Xodim", "Tabel / ID", "Bo'lim", "Keldi", "Keldi (terminal)", "Ketdi", "Ketdi (terminal)",
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
            ts = terminals()
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
    return {"Set-Cookie": f"dsid={tok}; HttpOnly; SameSite=Strict; Path=/; Max-Age={max_age}"}


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


def terminals_info():
    out = []
    for t in terminals():
        st = TSTATE.get(t["id"], {})
        agg = db.q("SELECT COUNT(*) n, MAX(time) last FROM events WHERE terminal_id=?", (t["id"],))[0]
        users = db.q("SELECT COUNT(*) n FROM term_users WHERE terminal_id=?", (t["id"],))[0]["n"]
        out.append({**t, "connected": st.get("connected", False), "error": st.get("error"),
                    "need_login": st.get("need_login", False), "last_poll": st.get("last_poll"),
                    "model": (st.get("device") or {}).get("model", ""), "events_total": agg["n"],
                    "last_event": agg["last"], "users_total": users})
    return out


def staff_info():
    ctx = make_ctx()
    tn = ctx["tnames"]
    staff = []
    for s in db.q("SELECT id, name, code, dept FROM staff ORDER BY lower(name)"):
        s["links"] = [{"terminal_id": t, "terminal": tn.get(t, "?"), "emp": e, "tname": ctx["tusers"].get((t, e), "")}
                      for (t, e), sid in sorted(ctx["links"].items()) if sid == s["id"] and t in tn]
        staff.append(s)
    tusers = []
    for (t, e), name in sorted(ctx["tusers"].items(), key=lambda x: (x[0][0], x[0][1].zfill(12))):
        if t not in tn:
            continue
        sid = ctx["links"].get((t, e))
        tusers.append({"terminal_id": t, "terminal": tn[t], "emp": e, "name": name,
                       "staff_id": sid if sid in ctx["staff"] else None})
    return {"staff": staff, "term_users": tusers, "terminals": [{"id": k, "name": v} for k, v in sorted(tn.items())]}


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
                                                                         "events_total", "last_event")}
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

    def do_POST(self):
        p = urlsplit(self.path).path
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(n).decode("utf-8") or "{}")
        except Exception:
            return self.send(400, {"error": "Noto'g'ri so'rov"})
        username = str(body.get("username") or "").strip()
        pw = str(body.get("password") or "")
        ip = self.client_address[0]
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

    def login_ok(self, username):
        tok = secrets.token_urlsafe(32)
        db.x("DELETE FROM sessions WHERE expires<?", (time.time(),))
        db.x("INSERT INTO sessions(token, username, expires) VALUES(?,?,?)",
             (tok, username, time.time() + SESSION_DAYS * 86400))
        return self.send(200, {"ok": True, "user": username}, extra=session_cookie(tok, SESSION_DAYS * 86400))


def main():
    global db, CFG
    CFG = load_config()
    os.makedirs(PHOTOS, exist_ok=True)
    os.makedirs(FACES, exist_ok=True)
    db = DB(os.path.join(DATA, "demo.db" if DEMO else "attendance.db"))
    TgWorker().start()
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
    for a in sys.argv:
        if a.startswith("--port="):
            port = int(a.split("=", 1)[1])
    srv = ThreadingHTTPServer((host, port), Handler)
    url = f"http://{'localhost' if host in ('0.0.0.0', '127.0.0.1') else host}:{port}"
    print(f"Dashboard: {url}   (to'xtatish: Ctrl+C)")
    if "--no-browser" not in sys.argv:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
