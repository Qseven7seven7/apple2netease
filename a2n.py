#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
a2n（本地音乐爬取工具）—— 把 Apple Music 歌单导入网易云音乐

用法:
  python3 a2n.py list  "~/Music/Music Library.xml"        列出资料库里所有歌单
  python3 a2n.py login                                    扫码登录网易云，保存 cookie
  python3 a2n.py run   "~/Music/Music Library.xml"        全流程：匹配 → 报告 → 导入
  python3 a2n.py run   "~/Music/Music Library.xml" --playlist "我的最爱" --dry-run

只要标准库即可运行；二维码登录额外需要 qrcode（.venv 里已装好）。
"""

from __future__ import annotations

import argparse
import binascii
import csv
import difflib
import json
import os
import plistlib
import random
import re
import string
import subprocess
import sys
import threading
import time
import unicodedata
from concurrent.futures import ThreadPoolExecutor, as_completed
import urllib.error
import urllib.parse
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
COOKIE_FILE = os.path.join(HERE, ".a2n_cookies.json")
CACHE_FILE = os.path.join(HERE, ".a2n_cache.json")

UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 "
      "(KHTML, like Gecko) Version/17.0 Safari/605.1.15")

BASE = "https://music.163.com"

# ── 网易云 weapi 加密（登录等接口必须，否则返回 401 无权限访问. ENC）──
# 算法固定：JSON → AES-128-CBC(NONCE) → base64 → AES-128-CBC(随机16位密钥) → base64，
# 随机密钥再用 RSA 公钥加密成 encSecKey。AES 直接借道系统 openssl，省一个依赖。
_W_MODULUS = (
    "00e0b509f6259df8642dbc35662901477df22677ec152b5ff68ace615bb7b725"
    "152b3ab17a876aea8a5aa76d2e417629ec4ee341f56135fccf695280104e03"
    "12ecbda92557c93870114af6c9d05c4f7f0c3685b7a46bee255932575cce10"
    "b424d813cfe4875d3e82047b97ddef52741d546b8e289dc6935b3ece0462db0a22b8e7")
_W_PUBKEY = "010001"
_W_NONCE = "0CoJUm6Qyw8W8jud"
_W_IV = "0102030405060708"


def _aes_b64(text: str, key: str) -> str:
    """AES-128-CBC 加密后 base64（用系统 openssl，避免引入 pycryptodome）。"""
    p = subprocess.run(
        ["openssl", "enc", "-aes-128-cbc",
         "-K", binascii.hexlify(key.encode()).decode(),
         "-iv", binascii.hexlify(_W_IV.encode()).decode(),
         "-base64", "-A"],
        input=text.encode("utf-8"), capture_output=True)
    if p.returncode != 0:
        raise RuntimeError("openssl 加密失败: %s" % p.stderr.decode()[:200])
    return p.stdout.decode().strip()


def _rsa_encrypt(secret: str) -> str:
    """把 16 位随机密钥倒序后做裸 RSA，输出 256 位十六进制。"""
    rev = secret[::-1].encode()
    n = int(_W_MODULUS, 16)
    e = int(_W_PUBKEY, 16)
    return format(pow(int(binascii.hexlify(rev), 16), e, n), "x").zfill(256)


def _norm_song(s: dict) -> dict:
    """cloudsearch 返回 ar/al/dt，老 search 返回 artists/album/duration，统一成后者。"""
    if not s.get("artists") and s.get("ar"):
        s["artists"] = [{"name": a.get("name", "")} for a in s["ar"]]
    if not s.get("album") and s.get("al"):
        s["album"] = {"name": (s["al"] or {}).get("name", "")}
    if not s.get("duration") and s.get("dt"):
        s["duration"] = s["dt"]
    return s


def _slim(s: dict) -> dict:
    """只保留匹配用得上的字段。

    网易云每条查询返回 20 个完整歌曲对象（含大量用不到的字段），
    直接缓存会让文件涨到 100MB+，而每存一次都要把整个缓存重新序列化一遍，
    随着缓存变大耗时线性增长 —— 实测跑 1344 首后彻底卡死。
    """
    return {
        "id": s.get("id"),
        "name": s.get("name", ""),
        "artists": [{"name": a.get("name", "")}
                    for a in (s.get("artists") or [])],
        "album": {"name": ((s.get("album") or {}).get("name") or "")},
        "duration": s.get("duration") or 0,
    }



# 默认跳过的系统歌单（名称归一化后比对）
SKIP_NAMES = {
    "音乐库", "资料库", "library", "下载", "downloaded", "最近添加", "recently added",
    "最近播放", "recently played", "音乐视频", "music videos", "电视节目",
    "tv shows", "有声读物", "audiobooks", "语音备忘录", "voice memos",
    "购买", "purchased", "上次播放", "apple music", "自动添加到我的最爱",
    "音乐", "music",      # 整库的镜像歌单，默认别整个导入
}

ALLOW_NAMES = {  # 虽然是系统歌单，但用户通常想要
    "我的最爱", "favorite songs", "favourites", "最爱",
}


# ─────────────────────────── 工具函数 ───────────────────────────

def norm(s: str) -> str:
    """归一化：全角转半角、去括号内容、去 feat、只留字母数字汉字。"""
    s = unicodedata.normalize("NFKC", s or "").lower()
    s = re.sub(r"\(.*?\)|\[.*?\]|（.*?）|【.*?】", " ", s)
    s = re.sub(r"\b(feat|ft|with|prod)\.?\s.*$", " ", s)
    s = re.sub(r"[^0-9a-z\u4e00-\u9fff]+", " ", s)
    return " ".join(s.split())


def sim(a: str, b: str) -> float:
    if not a or not b:
        return 0.0
    return difflib.SequenceMatcher(None, a, b).ratio()


def split_artists(s: str):
    """'A, B & C' → ['a','b','c']（已归一化）"""
    parts = re.split(r"[,&/、;]| feat\.? | ft\.? | with ", s or "", flags=re.I)
    return [norm(p) for p in parts if norm(p)]


def human(ms) -> str:
    if not ms:
        return "-"
    s = int(ms) // 1000
    return "%d:%02d" % (s // 60, s % 60)


# ─────────────────────────── 数据源：Apple Music ───────────────────────────

class Track:
    __slots__ = ("name", "artist", "album", "duration")

    def __init__(self, name, artist, album="", duration=0):
        self.name = name or ""
        self.artist = artist or ""
        self.album = album or ""
        self.duration = int(duration or 0)

    def __repr__(self):
        return "<%s - %s>" % (self.name, self.artist)


def load_library_xml(path: str):
    """解析 Music.app 导出的『资料库.xml』，返回 {歌单名: [Track]}"""
    with open(path, "rb") as f:
        pl = plistlib.load(f)

    tracks = pl.get("Tracks") or {}
    tracks = {str(k): v for k, v in tracks.items()}   # 防御：键统一成字符串
    playlists = pl.get("Playlists") or []
    out = {}

    for pl_entry in playlists:
        if pl_entry.get("Folder"):          # 文件夹，不是歌单
            continue
        name = pl_entry.get("Name")
        if not name:
            continue
        items = pl_entry.get("Playlist Items") or []
        tks = []
        for it in items:
            tid = it.get("Track ID")
            t = tracks.get(tid) or tracks.get(str(tid))
            if not t:
                continue
            if t.get("Kind") and "video" in str(t.get("Kind")).lower():
                continue
            tks.append(Track(
                name=t.get("Name", ""),
                artist=t.get("Artist") or t.get("Album Artist", ""),
                album=t.get("Album", ""),
                duration=t.get("Total Time", 0),
            ))
        if tks:
            out[name] = tks
    return out


def load_tsv(path: str):
    """从纯文本/TSV 读歌单（⌘A ⌘C 粘贴到 Music.app 或直接手写）。
    每行: 歌名 <TAB> 歌手 [<TAB> 专辑]；也支持 '歌名 - 歌手'。"""
    name = os.path.splitext(os.path.basename(path))[0]
    tks = []
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip():
                continue
            if "\t" in line:
                p = line.split("\t")
            elif " - " in line:                  # '歌名 - 歌手'
                a, b = line.split(" - ", 1)
                p = [a, b]
            else:
                p = [line]
            tks.append(Track(
                name=p[0].strip(),
                artist=p[1].strip() if len(p) > 1 else "",
                album=p[2].strip() if len(p) > 2 else "",
            ))
    return {name: tks}


OSA_SCRIPT = r'''
with timeout of 3600 seconds
tell application "Music"
  set d1 to character id 1
  set d2 to character id 2
  set out to ""
  repeat with p in playlists
    set cnt to 0
    try
      set cnt to (count of tracks of p)
    end try
    if cnt > 0 then
      set ns to name of every track of p
      set ars to artist of every track of p
      set als to album of every track of p
      set dys to duration of every track of p
      set AppleScript's text item delimiters to d1
      set a to ns as text
      set b to ars as text
      set c to als as text
      set e to dys as text
      set AppleScript's text item delimiters to ""
      set out to out & "###" & (name of p) & d2 & a & d2 & b & d2 & c & d2 & e & linefeed
    end if
  end repeat
  return out
end tell
end timeout
'''

S1, S2 = "\x01", "\x02"


def load_music_app():
    """直接通过 AppleScript 从 Music.app 读歌单，不需要先导出 XML。

    做法是每个歌单一次性取「全部歌名/歌手/专辑/时长」四个列表（各一次 Apple 事件），
    而不是逐首取属性 —— 3623 首也只要 0.7 秒。
    """
    p = subprocess.run(["osascript", "-e", OSA_SCRIPT],
                       capture_output=True, text=True, timeout=600)
    if p.returncode != 0:
        sys.exit("读取 Music.app 失败：%s\n"
                 "若提示没有权限，去 系统设置 → 隐私与安全性 → 自动化 里允许本程序控制「音乐」。"
                 % (p.stderr.strip() or "未知错误"))

    out = {}
    for line in p.stdout.split("\n"):
        if not line.startswith("###"):
            continue
        parts = line[3:].split(S2)
        if len(parts) < 5:
            continue
        names = parts[1].split(S1)
        artists = parts[2].split(S1)
        albums = parts[3].split(S1)
        durs = parts[4].split(S1)
        tks = []
        for i, n in enumerate(names):
            if not n.strip():
                continue
            try:                       # Music.app 的 duration 单位是秒
                d = int(round(float(durs[i].replace(",", ".")) * 1000))
            except (ValueError, IndexError):
                d = 0
            tks.append(Track(
                name=n,
                artist=artists[i] if i < len(artists) else "",
                album=albums[i] if i < len(albums) else "",
                duration=d))
        if tks:
            out[parts[0]] = tks
    return out


def load_any(path: str):
    if not path:                       # 不给文件就直接读 Music.app
        return load_music_app()
    path = os.path.expanduser(path)
    if not os.path.exists(path):
        sys.exit("找不到文件: %s" % path)
    if path.lower().endswith((".xml", ".plist")):
        return load_library_xml(path)
    return load_tsv(path)


def write_png(path, matrix, scale=8, border=4):
    """把布尔矩阵写成 PNG。纯标准库（zlib+struct），不需要 Pillow。"""
    import struct
    import zlib

    n = len(matrix)
    size = (n + border * 2) * scale
    raw = bytearray()
    for y in range(size):
        raw.append(0)                       # 每行的 filter type
        my = y // scale - border
        inside_y = 0 <= my < n
        for x in range(size):
            mx = x // scale - border
            black = inside_y and 0 <= mx < n and matrix[my][mx]
            raw.extend(b"\x00\x00\x00" if black else b"\xff\xff\xff")

    def chunk(tag, data):
        return (struct.pack(">I", len(data)) + tag + data
                + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF))

    png = b"\x89PNG\r\n\x1a\n"
    png += chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 2, 0, 0, 0))
    png += chunk(b"IDAT", zlib.compress(bytes(raw), 9))
    png += chunk(b"IEND", b"")
    with open(path, "wb") as f:
        f.write(png)
    return size


def make_qr_png(url, path):
    """生成二维码 PNG；返回 True 表示成功。"""
    import qrcode
    qr = qrcode.QRCode(border=0, error_correction=qrcode.constants.ERROR_CORRECT_M)
    qr.add_data(url)
    qr.make(fit=True)
    write_png(path, qr.get_matrix())
    return True


# ─────────────────────────── 网易云客户端 ───────────────────────────

class Netease:
    def __init__(self, min_gap=0.9):
        self.cookies = {}
        self.uid = None
        self.nickname = None
        # 自适应节流：网易云对密集请求返回 code=406，命中就自动放慢
        self.min_gap = min_gap
        self._floor = min_gap
        self._ceiling = 20.0
        self._last = 0.0
        self.hits = 0            # 缓存命中数
        self.fetched = 0         # 实际发出的搜索请求数
        self.qr_path = None      # 最近一次生成的二维码图片路径
        self._cache = {}
        self._cache_dirty = False
        self._lock = threading.RLock()   # 并发时保护节流器和缓存写盘
        self._load_cookies()
        self._load_cache()

    def _throttle(self):
        # 持锁睡眠：让请求“发起时刻”严格按 min_gap 排开。
        # 多线程下这样既能限速，又能让多个请求同时在途（突破单连接延迟瓶颈）。
        with self._lock:
            gap = time.time() - self._last
            if gap < self.min_gap:
                time.sleep(self.min_gap - gap)
            self._last = time.time()

    def _slow_down(self):
        with self._lock:
            # 翻倍式放慢：一被限流就快速退到安全区，别一格一格试
            self.min_gap = min(max(self.min_gap * 2.0, 2.0), self._ceiling)

    def _speed_up(self):
        with self._lock:
            # 只有拿到 200 才恢复，每次砍 20%（恢复要快，否则会一直卡在高位）
            self.min_gap = max(self._floor, self.min_gap * 0.8)

    # ---- 搜索缓存：重跑不再发请求，也就不会再被限流 ----
    def _load_cache(self):
        if os.path.exists(CACHE_FILE):
            try:
                with open(CACHE_FILE, encoding="utf-8") as f:
                    self._cache = json.load(f)
            except Exception:                     # noqa: BLE001
                self._cache = {}

    def _save_cache(self):
        with self._lock:
            if not self._cache_dirty:
                return
            try:
                tmp = CACHE_FILE + ".tmp"
                with open(tmp, "w", encoding="utf-8") as f:
                    json.dump(self._cache, f, ensure_ascii=False,
                              separators=(",", ":"))
                os.replace(tmp, CACHE_FILE)   # 原子替换，中断也不留半截文件
                self._cache_dirty = False
            except Exception:                     # noqa: BLE001
                pass

    # ---- 底层请求 ----
    def _req(self, url, data=None, method=None, timeout=30):
        self._throttle()
        body = urllib.parse.urlencode(data).encode() if data else None
        req = urllib.request.Request(url, data=body, method=method or ("POST" if data else "GET"))
        req.add_header("User-Agent", UA)
        req.add_header("Referer", BASE + "/")
        req.add_header("Origin", BASE)
        if body:
            req.add_header("Content-Type", "application/x-www-form-urlencoded")
        if self.cookies:
            req.add_header("Cookie", "; ".join("%s=%s" % kv for kv in self.cookies.items()))
        last = None
        for attempt in range(3):
            try:
                with urllib.request.urlopen(req, timeout=timeout) as r:
                    raw = r.read().decode("utf-8", "replace")
                    for sc in r.headers.get_all("Set-Cookie") or []:
                        kv = sc.split(";")[0]
                        if "=" in kv:
                            k, v = kv.split("=", 1)
                            self.cookies[k.strip()] = v.strip()
                try:
                    return json.loads(raw)
                except ValueError:
                    return {"code": -1, "_raw": raw[:400]}
            except Exception as e:                # noqa: BLE001
                last = e
                time.sleep(1.2 * (attempt + 1))
        return {"code": -1, "_error": str(last)}

    def weapi(self, path, payload, timeout=30):
        """走 /weapi/ 加密通道。登录等敏感接口必须用它，否则 401 无权限访问. ENC"""
        secret = "".join(random.choice(string.ascii_letters + string.digits)
                         for _ in range(16))
        data = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
        params = _aes_b64(_aes_b64(data, _W_NONCE), secret)
        body = {"params": params, "encSecKey": _rsa_encrypt(secret)}
        url = "%s/weapi%s?csrf_token=%s" % (BASE, path, self.csrf)
        return self._req(url, body, timeout=timeout)

    @property
    def csrf(self):
        return self.cookies.get("__csrf", "")

    # ---- cookie 存取 ----
    def _load_cookies(self):
        if os.path.exists(COOKIE_FILE):
            try:
                with open(COOKIE_FILE, encoding="utf-8") as f:
                    d = json.load(f)
                self.cookies = d.get("cookies") or {}
                self.uid = d.get("uid")
                self.nickname = d.get("nickname")
            except Exception:                     # noqa: BLE001
                pass

    def save_cookies(self):
        with open(COOKIE_FILE, "w", encoding="utf-8") as f:
            json.dump({"cookies": self.cookies, "uid": self.uid,
                       "nickname": self.nickname}, f, ensure_ascii=False, indent=2)
        os.chmod(COOKIE_FILE, 0o600)

    # ---- 登录 ----
    def whoami(self):
        d = self._req(BASE + "/api/nuser/account/get")
        prof = d.get("profile") or {}
        acct = d.get("account") or {}
        if prof.get("userId") or acct.get("id"):
            self.uid = prof.get("userId") or acct.get("id")
            self.nickname = prof.get("nickname") or ""
            return True
        return False

    def login_qr(self, total_wait=900):
        deadline = time.time() + total_wait
        unikey = None
        n = 0
        state = None
        while time.time() < deadline:
            if unikey is None:                      # 取新码（首次或上一张过期）
                d = self._req(BASE + "/api/login/qrcode/unikey?type=1")
                unikey = d.get("unikey")
                if not unikey:
                    print("! 取二维码失败(%s)，10 秒后重试" % d)
                    time.sleep(10)
                    continue
                url = "%s/login?codekey=%s" % (BASE, unikey)
                n += 1
                # 每张码用独立文件名：预览/聊天窗口不会拿缓存的老图糊弄人
                stamp = time.strftime("%H%M%S")
                png = os.path.join(HERE, "qr-%s.png" % stamp)
                self.qr_path = png
                try:
                    make_qr_png(url, png)
                    subprocess.run(["open", png], check=False)
                except Exception as e:              # noqa: BLE001
                    print("! 生成二维码图片失败（%s）" % e)
                print("\n── 第 %d 张二维码已生成并弹出（%s）──" % (n, stamp))
                print("   图片文件: %s" % png)
                print("   用【网易云音乐 App → 扫一扫】扫它。若提示失效，我会自动换新的。")
                print("   链接: %s" % url)
                state = None

            time.sleep(3.0)      # 轮询本身也吃限流额度，别太密
            r = self._req("%s/api/login/qrcode/client/login?key=%s&type=1"
                          % (BASE, unikey))
            code = r.get("code")

            if code == 800:                         # 过期 → 自动换一张
                print("  · 这张过期了，自动换新的…")
                unikey = None
                continue
            if code == 801:
                if state != 801:
                    print("  · 等待扫码…")
                    state = 801
                continue
            if code == 802:
                if state != 802:
                    print("  ✓ 已扫码！请在手机上点「确认登录」")
                    state = 802
                continue
            if code == 803:
                ck = r.get("cookie") or ""
                for kv in ck.split(";"):
                    if "=" in kv:
                        k, v = kv.strip().split("=", 1)
                        self.cookies[k] = v
                if not self.cookies.get("__csrf"):
                    self.cookies["__csrf"] = ""
                self.save_cookies()
                ok = self.whoami()
                self.save_cookies()
                if ok:
                    print("\n✓ 登录成功：%s (uid=%s)"
                          % (self.nickname or "?", self.uid))
                else:
                    print("\n✓ 已拿到 cookie，但校验失败")
                return ok

        print("等待超时。请重跑 ./a2n login")
        return False

    # ---- 短信登录（二维码老是扫不过去时的备选） ----
    def sms_send(self, phone, ctcode="86"):
        d = self.weapi("/sms/captcha/sent", {"cellphone": phone, "ctcode": ctcode})
        if d.get("code") == 200:
            print("✓ 验证码已发到 %s，请查收短信（一般 1 分钟内到）" % phone)
            return True
        print("! 发送验证码失败: %s" % d)
        return False

    def sms_login(self, phone, code, ctcode="86"):
        d = self.weapi("/login/cellphone",
                       {"phone": phone, "countrycode": ctcode, "captcha": code,
                        "rememberLogin": "true", "csrf_token": ""})
        if d.get("code") != 200:
            print("! 登录失败: %s" % d)
            return False
        for k in ("MUSIC_U", "__csrf"):
            if d.get(k):
                self.cookies[k] = d[k]
        for kv in (d.get("cookie") or "").split(";"):     # 有的返回带 cookie 串
            if "=" in kv:
                k, v = kv.strip().split("=", 1)
                self.cookies[k] = v
        if not self.cookies.get("__csrf"):
            self.cookies["__csrf"] = ""
        self.save_cookies()
        if self.whoami():
            self.save_cookies()
            print("✓ 登录成功：%s (uid=%s)" % (self.nickname or "?", self.uid))
            return True
        print("! 接口返回 200，但拿不到用户信息")
        return False

    def ensure_login(self, anon=False):
        if self.cookies and self.whoami():
            print("✓ 已登录：%s" % (self.nickname or self.uid))
            return True
        if anon:
            print("! 匿名模式：实测未登录时网易云限流极严，会慢到不可用。")
            return False
        print("需要先登录网易云（未登录会被严厉限流，强烈建议登录）。")
        self.login_qr()
        if not self.whoami():
            print("! 登录未完成，退回匿名模式（会很慢）。建议单独跑 ./a2n login")
            return False
        return True

    # ---- 业务接口 ----
    def search(self, keyword, limit=20, tries=4):
        """搜索走 /weapi/cloudsearch/get/web 加密通道。

        老的 /api/search/get/web 会被 code=405 拦死（实测固定 1~3 秒间隔下
        成功率 0/12，登录也没用），换 weapi 后同样请求稳定 200、约 0.4 秒。
        """
        key = "%d|%s" % (limit, keyword)
        with self._lock:
            hit = self._cache.get(key)
            if hit is not None:
                self.hits += 1
                return hit
            self.fetched += 1
            n = self.fetched

        wait = 2.0
        for _ in range(tries):
            d = self.weapi("/cloudsearch/get/web",
                           {"s": keyword, "type": 1, "offset": 0,
                            "limit": limit, "total": "true"})
            code = d.get("code")
            if code == 200:
                self._speed_up()
                songs = [_slim(_norm_song(s)) for s in
                         (((d.get("result") or {}).get("songs")) or [])]
                with self._lock:
                    self._cache[key] = songs
                    self._cache_dirty = True
                if n % 25 == 0:
                    self._save_cache()
                return songs
            if code in (406, 405, -1, 400, 503):
                self._slow_down()
                time.sleep(wait)
                wait = min(wait * 2, 30.0)
                continue
            return []          # 其它业务错误：真的没有
        return []

    def my_playlists(self):
        d = self._req("%s/api/user/playlist?uid=%s&offset=0&limit=1000" % (BASE, self.uid))
        return d.get("playlist") or []

    def create_playlist(self, name):
        d = self._req(BASE + "/api/playlist/create",
                      {"name": name, "privacy": 0, "type": "NORMAL",
                       "csrf_token": self.csrf})
        pl = d.get("playlist") or d
        pid = pl.get("id") or pl.get("playlistId")
        return pid, d

    def add_tracks(self, pid, ids):
        ok = 0
        for i in range(0, len(ids), 100):
            chunk = ids[i:i + 100]
            d = self._req(BASE + "/api/playlist/manipulate/tracks",
                          {"op": "add", "pid": pid,
                           "trackIds": json.dumps(chunk),
                           "csrf_token": self.csrf})
            if d.get("code") == 200:
                ok += len(chunk)
            else:
                print("  ! 加曲失败(第%d批): %s" % (i // 100 + 1, d))
            time.sleep(0.5)
        return ok


# ─────────────────────────── 匹配 ───────────────────────────

BAD_WORDS = re.compile(r"伴奏|remix|翻唱|cover|现场|live|instrumental|纯音乐|karaoke|"
                       r"slowed|reverb|sped up|dj |mashup", re.I)

QUERY_TPL = ["{artist} {name}", "{name} {artist}", "{name}"]


def score(tr: Track, c: dict) -> float:
    cn = norm(c.get("name", ""))
    an = norm(tr.name)
    if not an or not cn:
        return 0.0

    t = sim(an, cn)
    if an in cn or cn in an:
        t = max(t, 0.90)

    c_artists = [norm(a.get("name", "")) for a in (c.get("artists") or [])]
    a_artists = split_artists(tr.artist)
    art = 0.0
    for x in a_artists:
        for y in c_artists:
            if x and y:
                s = sim(x, y)
                if x in y or y in x:
                    s = max(s, 0.92)
                art = max(art, s)

    alb = sim(norm(tr.album), norm((c.get("album") or {}).get("name", ""))) if tr.album else 0.0

    sc = 0.58 * t + 0.32 * art + 0.10 * alb

    # 时长校验（Apple Music 与网易云的 duration 都是毫秒）
    cd = c.get("duration") or 0
    if tr.duration and cd:
        diff = abs(tr.duration - cd)
        if diff <= 2000:
            sc += 0.10
        elif diff <= 5000:
            sc += 0.04
        elif diff > 20000:
            sc -= 0.15

    # 版本惩罚：网易云结果是伴奏/翻唱/remix，而源不是
    if BAD_WORDS.search(c.get("name", "")) and not BAD_WORDS.search(tr.name):
        sc -= 0.20

    return max(0.0, min(1.0, sc))


def match_track(ne: Netease, tr: Track):
    """返回 (最佳候选或 None, 分数)。节流由 Netease 内部自适应控制。"""
    seen, best, best_sc = set(), None, 0.0
    for tpl in QUERY_TPL:
        q = tpl.format(artist=tr.artist, name=tr.name).strip()
        if not q:
            continue
        for c in ne.search(q):
            cid = c.get("id")
            if cid in seen:
                continue
            seen.add(cid)
            s = score(tr, c)
            if s > best_sc:
                best, best_sc = c, s
        if best_sc >= 0.93:      # 已经足够确定，不用再换关键词
            break
    return best, best_sc


def why_miss(tr: Track, best: dict) -> str:
    """给未命中的曲目一个人话解释，方便人工判断要不要手动加。"""
    cname = best.get("name", "")
    if BAD_WORDS.search(cname) and not BAD_WORDS.search(tr.name):
        return "只搜到翻唱/伴奏版，原唱可能无版权"
    cart = "/".join(a.get("name", "") for a in (best.get("artists") or []))
    if norm(tr.artist) and norm(cart) and sim(norm(tr.artist), norm(cart)) < 0.5:
        return "歌手对不上（候选是 %s）" % cart[:16]
    if norm(tr.name) != norm(cname):
        return "歌名不完全一致"
    return "需人工确认"


# ─────────────────────────── 子命令 ───────────────────────────

def cmd_list(args):
    src = args.xml or "Music.app（实时读取）"
    print("数据源: %s\n" % src)
    lib = load_any(args.xml)
    print("%-40s %s" % ("歌单", "曲目数"))
    print("-" * 50)
    total = 0
    for name, tks in lib.items():
        flag = ""
        if norm(name) in SKIP_NAMES and norm(name) not in ALLOW_NAMES:
            flag = "  (系统歌单，默认跳过)"
        total += len(tks)
        print("%-40s %d%s" % (name[:38], len(tks), flag))
    print("-" * 50)
    print("共 %d 个歌单 / %d 首" % (len(lib), total))


def cmd_login(args):
    ne = Netease()
    if getattr(args, "sms_send", None):
        ne.sms_send(args.sms_send)
    elif getattr(args, "sms_code", None):
        ne.sms_login(args.sms_code[0], args.sms_code[1])
    else:
        ne.login_qr()


def pick_playlists(lib, want=None, include_all=False):
    if want:
        if want in lib:
            return {want: lib[want]}
        cand = [n for n in lib if want.lower() in n.lower()]
        if not cand:
            sys.exit("没找到歌单 %r。可用: %s" % (want, "、".join(lib) or "(无)"))
        if len(cand) > 1:
            print("模糊匹配到 %d 个歌单，全部处理：%s" % (len(cand), "、".join(cand)))
        return {n: lib[n] for n in cand}
    out = {}
    for n, tks in lib.items():
        if include_all or norm(n) in ALLOW_NAMES or norm(n) not in SKIP_NAMES:
            out[n] = tks
    return out


def cmd_run(args):
    lib = load_any(args.xml)
    playlists = pick_playlists(lib, args.playlist, args.all)
    jobs = max(1, getattr(args, "jobs", 1) or 1)
    if not playlists:
        sys.exit("没有可导入的歌单（试试 --all）")

    print("准备处理 %d 个歌单：" % len(playlists))
    for n, tks in playlists.items():
        print("  · %s  (%d 首)" % (n, len(tks)))
    print()

    ne = Netease(min_gap=args.delay)
    if getattr(args, "anon", False):
        print("! 匿名模式（--anon）：网易云对未登录请求限流极严，会非常慢。\n")
    else:
        ne.ensure_login()
    existing = set()
    if not args.dry_run:
        existing = {p.get("name") for p in ne.my_playlists()}

    report_dir = os.path.join(HERE, "reports")
    os.makedirs(report_dir, exist_ok=True)

    for pname, tracks in playlists.items():
        if args.limit:
            tracks = tracks[:args.limit]
        if not tracks:
            print("\n══ %s ══ 空歌单，跳过" % pname)
            continue
        print("\n══ %s (%d 首) ══" % (pname, len(tracks)))

        rows, hit_ids = [], []
        plock = threading.Lock()
        donen = [0]

        def work(item):
            i, tr = item
            best, sc = match_track(ne, tr)
            ok = best is not None and sc >= args.threshold
            if ok:
                status, why = "OK", ""
            elif best is not None:
                status, why = "置信度不足", why_miss(tr, best)
            else:
                status, why = "未找到", "网易云搜不到这首"
            with plock:
                donen[0] += 1
                mark = "✓" if ok else ("·" if best is not None else "✗")
                print("  %s [%3d/%3d] %-36s %-20s %.2f%s" % (
                    mark, donen[0], len(tracks), tr.name[:36],
                    tr.artist[:20], sc, ("  ← " + why) if why else ""),
                    flush=True)
            return i, tr, best, sc, status, why

        items = list(enumerate(tracks, 1))
        results = []
        if jobs > 1:
            with ThreadPoolExecutor(max_workers=jobs) as ex:
                futs = [ex.submit(work, it) for it in items]
                for fu in as_completed(futs):
                    results.append(fu.result())
        else:
            for it in items:
                results.append(work(it))
        results.sort(key=lambda r: r[0])      # 报告按原歌单顺序

        n_ok = n_low = n_none = 0
        for i, tr, best, sc, status, why in results:
            if status == "OK":
                n_ok += 1
                hit_ids.append(best["id"])
            elif status == "置信度不足":
                n_low += 1
            else:
                n_none += 1
            rows.append({
                "序号": i, "Apple歌名": tr.name, "Apple歌手": tr.artist,
                "Apple专辑": tr.album, "时长": human(tr.duration),
                "状态": status, "说明": why,
                "网易云ID": (best or {}).get("id", ""),
                "网易云歌名": (best or {}).get("name", ""),
                "网易云歌手": "/".join(a.get("name", "") for a in (best or {}).get("artists", [])),
                "网易云专辑": ((best or {}).get("album") or {}).get("name", ""),
                "置信度": "%.2f" % sc,
            })

        safe = re.sub(r"[/\\:*?\"<>|]", "_", pname)
        csv_path = os.path.join(report_dir, "%s.csv" % safe)
        with open(csv_path, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)

        print("  ── 命中 %d ／ 置信度不足 %d ／ 搜不到 %d（共 %d 首）"
              % (n_ok, n_low, n_none, len(tracks)))
        print("     当前节流 %.2fs   报告: %s" % (ne.min_gap, csv_path))

        if args.dry_run:
            continue
        if not hit_ids:
            print("  跳过创建（无命中曲目）")
            continue

        if not args.yes:
            ans = input("  创建歌单「%s」并加入 %d 首？[y/N] " % (pname, len(hit_ids))).strip().lower()
            if ans != "y":
                print("  已跳过")
                continue

        chunks = [hit_ids]
        if getattr(args, "split", None) and len(hit_ids) > args.split:
            chunks = [hit_ids[i:i + args.split]
                      for i in range(0, len(hit_ids), args.split)]
            print("  曲目 %d 首超过单歌单上限 %d，拆成 %d 个歌单"
                  % (len(hit_ids), args.split, len(chunks)))

        for ci, chunk in enumerate(chunks, 1):
            base = pname if len(chunks) == 1 else \
                "%s (%d/%d)" % (pname, ci, len(chunks))
            name = base if base not in existing else base + " (导入)"
            pid, raw = ne.create_playlist(name)
            if not pid:
                print("  ! 创建歌单失败: %s" % raw)
                continue
            n = ne.add_tracks(pid, chunk)
            existing.add(name)
            print("  ✓ 歌单「%s」已创建，加入 %d/%d 首" % (name, n, len(chunk)))
            print("    https://music.163.com/#/playlist?id=%s" % pid)

    ne._save_cache()
    print("\n完成。未命中的曲目都记在 reports/*.csv（含候选与原因），可人工补。")
    print("搜索统计：实发 %d 次请求 / 缓存命中 %d 次 / 最终节流 %.2fs"
          % (ne.fetched, ne.hits, ne.min_gap))


def main():
    ap = argparse.ArgumentParser(
        prog="a2n", description="把 Apple Music 歌单导入网易云音乐")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("list", help="列出歌单（省略文件则直接读 Music.app）")
    p.add_argument("xml", nargs="?", help="资料库 XML；省略 = 直接读 Music.app")
    p.set_defaults(func=cmd_list)

    p = sub.add_parser("login", help="扫码登录网易云（也可用 --sms-send 短信登录）")
    p.add_argument("--sms-send", metavar="手机号", help="给这个手机号发短信验证码")
    p.add_argument("--sms-code", nargs=2, metavar=("手机号", "验证码"),
                   help="用验证码完成登录")
    p.set_defaults(func=cmd_login)

    p = sub.add_parser("run", help="匹配并导入（省略文件则直接读 Music.app）")
    p.add_argument("xml", nargs="?", help="资料库 XML；省略 = 直接读 Music.app")
    p.add_argument("--playlist", help="只处理这一个歌单（支持模糊名）")
    p.add_argument("--all", action="store_true", help="连系统歌单也一起处理")
    p.add_argument("--limit", type=int, help="每个歌单最多处理多少首（试跑用）")
    p.add_argument("--threshold", type=float, default=0.70, help="匹配阈值，默认 0.70")
    p.add_argument("--delay", type=float, default=0.4,
                   help="请求最小间隔秒数，默认 0.4（走 weapi 加密通道，基本不限流）")
    p.add_argument("--split", type=int, metavar="N",
                   help="单个歌单最多放 N 首，超出则拆成「名字 (1/4)」等多个歌单")
    p.add_argument("--jobs", type=int, default=1, metavar="N",
                   help="并发请求数，默认 1。瓶颈是网络延迟，调大能显著加速")
    p.add_argument("--dry-run", action="store_true", help="只匹配、只出报告，不写网易云")
    p.add_argument("--anon", action="store_true", help="跳过登录（不推荐，会被严重限流）")
    p.add_argument("--yes", action="store_true", help="不再逐个确认")
    p.set_defaults(func=cmd_run)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n已取消")
