#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
U_Autobooking · 浴室自动预约系统

作者：HEDBS
项目地址：https://github.com/HEDBS/U_Autobooking
开源许可：MIT License（详见项目根目录 LICENSE 文件）

功能概述
--------
本程序用于 h5.hydream.cn（浴室预约系统）的自动化操作，提供两类自动化：

  1. 空闲预约：监控指定浴室的空闲位置数量，当数量满足设定条件时自动完成预约。
  2. 排队预约：当浴室满员、系统进入排队模式时，监控当前排队人数，
     人数满足设定条件时自动加入排队，并持续跟踪排队结果，
     排到位置后报告预约的浴室与位置编号。

运行方式
--------
直接运行本文件即可，全部操作通过菜单完成，不需要命令行参数。
首次运行会引导完成登录与参数配置；配置完成后支持快速启动。

生成文件
--------
U_Autobooking_state.json  运行配置与登录状态（程序自动维护，无需手工编辑）
U_Autobooking.log         运行日志

运行环境：Python 3.7 及以上，仅使用标准库。
"""

import base64
import getpass
import http.cookiejar
import json
import os
import random
import re
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta

VERSION = "1.0"
PROJECT = "U_Autobooking"
AUTHOR = "HEDBS"
PROJECT_URL = "https://github.com/HEDBS/U_Autobooking"

__author__ = AUTHOR
__version__ = VERSION
__url__ = PROJECT_URL
__license__ = "MIT"

# ============================================================ 路径 / 常量

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
STATE_PATH = os.path.join(BASE_DIR, "U_Autobooking_state.json")
LOG_PATH = os.path.join(BASE_DIR, "U_Autobooking.log")

API_BASE = "https://lz.hydream.cn/api/v1/"
PAGE_HOST = "https://h5.hydream.cn"

UA = ("Mozilla/5.0 (iPhone; CPU iPhone OS 16_6 like Mac OS X) AppleWebKit/605.1.15 "
      "(KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1")

# 内置平均洗澡时长（分钟）——用于估算排队等待，仅在站点未提供预计等待时兜底。
# 数据参考：
#   1) 北京大学学报（自然科学版）2025《基于混合策略的高校学生生活节水潜力模拟研究》：
#      高校学生平均每周洗浴 4~6 次，25% 的学生单次洗浴时长超过 20 分钟。
#   2) 新浪天津 2019 洗澡习惯报告：男性平均洗澡时长比女性少约 10 分钟。
#   3) 联合利华 / 青年参考：约七成受访者淋浴在 10 分钟以内。
# 结论性取值：男生约 10 分钟、女生约 20 分钟。可被用户覆盖，也会被站点
# expectedWaitingTime 的实际数据自动取代。
AVG_BATH_MINUTES = {"male": 10, "female": 20}

GENDER_TEXT = {"male": "男", "female": "女", "unknown": "未知"}


def human_secs(seconds):
    """把秒数说成人话。"""
    try:
        seconds = int(seconds)
    except (TypeError, ValueError):
        return "未知"
    if seconds < 0:
        seconds = -seconds
        sign = "-"
    else:
        sign = ""
    if seconds >= 3600:
        return "%s%d 小时 %d 分" % (sign, seconds // 3600, (seconds % 3600) // 60)
    if seconds >= 60:
        return "%s%d 分 %d 秒" % (sign, seconds // 60, seconds % 60)
    return "%s%d 秒" % (sign, seconds)


def plan_gate(now_ts, target_ts, arrive_lead_min, wait_sec=None, factor=0.8):
    """根据计划洗澡时间决定此刻能不能动手。

    返回 (能否抢空位, 能否排队, 说明)。

    保守策略：抢到位置后必须能在 arrive_lead_min 内到场，所以拿到位置的时刻
    不得早于 target - lead；排队则要求「现在 + 预计等待（保守低估）」
    也不早于该时刻，宁可晚排也不早到。
    """
    ready_at = target_ts - arrive_lead_min * 60      # 最迟该在此时拿到位置
    remaining = ready_at - now_ts
    if remaining <= 0:
        return True, True, "已进入可拿位置的时间窗口"
    if wait_sec is None:
        return False, False, "距可拿位置还有 %s，且尚未取得排队时长" % human_secs(remaining)
    est = max(0.0, float(wait_sec) * float(factor))
    if est >= remaining:
        return False, True, ("预计等待 %s（已按保守系数 %s 折算）足以覆盖剩余 %s，可以排队"
                             % (human_secs(est), factor, human_secs(remaining)))
    return False, False, ("预计等待 %s 不足以覆盖剩余 %s，再等等"
                          % (human_secs(est), human_secs(remaining)))


DEFAULT_STATE = {
    "account": "",
    "password": "",
    "org_area_id": None,
    "device_type_key": None,
    "device_type_name": "",
    "targets": [],              # [{"area_id": 12, "area_name": "10#1层 (男)"}]
    "target_time": "",          # 计划开始洗澡时间 "21:30"（定时预约的唯一入口，必填）
    "gender": "auto",           # auto=从账号读取；也可手动指定 male/female
    "avg_bath_minutes": None,   # None=按性别用内置平均时长；也可自填（分钟）
    "arrive_lead_min": 5,       # 到场准备时间（分钟）：拿到位置后多久能到浴室
    "conservative_factor": 0.8, # 保守系数：低估排队等待，宁可晚排也不早到
    "give_up_min": 30,          # 超过计划时间这么多分钟还没拿到位置就停止
    "auto_cancel_early": True,  # 排到的时间早于计划时间时，自动取消这次位置并重新等
    "cancel_queue_on_giveup": True,  # 超过计划时间仍未拿到位置时，自动退出排队
    "poll_interval": 1,         # 检测周期（秒），1~60
    "auto_health_log": True,    # 自动提交体温登记（部分校区预约前置条件）
    "temperature": "36.01",
    "notify_cmd": "",           # 结果通知命令，消息内容见环境变量 HY_DREAM_MSG
    "session": {},
}

# 接口字段兼容：不同校区/版本可能使用不同命名
IDLE_KEYS = ["idleNum", "idle_num", "idleDeviceNum", "freeNum", "free_num", "freeCount",
             "idleCount", "canUseNum", "remainingNum", "remainNum"]
TOTAL_KEYS = ["totalNum", "total_num", "deviceNum", "device_num", "device_number",
              "deviceNumber", "totalCount", "total"]
WAIT_KEYS = ["queuingNumber", "queueingNumber", "queuing_number", "queueing_number",
             "waitingNumber", "waitingCount", "waitNum", "wait_num", "queueNum",
             "queueCount", "queue_num", "waiting_num", "peopleNum", "people_num"]
POSITION_KEYS = ["queuingNumber", "queueingNumber", "position", "queuePosition", "queue_position",
                 "waitingNumber", "index", "no", "number"]
READY_STATES = {"ready", "normal", "idle", "free"}

_LOG_DISABLED = False   # 自检等场景下临时关闭日志写入
_STATUS_CACHE = {"at": 0.0, "key": "", "lines": []}   # 主页面实时状态缓存


# ============================================================ 输出 / 界面

def out(msg="", level="INFO"):
    line = msg if level == "RAW" else "[%s] %-5s %s" % (
        datetime.now().strftime("%H:%M:%S"), level, msg)
    print(line, flush=True)
    if level != "RAW" and not _LOG_DISABLED:
        try:
            with open(LOG_PATH, "a", encoding="utf-8") as f:
                f.write("[%s] %-5s %s\n" % (
                    datetime.now().strftime("%Y-%m-%d %H:%M:%S"), level, msg))
        except OSError:
            pass


def can_interact():
    try:
        return bool(sys.stdin) and sys.stdin.isatty()
    except Exception:
        return False


def clear():
    """清屏，保证界面干净（仅供交互模式使用）。"""
    if not can_interact():
        return
    try:
        if os.name == "nt":
            os.system("cls")
        else:
            sys.stdout.write("\033[2J\033[3J\033[H")
            sys.stdout.flush()
    except Exception:
        pass


def banner():
    print("=" * 62)
    print("  %s  浴室自动预约系统  v%s" % (PROJECT, VERSION))
    print("  作者 %s   %s" % (AUTHOR, PROJECT_URL))
    print("=" * 62)


def title(text):
    print()
    print("  【%s】" % text)
    print("-" * 62)


def line(text=""):
    print(("  " + text) if text else "")


# ============================================================ 输入

class NoInput(Exception):
    """无法获取键盘输入（无控制台环境）。"""


def ask(prompt, default=None):
    suffix = "（回车 = %s）" % default if default not in (None, "") else ""
    try:
        raw = input("  %s%s：" % (prompt, suffix)).strip()
    except EOFError:
        raise NoInput()
    if not raw and default is not None:
        return str(default)
    return raw


def ask_secret(prompt):
    """读取密码。有控制台时不回显，无控制台时降级为普通输入。"""
    if not can_interact():
        return ask(prompt)
    try:
        return getpass.getpass("  %s（输入不显示）：" % prompt).strip()
    except Exception:
        return ask(prompt)


def ask_choice(prompt, options, default=1):
    """options: [(编号, 标题, 说明)]，返回选中的编号字符串。"""
    for key, name, desc in options:
        mark = "   （默认）" if str(key) == str(default) else ""
        desc_text = ("   —— " + desc) if desc else ""
        print("   %s) %s%s%s" % (key, name, desc_text, mark))
    while True:
        raw = ask(prompt, default=str(default))
        if raw in [str(k) for k, _, _ in options]:
            return raw
        print("   输入无效，请填写上方编号。")


def pause(text="按回车返回上级菜单"):
    try:
        input("  %s…" % text)
    except (EOFError, KeyboardInterrupt):
        raise NoInput()


def confirm(prompt, default_yes=False):
    default = "是" if default_yes else "否"
    raw = ask("%s（是/否）" % prompt, default=default)
    return raw.strip() in ("是", "y", "Y", "yes", "1", "确认")


# ============================================================ 配置持久化

def load_state(path=STATE_PATH):
    state = dict(DEFAULT_STATE)
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                state.update(data)
        except (OSError, ValueError) as e:
            out("配置文件读取失败（%s），已使用默认配置" % e, "WARN")
    return state


def save_state(state, path=STATE_PATH):
    try:
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)
        try:
            os.chmod(path, 0o600)
        except OSError:
            pass
        return True
    except OSError as e:
        out("配置保存失败：%s" % e, "ERROR")
        return False


def is_configured(state):
    return bool(state.get("account") and state.get("password") and state.get("targets")
                and (state.get("target_time") or "").strip())


# ============================================================ 接口客户端

class ApiError(Exception):
    def __init__(self, code, msg, raw=""):
        super().__init__("code=%s %s" % (code, msg))
        self.code = code
        self.msg = str(msg)


class NotLoggedIn(ApiError):
    pass


def status_conflict(e):
    """站点提示「已有设备 / 已在排队」这类状态冲突，属于业务状态而非程序错误。"""
    if not isinstance(e, ApiError):
        return False
    msg = e.msg or ""
    return str(e.code) == "101212" or "同时只能使用" in msg or "已在排队" in msg or "正在排队" in msg


class NetworkError(Exception):
    pass


class HydreamClient:
    def __init__(self, timeout=20, debug=False):
        self.timeout = timeout
        self.debug = debug
        self.session_name = ""
        self.session_id = ""
        self.jar = http.cookiejar.CookieJar()
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.jar))
        self.headers = {
            "User-Agent": UA,
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
            "Origin": PAGE_HOST,
            "Referer": PAGE_HOST + "/index_list.html",
            "X-Requested-With": "XMLHttpRequest",
            "Connection": "keep-alive",
        }

    # ---- 底层请求 ------------------------------------------------------

    def _post(self, url, data):
        body = urllib.parse.urlencode(data).encode("utf-8")
        req = urllib.request.Request(url, data=body, headers=self.headers, method="POST")
        try:
            with self.opener.open(req, timeout=self.timeout) as resp:
                return resp.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            raise NetworkError("服务器返回 HTTP %s" % e.code)
        except urllib.error.URLError as e:
            raise NetworkError("无法连接服务器：%s" % e.reason)
        except OSError as e:
            raise NetworkError("网络异常：%s" % e)

    @staticmethod
    def _parse(raw):
        txt = (raw or "").strip()
        if not txt:
            raise ApiError(-1, "服务器返回内容为空")
        if txt[0] in "{[":
            return json.loads(txt)
        if "Access Denied" in txt:
            raise ApiError(-2, "请求被网站安全策略拦截")
        try:
            clean = re.sub(r"[^A-Za-z0-9+/=]", "", txt)
            clean += "=" * (-len(clean) % 4)
            return json.loads(base64.b64decode(clean).decode("utf-8", "replace"))
        except Exception:
            raise ApiError(-3, "服务器返回内容无法识别：%s" % txt[:120])

    def api(self, mod, act, data=None, retries=3):
        payload = dict(data or {})
        payload["isWeb"] = 1
        url = API_BASE + mod + "/" + act
        if self.session_id:
            url += "?PHPSESSID=" + urllib.parse.quote(self.session_id)

        parsed, last = None, None
        for attempt in range(1, retries + 1):
            try:
                parsed = self._parse(self._post(url, payload))
                break
            except NetworkError as e:
                last = e
                out("网络请求失败（第 %d/%d 次）：%s" % (attempt, retries, e), "WARN")
                time.sleep(2 * attempt)
            except ApiError as e:
                if e.code == -2 and attempt < retries:
                    last = e
                    out("请求被安全策略拦截（第 %d/%d 次），正在重试" % (attempt, retries), "WARN")
                    time.sleep(2 * attempt)
                    continue
                raise
        if parsed is None:
            raise NetworkError("重试 %d 次后仍失败：%s" % (retries, last))

        if self.debug:
            out("接口 %s/%s 返回：%s" % (
                mod, act, json.dumps(parsed, ensure_ascii=False)[:400]), "DEBUG")

        inner = parsed.get("data") if isinstance(parsed, dict) else None
        if not isinstance(inner, dict) or "code" not in inner:
            raise ApiError(-4, "接口返回格式异常：%s" % json.dumps(parsed, ensure_ascii=False)[:150])
        if inner.get("code") != 200:
            msg = inner.get("msg") or inner.get("message") or ""
            if str(inner.get("code")) in ("100090", "100091"):
                raise NotLoggedIn(inner["code"], msg)
            raise ApiError(inner["code"], msg)
        return inner.get("data")

    # ---- 会话 ----------------------------------------------------------

    def set_cookie(self, name, value):
        self.jar.set_cookie(http.cookiejar.Cookie(
            version=0, name=name, value=str(value), port=None, port_specified=False,
            domain=".hydream.cn", domain_specified=True, domain_initial_dot=True,
            path="/", path_specified=True, secure=False, expires=None, discard=False,
            comment=None, comment_url=None, rest={}, rfc2109=False))

    def login(self, account, password):
        payload = self.api("UserApi", "loginWidthPwd", {"mobile": account, "pwd": password})
        if not isinstance(payload, dict):
            raise ApiError(-5, "登录接口返回异常")
        sname, sid = payload.get("sessionName"), payload.get("sessionId")
        if sname and sid:
            self.session_name, self.session_id = sname, str(sid)
            self.set_cookie(sname, sid)
        else:
            for c in self.jar:
                if c.name.upper() == "PHPSESSID":
                    self.session_name, self.session_id = "PHPSESSID", c.value
        return payload

    def dump_session(self):
        return {"name": self.session_name, "id": self.session_id, "saved_at": time.time(),
                "cookies": [{"name": c.name, "value": c.value, "domain": c.domain,
                             "path": c.path} for c in self.jar]}

    def restore_session(self, session):
        if not isinstance(session, dict):
            return False
        for c in session.get("cookies") or []:
            try:
                self.set_cookie(c.get("name"), c.get("value"))
            except Exception:
                pass
        self.session_name = session.get("name", "")
        self.session_id = str(session.get("id") or "")
        return bool(self.session_id or session.get("cookies"))


# ============================================================ 数据整理

def pick_field(row, keys):
    for k in keys:
        if k in row and row[k] not in (None, ""):
            try:
                return int(float(row[k]))
            except (TypeError, ValueError):
                continue
    return None


def normalize_areas(rows, meta=None):
    meta = meta or {}
    result = []
    for i, row in enumerate(rows or []):
        if not isinstance(row, dict):
            continue
        aid = row.get("device_area_id", row.get("deviceAreaId"))
        name = (row.get("device_area_name") or row.get("deviceAreaName")
                or meta.get(aid) or ("浴室%s" % aid))
        name = str(name).strip()
        result.append({"index": i, "id": aid, "name": name,
                       "idle": pick_field(row, IDLE_KEYS),
                       "total": pick_field(row, TOTAL_KEYS),
                       "waiting": pick_field(row, WAIT_KEYS),
                       "raw": row})
    return result


def matched(value, threshold, condition):
    if value is None:
        return False
    c = (condition or "le").lower()
    if c in ("le", "<="):
        return value <= threshold
    if c in ("eq", "=="):
        return value == threshold
    if c in ("ge", ">="):
        return value >= threshold
    if c == "lt":
        return value < threshold
    if c == "gt":
        return value > threshold
    raise ValueError("条件参数无效：%r" % condition)


def cond_text(condition, threshold, subject="空闲位置"):
    tpl = {"le": "%s 不超过 %d 时", "eq": "%s 恰好为 %d 时",
           "ge": "%s 达到 %d 及以上时", "lt": "%s 少于 %d 时",
           "gt": "%s 多于 %d 时"}.get(condition, "%s 为 %d 时")
    return tpl % (subject, threshold)


def cond_issue(condition, threshold, subject="空闲位置"):
    """检查条件设置是否退化（恒真或恒假），返回说明文字；无问题返回 None。"""
    try:
        threshold = int(threshold)
    except (TypeError, ValueError):
        return "阈值必须是整数"
    if subject.startswith("空闲"):
        if condition == "ge" and threshold < 1:
            return "「%s ≥ %d」在任何情况下都成立，等同于无条件立即预约" % (subject, threshold)
        if condition in ("le", "eq") and threshold < 1:
            return "「%s ≤ %d」只在满员时成立，而满员会走排队流程，等于空闲预约失效" % (subject, threshold)
    else:
        if condition in ("ge", "eq") and threshold < 1:
            return "「%s ≥ %d」在任何情况下都成立，等同于满员就排队" % (subject, threshold)
    return None


def cond_preview(condition, threshold, total=None):
    """给用户看的效果预览：不同空闲/排队人数下会不会动作。"""
    rows = []
    if total:
        samples = [total, max(1, total // 2), 2, 1, 0]
    else:
        samples = [28, 10, 3, 2, 1, 0]
    seen = []
    for n in samples:
        if n in seen:
            continue
        seen.append(n)
        rows.append("  %s %2d 个 -> %s" % ("空闲" if total else "空闲", n,
                                          "预约" if matched(n, threshold, condition) else
                                          ("排队" if n == 0 else "不动作")))
    return rows


def ts_text(value):
    try:
        return datetime.fromtimestamp(int(value)).strftime("%m-%d %H:%M:%S")
    except (TypeError, ValueError, OSError):
        return str(value or "未知")


# ============================================================ 业务核心

class Bot:
    def __init__(self, client, state):
        self.c = client
        self.state = state
        self.user = {}
        self.org_area_id = None
        self.device_type_key = None
        self.last_msg_id = 0
        self._area_meta_unsupported = False
        self._queue_block_until = 0          # 排队被服务器拒绝后的冷却截止时间
        self.plan_current = None             # 本次监控使用的时间计划
        self._early_cancel_count = 0         # 因"排到太早"自动取消的次数
        self.check_body_temperature = None   # 该校区是否需要体温登记（None = 未知）

    # ---- 基础信息 ------------------------------------------------------

    def whoami(self):
        self.user = self.c.api("UserApi", "getUserInfo") or {}
        out("账号：%s（%s）  账户余额：%s" % (
            self.user.get("user_nickname") or self.user.get("user_login") or "未命名",
            self.user.get("mobile") or "无手机号",
            self.user.get("available_balance") or "0.00"))
        return self.user

    def device_types(self):
        return self.c.api("DeviceAreaApi", "selectDeviceTypeByOrgAreaId",
                          {"orgAreaId": self.org_area_id}) or []

    def areas(self, retries=3):
        rows = self.c.api("DeviceAreaApi", "selectDeviceAreasWithDeviceState",
                          {"orgAreaId": self.org_area_id,
                           "deviceTypeKey": self.device_type_key}, retries=retries) or []
        meta = {}
        if not self._area_meta_unsupported:      # 部分站点无此接口，只尝试一次
            try:
                for r in self.c.api("DeviceAreaApi", "selectDeviceAreas",
                                    {"orgAreaId": self.org_area_id}) or []:
                    meta[r.get("device_area_id")] = r.get("device_area_name")
            except ApiError:
                self._area_meta_unsupported = True
        return normalize_areas(rows, meta)

    def resolve_org_area(self):
        self.org_area_id = self.state.get("org_area_id") or self.user.get("default_org_area_id")
        if not self.org_area_id or str(self.org_area_id) == "0":
            raise ApiError(-8, "账号未绑定校区，请先在 h5.hydream.cn 上选择校区后重试")
        self.state["org_area_id"] = self.org_area_id
        return self.org_area_id

    def resolve_device_type(self, interactive=False):
        types = self.device_types()
        if not types:
            raise ApiError(-6, "该校区暂无可用的设备类型")
        saved = self.state.get("device_type_key")
        if saved and any(t.get("device_type_key") == saved for t in types):
            self.device_type_key = saved
            return self.device_type_key
        if not interactive:
            pick = next((t for t in types if str(t.get("need_reserve")) == "1"), types[0])
            self.device_type_key = pick.get("device_type_key")
            return self.device_type_key

        title("选择设备类型")
        options = []
        default = 1
        for i, t in enumerate(types, 1):
            need = str(t.get("need_reserve")) == "1"
            options.append((i, "%s（%s）" % (t.get("device_type_name") or t.get("device_type_key"),
                                             "需预约" if need else "可直接使用"), ""))
            if need and default == 1:
                default = i
        idx = int(ask_choice("请选择设备类型", options, default))
        chosen = types[idx - 1]
        self.device_type_key = chosen.get("device_type_key")
        self.state["device_type_key"] = self.device_type_key
        self.state["device_type_name"] = chosen.get("device_type_name") or self.device_type_key
        return self.device_type_key

    # ---- 预约 ----------------------------------------------------------

    def health_log(self):
        if not self.state.get("auto_health_log"):
            return
        if self.check_body_temperature is False:   # 该校区不需要体温登记
            return
        try:
            self.c.api("HealthApi", "createLog",
                       {"bodyTemperature": str(self.state.get("temperature", "36.01")),
                        "deviceTypeKey": self.device_type_key})
        except ApiError as e:
            out("体温登记未成功（不影响后续操作）：%s" % e, "WARN")

    def pick_ready_device(self, area_id):
        devices = self.c.api("DeviceAreaApi", "selectDevicesByAreaId",
                             {"deviceAreaId": area_id,
                              "deviceTypeKey": self.device_type_key}) or []
        ready = [d for d in devices if str(d.get("device_status", "")).lower() in READY_STATES]
        return random.choice(ready) if ready else None

    def reserve(self, area_id, area_name):
        device = self.pick_ready_device(area_id)
        if device is None:
            out("当前未读取到空闲位置（可能刚刚被占用），本轮跳过", "WARN")
            return None
        device_name = device.get("device_name") or device.get("device_key")
        line("选中位置：%s" % device_name)
        self.health_log()
        result = self.c.api("DeviceApi", "reserve", {"uuid": device["device_key"]}) or {}
        return {"area_id": area_id, "area_name": area_name, "device": device, "result": result}

    # ---- 排队 / 状态总线 -----------------------------------------------

    def bus_messages(self, area_id, retries=3):
        """通过 BusApi 获取浴室实时状态（排队人数、本人状态）。"""
        params = {"deviceAreaId": area_id, "deviceTypeKey": self.device_type_key,
                  "time": int(time.time()), "lastId": self.last_msg_id}
        data = self.c.api("BusApi", "exchangeMsg", params, retries=retries)
        if isinstance(data, dict):
            data = data.get("list") or data.get("data") or data.get("messages") or []
        if not isinstance(data, list):
            return []
        for m in data:
            if isinstance(m, dict):
                try:
                    self.last_msg_id = max(self.last_msg_id, int(m.get("id") or 0))
                except (TypeError, ValueError):
                    pass
        return [m for m in data if isinstance(m, dict)]

    @staticmethod
    def _content(msg):
        return Bot._as_dict(msg.get("content", msg.get("data")))

    @staticmethod
    def _as_dict(value):
        """接口中的明细字段可能是对象，也可能是 JSON 字符串或空字符串。"""
        if isinstance(value, dict):
            return value
        if isinstance(value, str) and value.strip().startswith("{"):
            try:
                parsed = json.loads(value)
                return parsed if isinstance(parsed, dict) else {}
            except ValueError:
                return {}
        return {}

    def waiting_count(self, messages, area_row=None):
        """排队人数：优先取总线的 waitingInfo，其次取浴室状态字段。"""
        for m in messages:
            if m.get("type") == "waitingInfo":
                n = pick_field(self._content(m), WAIT_KEYS)
                if n is not None:
                    return n
        for m in messages:                       # 部分版本把排队信息放在 indexTip 里
            if m.get("type") in ("indexTip", "queueInfo"):
                n = pick_field(self._content(m), WAIT_KEYS)
                if n is not None:
                    return n
        for m in messages:
            c = self._content(m)
            n = pick_field(c, WAIT_KEYS)
            if n is not None and m.get("type") in (None, "waitingInfo", "userState"):
                return n
        return (area_row or {}).get("waiting")

    def my_status(self, messages):
        """本人状态：normal / queuing / reserved / running，附带明细。"""
        for m in messages:
            if m.get("type") == "userState":
                c = self._content(m)
                return {"state": c.get("userState") or c.get("state") or "",
                        "queue": self._as_dict(c.get("queueInfo")),
                        "device": self._as_dict(c.get("deviceInfo")),
                        "remain": c.get("remainTime"),
                        "raw": c}
        return {}

    def busy_status(self, area_id):
        """查询本人是否已有设备（已预约 / 使用中 / 排队中）。查询失败返回空。"""
        try:
            return self.my_status(self.bus_messages(area_id, retries=2))
        except (ApiError, NetworkError):
            return {}

    @staticmethod
    def describe_busy(status, fallback_name=""):
        """把本人当前状态描述成一句话；没有占用时返回空字符串。"""
        status = status or {}
        name = status.get("state") or ""
        device = status.get("device") or {}
        queue = status.get("queue") or {}
        area = (device.get("deviceAreaName") or device.get("device_area_name")
                or fallback_name or "未知浴室")
        number = device.get("deviceNumber") or device.get("device_name") or "?"
        if name == "running":
            return "使用中：%s 位置 %s" % (area, number)
        if name == "reserved":
            try:
                remain = int(status.get("remain") or 0)
            except (TypeError, ValueError):
                remain = 0
            text = "已预约：%s 位置 %s" % (area, number)
            if remain > 0:
                text += "，剩余约 %s" % ("%d 分钟" % (remain // 60) if remain >= 60 else "%d 秒" % remain)
            return text
        if name == "queuing":
            position = pick_field(queue, POSITION_KEYS)
            return "排队中：当前排位 %s 号" % (position if position is not None else "?")
        return ""

    def can_act(self, row, messages=None):
        """动手前的检查：已有预约 / 使用中 / 排队中时不再重复操作（避免 101212）。"""
        status = self.my_status(messages) if messages is not None else self.busy_status(row["id"])
        text = self.describe_busy(status, row["name"])
        if text:
            out("本轮不执行操作 —— %s" % text, "WARN")
            return False
        return True

    def queue_up(self, area_id):
        self.health_log()
        return self.c.api("DeviceAreaApi", "queueUp",
                          {"deviceAreaId": area_id,
                           "deviceTypeKey": self.device_type_key}) or {}

    def cancel_current(self, area_id=None):
        """取消本人当前的排队或预约。返回 (是否成功, 说明)。"""
        area_id = area_id or ((self.state.get("targets") or [{}])[0].get("area_id"))
        status = {}
        if area_id:
            try:
                status = self.my_status(self.bus_messages(area_id, retries=1))
            except (ApiError, NetworkError):
                status = {}
        kind = status.get("state")
        device = status.get("device") or {}

        if kind == "queuing":
            try:
                self.c.api("DeviceAreaApi", "cancelQueue",
                           {"deviceAreaId": area_id, "deviceTypeKey": self.device_type_key})
                return True, "已取消排队"
            except ApiError as e:
                return False, "取消排队失败：%s" % e.msg
        if kind in ("reserved", "running"):
            if not device.get("uuid"):
                return False, "读不到当前设备信息，无法自动取消，请在手机端操作"
            try:
                self.c.api("DeviceApi", "cancelReserve",
                           {"uuid": device.get("uuid"),
                            "deviceType": device.get("device_type_key") or self.device_type_key})
                return True, "已取消%s（%s 位置 %s）" % (
                    "使用中的设备" if kind == "running" else "预约",
                    device.get("deviceAreaName") or device.get("device_area_name") or "",
                    device.get("deviceNumber") or "?")
            except ApiError as e:
                return False, "取消预约失败：%s" % e.msg
        return False, "当前没有排队或预约（账号状态：%s）" % (kind or "未知")

    # ---- 结果确认 ------------------------------------------------------

    def confirm_reservation(self, info):
        """读取总线确认预约结果，返回确认信息（可能为空）。"""
        area_id = info.get("area_id") or (self.state.get("targets") or [{}])[0].get("area_id")
        try:
            messages = self.bus_messages(area_id)
        except (ApiError, NetworkError):
            return {}
        status = self.my_status(messages)
        device = status.get("device") or {}
        if status.get("state") in ("reserved", "running") and device:
            return {"area_name": device.get("deviceAreaName") or device.get("device_area_name"),
                    "device_number": device.get("deviceNumber") or device.get("device_number"),
                    "state": status.get("state")}
        return {}

    # ---- 监控主循环 ----------------------------------------------------

    # ---- 性别 / 时间计划 / 合法性 --------------------------------------

    def resolve_gender(self):
        """性别：优先用用户指定；否则读账号里的 sex（1=男 2=女 0=保密）。"""
        want = (self.state.get("gender") or "auto").lower()
        if want in ("male", "female"):
            return want
        if not self.user:
            try:
                self.user = self.c.api("UserApi", "getUserInfo") or {}
            except (ApiError, NetworkError):
                self.user = {}
        sex = str(self.user.get("sex", "0"))
        return {"1": "male", "2": "female"}.get(sex, "unknown")

    def plan(self):
        """解析计划洗澡时间。未设置返回 None；格式错误抛 ApiError。"""
        raw = (self.state.get("target_time") or "").strip()
        if not raw:
            return None
        try:
            hh, mm = [int(x) for x in raw.replace("：", ":").split(":")[:2]]
            if not (0 <= hh <= 23 and 0 <= mm <= 59):
                raise ValueError
        except ValueError:
            raise ApiError(-10, "计划洗澡时间格式应为 HH:MM（例如 21:30）")

        now = datetime.now()
        target = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
        rolled = target < now
        if rolled:
            target += timedelta(days=1)

        gender = self.resolve_gender()
        avg_min = self.state.get("avg_bath_minutes")
        if not avg_min:
            avg_min = AVG_BATH_MINUTES.get(gender, 15)
        try:
            avg_min = int(avg_min)
        except (TypeError, ValueError):
            avg_min = AVG_BATH_MINUTES.get(gender, 15)
        try:
            lead = int(self.state.get("arrive_lead_min", 5) or 0)
        except (TypeError, ValueError):
            lead = 5
        try:
            factor = float(self.state.get("conservative_factor", 0.8) or 1.0)
        except (TypeError, ValueError):
            factor = 0.8
        try:
            give_up = int(self.state.get("give_up_min", 30) or 0)
        except (TypeError, ValueError):
            give_up = 30
        return {"raw": raw, "target": target, "rolled": rolled, "gender": gender,
                "avg_min": avg_min, "lead": lead, "factor": factor, "give_up": give_up}

    def validate_plan(self, plan, row=None, types=None):
        """预约时间的合法性检查。返回 (是否可继续, [提示])。"""
        notes = []
        fatal = False
        now = datetime.now()
        if plan["rolled"]:
            notes.append("计划时间 %s 今天已过，按明天 %s 执行" % (plan["raw"], plan["raw"]))
        if plan["target"] - timedelta(minutes=plan["lead"]) < now:
            notes.append("！距计划时间不足 %d 分钟的到场准备时间，来不及" % plan["lead"])
            fatal = True

        if row:
            raw = row.get("raw") or {}
            limit = (raw.get("gender_limit") or "").strip()
            if plan["gender"] in ("male", "female") and limit in ("male", "female") \
                    and limit != plan["gender"]:
                notes.append("！该浴室限%s使用，你的性别是%s，不能预约"
                             % (GENDER_TEXT.get(limit), GENDER_TEXT.get(plan["gender"])))
                fatal = True
            # maintenance_tip 是模板文本（正常开放的浴室里也可能带"预计开放"字样），
            # 只有出现明确的停用字样才提示，避免误报。
            tip = (raw.get("maintenance_tip") or "").strip()
            if any(key in tip for key in ("停止", "停水", "维护", "暂停", "关闭", "检修", "维修", "故障")):
                notes.append("注意：站点对该浴室的提示「%s」" % tip)
            try:
                status = str(raw.get("status", "1"))
            except Exception:
                status = "1"
            if status not in ("1", "true", "True"):
                notes.append("！该浴室当前状态为「%s」，不可预约" % status)
                fatal = True
            try:
                open_at = int(float(raw.get("expected_open_time") or 0))
            except (TypeError, ValueError):
                open_at = 0
            if open_at > time.time() + 60:
                notes.append("！该浴室预计 %s 才开放，现在不能预约"
                             % datetime.fromtimestamp(open_at).strftime("%m-%d %H:%M"))
                fatal = True

        for t in (types or []):
            if t.get("device_type_key") != self.device_type_key:
                continue
            try:
                max_run = int(float(t.get("max_run_time") or 0))
            except (TypeError, ValueError):
                max_run = 0
            try:
                limit_times = int(float(t.get("max_reserve_times") or 0))
            except (TypeError, ValueError):
                limit_times = 0
            if limit_times:
                notes.append("提示：该类型每天最多预约 %d 次" % limit_times)
            if max_run and plan["avg_min"] * 60 > max_run:
                notes.append("！计划洗澡 %d 分钟，超过站点单次最长 %d 分钟"
                             % (plan["avg_min"], max_run // 60))
                fatal = True
        return (not fatal), notes

    @staticmethod
    def expected_wait(messages):
        """站点给出的预计等待时长（秒）。"""
        for m in messages:
            if m.get("type") == "waitingInfo":
                content = Bot._content(m)
                for key in ("expectedWaitingTime", "expected_waiting_time", "waitTime", "wait_time"):
                    if key in content:
                        try:
                            return int(float(content[key]))
                        except (TypeError, ValueError):
                            pass
        return None

    def snapshot(self, target):
        """一次请求拿到本轮所需的一切：空闲数、排队人数、预计等待、本人状态。

        1 秒级侦测靠这个把请求量压到每轮 1 个（总线里已包含该浴室全部设备状态）。
        """
        data = {"name": target.get("area_name", ""), "idle": None, "total": None,
                "waiting": None, "wait_sec": None, "mine": {}, "messages": []}
        try:
            messages = self.bus_messages(target["area_id"], retries=1)
        except (ApiError, NetworkError):
            messages = []
        if messages:
            data["messages"] = messages
            devices = []
            for m in messages:
                if m.get("type") == "deviceState" and isinstance(m.get("content"), list):
                    devices = m["content"]
            if devices:
                data["total"] = len(devices)
                data["idle"] = sum(1 for d in devices
                                   if str(d.get("deviceStatus", "")).lower() in READY_STATES)
            data["waiting"] = self.waiting_count(messages)
            data["wait_sec"] = self.expected_wait(messages)
            data["mine"] = self.my_status(messages)
        if data["idle"] is None:            # 总线没带设备状态时退回浴室接口
            try:
                for area in self.areas(retries=1):
                    if str(area["id"]) == str(target["area_id"]):
                        data["idle"], data["total"] = area["idle"], area["total"]
                        data["name"] = area["name"]
                        if data["waiting"] is None:
                            data["waiting"] = area.get("waiting")
                        break
            except (ApiError, NetworkError):
                pass
        return data

    def bootstrap(self, verbose=True):
        """进入监控前的必要初始化：账号、校区、设备类型。"""
        if not self.user:
            self.user = self.c.api("UserApi", "getUserInfo") or {}
        if not self.org_area_id:
            self.org_area_id = self.state.get("org_area_id") or self.user.get("default_org_area_id")
        if not self.org_area_id or str(self.org_area_id) == "0":
            raise ApiError(-8, "账号未绑定校区，请先在 h5.hydream.cn 上选择校区后重试")
        self.state["org_area_id"] = self.org_area_id
        if not self.device_type_key:
            self.resolve_device_type(interactive=False)
        if self.check_body_temperature is None:
            try:
                setting = self.c.api("UserApi", "getSetting") or {}
                self.check_body_temperature = str(
                    setting.get("checkBodyTemperature", "0")) in ("1", "true")
                if verbose:
                    out("站点设置：体温登记 %s，实时状态推送 %s" % (
                        "需要" if self.check_body_temperature else "不需要",
                        "已启用" if str(setting.get("enableDistributedEvent", "0")) != "0" else "未启用"))
            except ApiError:
                self.check_body_temperature = True   # 读取失败时按需要处理，避免漏登记
        return True

    def monitor(self, continuous=False):
        """定时预约监控：一切以「计划洗澡时间」为准。

        · 已到该拿位置的时间 → 有空位直接抢，满员就排队
        · 还没到该拿位置的时间 → 只在「站点预计等待能覆盖剩余时间」时提前排队占位
        · 全程保守：宁可晚排，不早到
        """
        targets = self.state.get("targets") or []
        if not targets:
            out("尚未配置目标浴室，请先进入「修改运行设置」完成配置", "ERROR")
            return False
        self.bootstrap()

        try:
            interval = float(self.state.get("poll_interval", 1) or 1)
        except (TypeError, ValueError):
            interval = 1.0
        interval = max(1.0, min(60.0, interval))

        plan = self.plan()
        if not plan:
            out("尚未设置「计划洗澡时间」，定时预约无法启动", "ERROR")
            out("请进入 修改运行设置 → 定时预约设置，设定开始洗澡的时间", "WARN")
            return False
        self.plan_current = plan

        try:
            types = self.device_types()
            areas = self.areas()
        except (ApiError, NetworkError) as e:
            out("读取浴室信息失败：%s" % e, "ERROR")
            return False
        row = next((a for a in areas if str(a["id"]) == str(targets[0]["area_id"])), None)
        ok, notes = self.validate_plan(plan, row, types)

        title("定时预约 · 时间合法性检查")
        line("计划洗澡时间：%s（%s）" % (plan["target"].strftime("%m-%d %H:%M"),
                                        "明天" if plan["rolled"] else "今天"))
        line("性别 %s ｜ 预计用时 %d 分钟 ｜ 到场准备 %d 分钟 ｜ 保守系数 %s"
             % (GENDER_TEXT.get(plan["gender"], plan["gender"]), plan["avg_min"],
                plan["lead"], plan["factor"]))
        line("最早拿位置时间：%s（抢到后 %d 分钟内需到场，否则站点自动取消）"
             % ((plan["target"] - timedelta(minutes=plan["lead"])).strftime("%H:%M"), plan["lead"]))
        for note in (notes or ["未发现问题"]):
            line(note)
        if not ok:
            out("预约时间不合法，已停止启动", "ERROR")
            return False

        title("定时预约监控已启动")
        line("目标浴室：%s" % "、".join(t["area_name"] for t in targets))
        line("检测周期：每 %.0f 秒   （按 Ctrl+C 可随时终止）" % interval)
        print("-" * 62)

        for target in targets:
            text = self.describe_busy(self.busy_status(target["area_id"]), target["area_name"])
            if text:
                out("账号当前状态：%s；已有设备时不会重复操作" % text, "WARN")

        rounds = 0
        while True:
            rounds += 1
            try:
                for target in targets:
                    data = self.snapshot(target)
                    name, idle, total = data["name"], data["idle"], data["total"]

                    mine = self.describe_busy(data["mine"], name)
                    if mine:
                        out("第 %d 轮：%s" % (rounds, mine), "WARN")
                        continue
                    if idle is None:
                        out("第 %d 轮：%s 未取得空位数据，本轮跳过" % (rounds, name), "WARN")
                        continue

                    now_ts = time.time()
                    ready_at = plan["target"].timestamp() - plan["lead"] * 60
                    wait_sec = data["wait_sec"]
                    if wait_sec is None and data["waiting"]:
                        wait_sec = data["waiting"] * plan["avg_min"] * 60
                    est_wait = int(wait_sec * plan["factor"]) if wait_sec else None

                    if now_ts > plan["target"].timestamp() + plan["give_up"] * 60:
                        out("已超过计划时间 %d 分钟仍未拿到位置，停止监控" % plan["give_up"], "WARN")
                        if self.state.get("cancel_queue_on_giveup", True) \
                                and (data["mine"] or {}).get("state") == "queuing":
                            ok2, msg = self.cancel_current(target["area_id"])
                            out("自动退出排队：%s" % msg, "WARN" if not ok2 else "INFO")
                        return False

                    if now_ts >= ready_at:
                        # —— 已到该拿位置的时间 ——
                        if idle > 0:
                            out("第 %d 轮：%s 已到时间（%s 开始洗），空闲 %s/%s，直接抢位置"
                                % (rounds, name, plan["target"].strftime("%H:%M"), idle, total))
                            try:
                                info = self.reserve(target["area_id"], name)
                            except ApiError as e:
                                if status_conflict(e):
                                    out("服务器拒绝：%s。本轮跳过（你已有设备）" % e.msg, "WARN")
                                    continue
                                raise
                            if info:
                                self.report_reservation(info)
                                if not continuous:
                                    return True
                        else:
                            out("第 %d 轮：%s 已到时间且已满员，加入排队"
                                % (rounds, name))
                            if self.try_queue(target, rounds, messages=data["messages"],
                                              idle=idle, total=total, wait_sec=wait_sec,
                                              reason="已到计划时间") and not continuous:
                                return True
                        continue

                    # —— 还没到时间：只有预计等待足够长才提前排队占位 ——
                    remaining = int(ready_at - now_ts)
                    if est_wait is None:
                        out("第 %d 轮：%s 空闲 %s/%s，距该拿位置还有 %s，排队时长未知，继续等"
                            % (rounds, name, idle, total, human_secs(remaining)))
                        continue
                    if est_wait < remaining:
                        out("第 %d 轮：%s 空闲 %s/%s，当前排队 %s 人、预计等待 %s，"
                            "不足以覆盖剩余 %s，继续等"
                            % (rounds, name, idle, total,
                               data["waiting"] if data["waiting"] is not None else "?",
                               human_secs(est_wait), human_secs(remaining)))
                        continue
                    out("第 %d 轮：%s 预计等待 %s（已按保守系数 %s 折算）可覆盖剩余 %s，提前排队占位"
                        % (rounds, name, human_secs(est_wait), plan["factor"], human_secs(remaining)))
                    if self.try_queue(target, rounds, messages=data["messages"],
                                      idle=idle, total=total, wait_sec=wait_sec,
                                      reason="提前占位") and not continuous:
                        return True
            except NotLoggedIn:
                out("登录状态已失效，正在重新登录", "WARN")
                relogin(self.c, self.state)
            except ApiError as e:
                out("接口调用失败：%s" % e, "ERROR")
            except NetworkError as e:
                out("网络异常：%s" % e, "ERROR")
            time.sleep(interval + random.uniform(0, 0.2))

    def try_queue(self, target, rounds, messages=None, idle=None, total=None,
                  wait_sec=None, reason=""):
        """加入排队（不要求浴室满员）。是否该排由调用方按定时预约规则判断。

        返回 True 表示已排到位置并完成预约。
        """
        if time.time() < self._queue_block_until:
            return False                      # 上一轮被服务器拒绝，冷却期内不重试
        row = {"id": target.get("area_id"), "name": target.get("area_name", "")}
        if messages is None:
            try:
                messages = self.bus_messages(row["id"], retries=1)
            except (ApiError, NetworkError) as e:
                out("第 %d 轮：读取排队信息失败：%s" % (rounds, e), "WARN")
                return False

        busy = self.describe_busy(self.my_status(messages), row["name"])
        if busy:
            out("第 %d 轮：%s（不重复排队）" % (rounds, busy))
            return False

        waiting = self.waiting_count(messages)
        if waiting is None:
            if idle == 0:
                waiting = 0                   # 满员且总线未报排队 → 视为无人排队
                out("第 %d 轮：%s 已满员，总线未返回排队人数，按 0 人处理" % (rounds, row["name"]))
            else:
                out("第 %d 轮：%s 空闲 %s/%s，总线未提供排队人数，本轮跳过"
                    % (rounds, row["name"], idle, total))
                return False

        out("第 %d 轮：%s 空闲 %s/%s，当前排队 %s 人%s%s，加入排队"
            % (rounds, row["name"], idle, total, waiting,
               "（站点预计等待 %s）" % human_secs(wait_sec) if wait_sec else "",
               "，%s" % reason if reason else ""))
        try:
            result = self.queue_up(row["id"])
        except ApiError as e:
            if status_conflict(e):
                out("服务器拒绝排队：%s" % e.msg, "WARN")
                return False
            self._queue_block_until = time.time() + 300
            out("服务器拒绝排队：%s（5 分钟内不再尝试排队）" % e.msg, "WARN")
            return False

        ok, detail = self.judge_queue_result(result)
        if not ok:
            out("排队未成功：%s" % detail, "ERROR")
            return False
        out("排队成功：%s｜%s" % (row["name"], detail))
        self.notify("排队成功｜%s｜%s" % (row["name"], detail))
        return bool(self.watch_queue(row))

    @staticmethod
    def judge_queue_result(result):
        if not isinstance(result, dict):
            return True, "接口已受理"
        flag = result.get("result")
        if flag == "queued" or flag == 1 or flag is True or flag == "1":
            n = pick_field(result, POSITION_KEYS)
            wait = None
            for k in ("expectedWaitingTime", "expected_waiting_time", "waitTime"):
                if k in result:
                    try:
                        wait = int(float(result[k])) // 60
                    except (TypeError, ValueError):
                        pass
                    break
            detail = "排队状态已确认"
            if n is not None:
                detail += "，当前排位 %s 号" % n
            if wait:
                detail += "，预计等待 %s 分钟" % wait
            return True, detail
        msg = result.get("msg") or result.get("message") or ""
        return False, ("系统返回：%s" % msg if msg else "系统未确认排队（返回 %s）"
                       % json.dumps(result, ensure_ascii=False)[:120])

    def watch_queue(self, row):
        """排队跟踪：等待排到位置；若排到时间早于计划，可按设置自动取消重来。"""
        limit_min = float(self.state.get("queue_max_wait_min") or 0)
        deadline = time.time() + limit_min * 60 if limit_min > 0 else None
        interval = max(1.0, min(60.0, float(self.state.get("poll_interval", 1) or 1)))
        line("开始跟踪排队结果（每 %.0f 秒刷新一次，Ctrl+C 可停止本程序）" % interval)
        line("排队状态如需取消，可在主菜单选「取消排队 / 取消预约」")
        while True:
            try:
                messages = self.bus_messages(row["id"], retries=1)
                status = self.my_status(messages)
                state_name = status.get("state")
                if state_name in ("reserved", "running"):
                    device = status.get("device") or {}
                    info = {"area_id": row["id"],
                            "area_name": device.get("deviceAreaName") or row["name"],
                            "device": {"device_name": device.get("deviceNumber")
                                       or device.get("device_number"),
                                       "device_key": device.get("uuid") or device.get("deviceKey")},
                            "result": {"deviceAreaName": device.get("deviceAreaName") or row["name"],
                                       "deviceNumber": device.get("deviceNumber")
                                       or device.get("device_number"),
                                       "reserveTime": device.get("reserveTime")}}
                    plan = self.plan_current
                    if plan and self.state.get("auto_cancel_early", True):
                        ready_at = plan["target"].timestamp() - plan["lead"] * 60
                        if time.time() < ready_at - 30:
                            if self._early_cancel_count >= 3:
                                out("已连续 %d 次排到太早，停止自动取消（避免反复消耗预约次数），"
                                    "本次位置保留" % self._early_cancel_count, "WARN")
                                self.report_reservation(info, queued=True)
                                return True
                            ok, msg = self.cancel_current(row["id"])
                            self._early_cancel_count += 1
                            self._queue_block_until = time.time() + 300
                            out("排到的时间早于计划（%s 才需要到场），%s"
                                % ((plan["target"] - timedelta(minutes=plan["lead"])).strftime("%H:%M"),
                                   msg), "WARN")
                            out("已置为「不重复排队」5 分钟，之后再按条件重新排队")
                            return False
                    out("已排到位置，系统已完成预约")
                    self.report_reservation(info, queued=True)
                    return True
                if state_name and state_name not in ("queuing",):
                    out("排队已结束（当前状态：%s），返回空闲监控" % state_name, "WARN")
                    return False
                queue = status.get("queue") or {}
                position = pick_field(queue, POSITION_KEYS)
                if position is not None:
                    out("排队中：当前排位 %s 号" % position)
                else:
                    waiting = self.waiting_count(messages)
                    out("排队中：浴室当前排队 %s 人" % (waiting if waiting is not None else "未知"))
            except NotLoggedIn:
                out("登录状态已失效，正在重新登录", "WARN")
                relogin(self.c, self.state)
            except (ApiError, NetworkError) as e:
                out("排队状态查询失败：%s" % e, "WARN")

            if deadline and time.time() > deadline:
                out("排队等待已超过设定时长，返回空闲监控（排队状态保持，可手工取消）", "WARN")
                return False
            time.sleep(interval)

    # ---- 结果输出 ------------------------------------------------------

    def report_reservation(self, info, queued=False):
        result = info.get("result") or {}
        device = info.get("device") or {}
        area_name = result.get("deviceAreaName") or info.get("area_name") or "未知浴室"
        number = result.get("deviceNumber") or device.get("device_number") or device.get("device_name")
        confirmed = self.confirm_reservation(info)

        print("-" * 62)
        line("预约成功%s" % ("（排队自动排到）" if queued else ""))
        line("浴室：%s" % area_name)
        line("位置编号：%s" % (number if number is not None else "未提供"))
        if result.get("reserveTime"):
            line("预约时间：%s" % ts_text(result.get("reserveTime")))
        if result.get("maxWaitTime"):
            try:
                line("有效时限：%s 分钟" % (int(float(result["maxWaitTime"])) // 60))
            except (TypeError, ValueError):
                pass
        if confirmed:
            line("状态复核：已确认（%s，位置 %s）"
                 % (confirmed.get("area_name") or area_name,
                    confirmed.get("device_number") or number))
        else:
            line("状态复核：接口已返回预约结果，未取得额外确认")
        print("-" * 62)

        msg = "预约成功｜浴室=%s｜位置编号=%s" % (area_name, number)
        if result.get("reserveTime"):
            msg += "｜预约时间=%s" % ts_text(result.get("reserveTime"))
        self.notify(msg)
        return msg

    def notify(self, message):
        cmd = (self.state.get("notify_cmd") or "").strip()
        if not cmd:
            return
        try:
            subprocess.run(cmd, shell=True, env=dict(os.environ, HY_DREAM_MSG=message), timeout=60)
            out("通知命令已执行")
        except Exception as e:
            out("通知命令执行失败：%s" % e, "WARN")


# ============================================================ 登录流程

def is_rate_limited(e):
    """站点登录限流：短时间多次失败后要求等待 10 分钟。"""
    return isinstance(e, ApiError) and (str(e.code) in ("100", "1") or "重试" in (e.msg or ""))


def wait_rate_limit(state, msg=""):
    wait = int(state.get("rate_limit_wait", 600))
    out("站点提示：%s" % (msg or "请求过于频繁"), "WARN")
    out("程序将按站点要求等待 %d 分钟后再试（保持运行即可）" % max(1, wait // 60), "WARN")
    try:
        time.sleep(wait)
    except KeyboardInterrupt:
        raise NoInput()


def ensure_login(client, state, interactive=True):
    if client.restore_session(state.get("session")):
        try:
            client.api("UserApi", "getUserInfo")
            out("已使用本地登录状态（无需重复输入密码）")
            return True
        except NotLoggedIn:
            out("本地登录状态已过期，需要重新登录", "WARN")
        except ApiError:
            pass

    for _ in range(3):
        if interactive:
            account = state.get("account") or ask("账号（手机号或昵称）")
        else:
            account = state.get("account")
        password = state.get("password")
        if not account:
            return False
        if not password or account != state.get("account"):
            password = ask_secret("密码") if interactive else ""
        if not password:
            return False
        try:
            client.login(account, password)
            state["account"], state["password"] = account, password
            state["session"] = client.dump_session()
            save_state(state)
            out("登录成功")
            return True
        except ApiError as e:
            if e.code == 102:
                out("账号或密码不正确，请重新输入", "WARN")
                state["password"] = ""
                if not interactive:
                    return False
                continue
            if is_rate_limited(e):
                out("站点提示：%s" % e.msg, "WARN")
                if not interactive:
                    wait_rate_limit(state, e.msg)
                    continue
                state["password"] = ""
                out("连续输入错误会被站点暂时限制，请确认账号与密码", "WARN")
                continue
            raise
    out("登录未成功", "ERROR")
    return False


def safe_login(client, state, interactive=True):
    """登录并兜住网络 / 接口异常，返回是否成功（避免启动阶段因网络问题退出）。"""
    try:
        return ensure_login(client, state, interactive=interactive)
    except NetworkError as e:
        out("无法连接服务器：%s" % e, "ERROR")
        out("请检查网络连接后重试；如使用代理，请确认代理可用", "WARN")
    except ApiError as e:
        out("登录失败：%s" % e, "ERROR")
    return False


def relogin(client, state):
    account, password = state.get("account"), state.get("password")
    if not account or not password:
        raise NotLoggedIn(100090, "缺少已保存的账号信息")
    try:
        client.login(account, password)
    except ApiError as e:
        if is_rate_limited(e):
            wait_rate_limit(state, e.msg)
            client.login(account, password)
        else:
            raise
    state["session"] = client.dump_session()
    save_state(state)
    out("已重新登录")


# ============================================================ 界面：主菜单

def print_summary(state):
    account = state.get("account") or "未设置"
    if state.get("account"):
        account = account[:3] + "****" + account[-4:] if len(account) > 7 else account
    targets = "、".join(t["area_name"] for t in state.get("targets") or []) or "未设置"
    print("   账号：%s" % account)
    print("   目标浴室：%s" % targets)
    plan_raw = (state.get("target_time") or "").strip()
    if plan_raw:
        print("   定时预约：%s 开始洗 ｜ 性别 %s ｜ 预计 %s 分钟 ｜ 到场准备 %s 分钟 ｜ 保守系数 %s"
              % (plan_raw, GENDER_TEXT.get(state.get("gender", "auto"), "自动识别"),
                 state.get("avg_bath_minutes") or "按性别默认",
                 state.get("arrive_lead_min", 5), state.get("conservative_factor", 0.8)))
    else:
        print("   定时预约：未设置（启动前必须设置）")
    print("   检测周期：每 %s 秒" % state.get("poll_interval", 1))
    if (state.get("notify_cmd") or "").strip():
        print("   通知命令：已配置")


def set_account(state, client):
    clear()
    banner()
    title("账号与密码")
    current = state.get("account") or ""
    if current:
        line("当前账号：%s" % current)
    account = ask("账号（手机号或昵称）", default=current or None)
    if not account:
        line("未输入账号，已取消")
        return state
    password = ask_secret("密码")
    if not password:
        line("未输入密码，已取消")
        return state
    state["account"], state["password"] = account, password
    state["session"] = {}
    client.session_id = ""
    client.jar = http.cookiejar.CookieJar()
    save_state(state)
    if safe_login(client, state, interactive=True):
        Bot(client, state).whoami()
    else:
        out("账号信息已保存，但登录未通过，请在网络稳定后重试", "WARN")
    pause()
    return state


def set_targets(state, client):
    clear()
    banner()
    title("目标浴室与设备类型")
    bot = Bot(client, state)
    try:
        bot.whoami()
        bot.resolve_org_area()
        bot.resolve_device_type(interactive=True)
        areas = bot.areas()
    except (ApiError, NetworkError) as e:
        out("读取浴室列表失败：%s" % e, "ERROR")
        pause()
        return state
    if not areas:
        out("该校区未返回任何浴室", "ERROR")
        pause()
        return state

    default_id = bot.user.get("default_device_area_id")
    saved = [str(t["area_id"]) for t in state.get("targets") or []]

    print()
    print("   序号  浴室名称                    空闲/总计   说明")
    print("   " + "-" * 58)
    default_index = None
    for i, a in enumerate(areas, 1):
        marks = []
        if str(a["id"]) in saved:
            marks.append("上次所选")
        if default_id and str(a["id"]) == str(default_id):
            marks.append("账号默认")
            default_index = i
        print("   %-5s %-26s %-11s %s" % (i, a["name"],
                                          "%s/%s" % (a["idle"], a["total"]),
                                          "、".join(marks)))
    print()
    line("可多选，多个编号之间使用逗号分隔，例如 1,3")
    if default_index:
        line("直接回车 = 账号默认浴室（第 %d 项）" % default_index)
    elif saved:
        line("直接回车 = 沿用上次选择")
    else:
        line("直接回车 = 第 1 项")

    while True:
        raw = ask("请输入浴室序号")
        if not raw:
            if default_index:
                chosen = [areas[default_index - 1]]
            elif saved:
                chosen = [a for a in areas if str(a["id"]) in saved] or [areas[0]]
            else:
                chosen = [areas[0]]
            break
        try:
            idxs = [int(x.strip()) for x in raw.replace("，", ",").split(",") if x.strip()]
            chosen = [areas[i - 1] for i in idxs if 1 <= i <= len(areas)]
            if not chosen:
                raise ValueError
            break
        except (ValueError, IndexError):
            line("输入无效，请填写上方序号。")

    state["targets"] = [{"area_id": a["id"], "area_name": a["name"]} for a in chosen]
    save_state(state)
    out("已选择目标浴室：%s" % "、".join(a["name"] for a in chosen))
    pause()
    return state


def set_bath_plan(state, client):
    """定时预约设置：计划洗澡时间 / 性别 / 预计用时 / 到场准备 / 保守系数 / 放弃时限。"""
    clear()
    banner()
    title("定时预约设置")
    line("定时预约只有一个入口：设定你打算几点开始洗澡，其余由程序判断。")
    line("· 到了该拿位置的时间：有空位直接抢位置，满员则加入排队")
    line("· 还没到时间：只在预计等待能覆盖剩余时间时提前排队占位（宁可晚排，不早到）")
    print()
    if (state.get("target_time") or "").strip():
        line("当前设置：%s 开始洗 ｜ 性别 %s ｜ 预计 %s 分钟 ｜ 到场准备 %s 分钟 ｜ 保守系数 %s ｜ 放弃时限 %s 分钟"
             % (state["target_time"], GENDER_TEXT.get(state.get("gender", "auto"), "自动识别"),
                state.get("avg_bath_minutes") or "按性别默认", state.get("arrive_lead_min", 5),
                state.get("conservative_factor", 0.8), state.get("give_up_min", 30)))
    else:
        line("当前设置：尚未设置计划洗澡时间")
    print()

    default_time = state.get("target_time") or (datetime.now() + timedelta(hours=1)).strftime("%H:%M")
    while True:
        raw = ask("计划开始洗澡时间 HH:MM", default=default_time)
        try:
            hh, mm = [int(x) for x in raw.replace("：", ":").split(":")[:2]]
            if not (0 <= hh <= 23 and 0 <= mm <= 59):
                raise ValueError
            state["target_time"] = "%02d:%02d" % (hh, mm)
            break
        except ValueError:
            line("格式不对，请按 HH:MM 填写，例如 21:30。")

    print()
    default_choice = {"auto": 1, "male": 2, "female": 3}.get(state.get("gender", "auto"), 1)
    choice = ask_choice("性别（用于取平均洗澡时长与校验浴室限制）", [
        (1, "自动识别（从账号读取）", "推荐"),
        (2, "男", ""),
        (3, "女", ""),
    ], default_choice)
    state["gender"] = {"1": "auto", "2": "male", "3": "female"}[choice]

    gender = state["gender"]
    if gender == "auto":
        try:
            gender = Bot(client, state).resolve_gender()
            line("账号读取到的性别：%s" % GENDER_TEXT.get(gender, gender))
        except Exception:
            gender = "unknown"
        if gender == "unknown":
            line("账号里没有性别信息（保密），将按通用值估算")

    default_min = AVG_BATH_MINUTES.get(gender, 15)
    while True:
        raw = ask("每次洗澡预计用时（分钟）", default=str(state.get("avg_bath_minutes") or default_min))
        try:
            minutes = int(raw)
            if not (1 <= minutes <= 240):
                line("请填 1~240 之间的分钟数。")
                continue
            state["avg_bath_minutes"] = minutes
            break
        except ValueError:
            line("请输入数字。")

    while True:
        raw = ask("到场准备时间（分钟：拿到位置后到进浴室开门的时间）",
                  default=str(state.get("arrive_lead_min", 5)))
        try:
            state["arrive_lead_min"] = max(0, min(120, int(raw)))
            break
        except ValueError:
            line("请输入数字。")

    while True:
        raw = ask("保守系数（0.1~1.0，越小越保守＝越晚排队，避免提前把你叫走）",
                  default=str(state.get("conservative_factor", 0.8)))
        try:
            factor = float(raw)
            if not (0.1 <= factor <= 1.0):
                line("请填 0.1~1.0 之间。")
                continue
            state["conservative_factor"] = factor
            break
        except ValueError:
            line("请输入数字。")

    while True:
        raw = ask("超过计划时间多少分钟还没拿到位置就停止",
                  default=str(state.get("give_up_min", 30)))
        try:
            state["give_up_min"] = max(1, int(raw))
            break
        except ValueError:
            line("请输入数字。")

    save_state(state)
    print()
    try:
        bot = Bot(client, state)
        plan = bot.plan()
        ready = plan["target"] - timedelta(minutes=plan["lead"])
        out("已保存：%s 开始洗（%s 分钟），最早 %s 拿位置"
            % (plan["target"].strftime("%H:%M"), plan["avg_min"], ready.strftime("%H:%M")))
        try:                                  # 立即跑一次合法性检查
            types = bot.device_types()
            areas = bot.areas()
            row = next((a for a in areas if str(a["id"]) == str(
                (state.get("targets") or [{}])[0].get("area_id"))), None)
            ok, notes = bot.validate_plan(plan, row, types)
            line("合法性检查：%s" % ("通过" if ok else "不通过"))
            for note in notes:
                line("  " + note)
        except (ApiError, NetworkError) as e:
            line("合法性检查未能完成（%s），启动监控时会再检查一次" % e)
    except ApiError as e:
        out("时间设置有问题：%s" % e, "WARN")
    pause()
    return state


def set_misc(state):
    clear()
    banner()
    title("检测周期与结果通知")
    while True:
        raw = ask("检测周期（秒，范围 1~60）", default=state.get("poll_interval", 1))
        try:
            value = int(float(raw))
            if not (1 <= value <= 60):
                line("请填 1~60 之间的秒数。")
                continue
            state["poll_interval"] = value
            break
        except ValueError:
            line("请输入数字。")
    if state["poll_interval"] <= 1:
        line("提示：1 秒周期＝每秒 1 个请求。程序已把每轮压到只发 1 个总线请求，")
        line("      但长时间高频仍可能被站点安全策略拦截，被拦时会自动退避重试。")
    print()
    line("结果通知：预约成功后执行指定命令，消息内容存放在环境变量 HY_DREAM_MSG 中。")
    raw = ask("通知命令（留空表示不启用）", default=state.get("notify_cmd") or None)
    state["notify_cmd"] = "" if raw in (None, "", "无") else raw
    save_state(state)
    out("已保存：检测周期 %s 秒%s" % (state["poll_interval"],
                                    "，已配置通知命令" if state["notify_cmd"] else "，未配置通知命令"))
    pause()
    return state


def screen_open_with():
    """修复 Windows 下 .py 文件的默认打开方式（仅影响当前用户）。"""
    if os.name != "nt":
        out("该设置仅适用于 Windows", "WARN")
        pause()
        return
    clear()
    banner()
    title("启动方式修复")
    try:
        import winreg
    except ImportError:
        out("当前环境无法读取系统设置", "WARN")
        pause()
        return
    try:
        current = winreg.QueryValue(winreg.HKEY_CLASSES_ROOT, ".py")
    except FileNotFoundError:
        current = ""
    if current == "Python.File":
        line("当前双击 .py 文件即由 Python 直接运行，无需修复。")
        pause()
        return
    line("当前双击 .py 文件时，系统使用的打开方式：%s" % (current or "未知程序"))
    line("修复后双击本程序即可直接运行，不会打开其他软件。")
    line("该修改仅作用于当前用户，可随时还原。")
    print()
    if not confirm("是否修复", default_yes=True):
        return
    try:
        key = winreg.CreateKeyEx(winreg.HKEY_CURRENT_USER, r"Software\Classes\.py", 0,
                                 winreg.KEY_SET_VALUE)
        winreg.SetValueEx(key, "", 0, winreg.REG_SZ, "Python.File")
        winreg.CloseKey(key)
        now = winreg.QueryValue(winreg.HKEY_CLASSES_ROOT, ".py")
        if now == "Python.File":
            out("修复完成，双击本程序即可直接运行")
            try:
                line("调用方式：%s" % winreg.QueryValue(
                    winreg.HKEY_CLASSES_ROOT, r"Python.File\shell\open\command"))
            except FileNotFoundError:
                pass
        else:
            out("修复未生效（当前仍为 %s）" % now, "WARN")
    except OSError as e:
        out("修复失败：%s" % e, "WARN")
    line("如需还原：系统设置 → 应用 → 默认应用 → 按文件类型选择 → .py")
    pause()


# ============================================================ 界面：主流程

def live_status(client, state, ttl=15, force=False):
    """读取目标浴室的实时状态：空闲/总计，满员时显示当前排队人数。

    结果缓存 ttl 秒，避免每次刷新菜单都请求接口。返回 [(名称, 状态文本, 标签)]。
    """
    targets = state.get("targets") or []
    if not targets:
        return []
    if not client.session_id:
        client.restore_session(state.get("session"))
    if not client.session_id:
        return [(t["area_name"], "未登录（启动监控时会自动登录）", "warn") for t in targets]

    key = "|".join(str(t.get("area_id")) for t in targets)
    now = time.time()
    if not force and _STATUS_CACHE.get("key") == key and (now - _STATUS_CACHE.get("at", 0)) < ttl:
        return _STATUS_CACHE.get("lines", [])

    lines = []
    try:
        bot = Bot(client, state)
        bot.org_area_id = state.get("org_area_id")
        bot.device_type_key = state.get("device_type_key")
        if not bot.org_area_id or not bot.device_type_key:
            bot.bootstrap(verbose=False)
        area_map = {str(a["id"]): a for a in bot.areas(retries=2)}
        for t in targets:
            row = area_map.get(str(t["area_id"]))
            if row is None:
                lines.append((t["area_name"], "已不在可预约列表中", "warn"))
                continue
            idle, total = row["idle"], row["total"]
            messages = []
            try:
                messages = bot.bus_messages(row["id"], retries=2)
            except (ApiError, NetworkError):
                messages = []
            mine = bot.describe_busy(bot.my_status(messages), row["name"])
            if mine:
                lines.append((row["name"], "你 " + mine, "mine"))
            if idle == 0:
                waiting = bot.waiting_count(messages, row)
                if waiting is None:
                    lines.append((row["name"], "已满员（0/%s）" % total, "full"))
                else:
                    lines.append((row["name"], "已满员（0/%s）· 当前排队 %s 人" % (total, waiting), "full"))
            else:
                lines.append((row["name"], "空闲 %s/%s" % (idle, total), "ok"))
    except NotLoggedIn:
        lines = [(t["area_name"], "登录状态已失效（启动监控时重新登录）", "warn") for t in targets]
    except (ApiError, NetworkError) as e:
        lines = [(t["area_name"], "实时状态读取失败（%s）" % e, "warn") for t in targets]

    _STATUS_CACHE["at"], _STATUS_CACHE["key"], _STATUS_CACHE["lines"] = now, key, lines
    return lines


def print_live_status(client, state):
    """在主页面输出实时状态。"""
    lines = live_status(client, state)
    if not lines:
        return
    stamp = datetime.now().strftime("%H:%M:%S")
    if len(lines) == 1 and lines[0][2] == "ok":
        print("   实时状态（%s）：%s" % (stamp, lines[0][1]))
    else:
        print("   实时状态（%s）：" % stamp)
        for name, text, tag in lines:
            if tag == "mine":
                print("      %s" % text)
            else:
                print("      %-20s %s" % (name, text))


def screen_cancel(state, client):
    """取消当前的排队或预约。"""
    clear()
    banner()
    title("取消排队 / 取消预约")
    if not is_configured(state):
        line("尚未完成配置，无法查询账号状态。")
        pause()
        return
    if not safe_login(client, state):
        pause()
        return
    state["session"] = client.dump_session()
    save_state(state)
    bot = Bot(client, state)
    try:
        bot.bootstrap(verbose=False)
        found = None
        for target in state.get("targets") or []:
            status = bot.busy_status(target["area_id"])
            text = bot.describe_busy(status, target["area_name"])
            if text:
                found = (target, text)
                break
        if not found:
            line("当前账号没有排队或预约，无需取消。")
            pause()
            return
        target, text = found
        line("当前状态：%s" % text)
        print()
        line("取消后：排队中会退出队列；已预约会立即释放该位置，")
        line("（即使不取消，预约后未在规定时间内到场，站点也会自动释放。）")
        print()
        if not confirm("确认取消", default_yes=False):
            line("已放弃取消，状态保持不变。")
            pause()
            return
        ok, msg = bot.cancel_current(target["area_id"])
        out(msg, "INFO" if ok else "ERROR")
        if ok:
            try:
                status = bot.busy_status(target["area_id"])
                line("复核结果：%s" % (bot.describe_busy(status, target["area_name"]) or "已无占用"))
            except (ApiError, NetworkError):
                pass
    except (ApiError, NetworkError) as e:
        out("查询账号状态失败：%s" % e, "ERROR")
    pause()
    return


def screen_main(state, client):
    while True:
        clear()
        banner()
        title("主菜单")
        print_summary(state)
        print_live_status(client, state)
        print()
        choice = ask_choice("请选择", [
            (1, "启动自动预约监控", ""), (2, "修改运行设置", ""),
            (3, "系统自检", ""), (4, "退出程序", ""),
        ], 1)

        if choice == "4":
            return 0
        if choice == "3":
            clear()
            banner()
            title("系统自检")
            self_test()
            pause()
            continue
        if choice == "2":
            while True:
                clear()
                banner()
                title("修改运行设置")
                print_summary(state)
                print_live_status(client, state)
                print()
                sub = ask_choice("请选择设置项", [
                    (1, "账号与密码", ""), (2, "目标浴室与设备类型", ""),
                    (3, "定时预约设置", ""), (4, "检测周期与结果通知", ""),
                    (5, "启动方式修复", ""), (0, "返回", ""),
                ], 0)
                if sub == "0":
                    break
                if sub == "1":
                    set_account(state, client)
                elif sub == "2":
                    if safe_login(client, state):
                        state["session"] = client.dump_session()
                        set_targets(state, client)
                elif sub == "3":
                    set_bath_plan(state, client)
                elif sub == "4":
                    set_misc(state)
                elif sub == "5":
                    screen_open_with()
            continue

        # 启动监控
        if not is_configured(state):
            clear()
            banner()
            title("配置未完成")
            line("启动监控前需要先完成以下配置：")
            print()
            if not state.get("account") or not state.get("password"):
                print("   · 账号与密码")
            if not state.get("targets"):
                print("   · 目标浴室")
            print()
            line("请进入主菜单「修改运行设置」完成配置。")
            pause()
            continue
        if not safe_login(client, state):
            pause()
            continue
        state["session"] = client.dump_session()
        save_state(state)
        monitor_flow(state, client)
        continue


def fast_start(state, client):
    """配置完备时的快速启动：倒计时后自动进入监控，可中断。"""
    seconds = int(state.get("fast_start_seconds", 5))
    clear()
    banner()
    title("快速启动")
    print_summary(state)
    print_live_status(client, state)
    print()
    if seconds > 0:
        line("配置已就绪，%d 秒后自动启动监控" % seconds)
        line("如不启动：按 S 进入设置，按 Q 退出程序")
        print()
        start = time.time()
        while True:
            remain = seconds - (time.time() - start)
            if remain <= 0:
                break
            sys.stdout.write("\r   启动倒计时：%2d 秒 " % int(remain + 0.999))
            sys.stdout.flush()
            key = poll_key()
            if key:
                print()
                key = key.lower()
                if key == "s":
                    return "settings"
                if key in ("q", "0"):
                    return "quit"
                if key in ("\r", "\n", " "):
                    break
            time.sleep(0.15)
        print()
    if not safe_login(client, state):
        return "settings"
    state["session"] = client.dump_session()
    save_state(state)
    return "monitor"


def poll_key():
    """非阻塞读取一个按键（仅交互模式有效）。"""
    if not can_interact():
        return None
    try:
        if os.name == "nt":
            import msvcrt
            if msvcrt.kbhit():
                return msvcrt.getwch()
            return None
        import select
        if select.select([sys.stdin], [], [], 0)[0]:
            return sys.stdin.read(1)
    except Exception:
        return None
    return None


def monitor_flow(state, client):
    bot = Bot(client, state)
    try:
        bot.monitor()
        out("预约流程已结束")
    except NotLoggedIn:
        out("登录状态已失效，请重新登录后再启动", "WARN")
    except KeyboardInterrupt:
        raise
    if can_interact():
        pause("按回车返回主菜单")


# ============================================================ 自检

class SimClient:
    """自检用的模拟客户端：不联网，按脚本返回接口数据。

    可模拟：有无空位、排队人数与站点预计等待、账号是否已有设备。
    """

    def __init__(self, idle=0, wait_sec=240, queue_people=2, already_reserved=False):
        self.idle = idle
        self.wait_sec = wait_sec
        self.queue_people = queue_people
        self.reserved = bool(already_reserved)
        self.queued = False
        self.q_polls = 0
        self.reserve_calls = 0
        self.queue_calls = 0

    @staticmethod
    def _device_info():
        return {"uuid": "dev-77", "deviceNumber": "77", "deviceAreaName": "4号楼1层（男）",
                "reserveTime": 1789555000, "device_type_key": "faucet"}

    def api(self, mod, act, data=None, retries=3):
        if act == "getUserInfo":
            return {"id": 1, "mobile": "13800000000", "user_nickname": "模拟账号",
                    "available_balance": "0.00", "sex": "1",
                    "default_org_area_id": 105, "default_device_area_id": 12}
        if act == "getSetting":
            return {"checkBodyTemperature": "0", "enableDistributedEvent": "0"}
        if act == "selectDeviceTypeByOrgAreaId":
            return [{"device_type_key": "faucet", "device_type_name": "超级澡堂",
                     "need_reserve": "1", "max_run_time": "3600", "max_reserve_times": "10"}]
        if act == "selectDeviceAreasWithDeviceState":
            return [{"device_area_id": 12, "device_area_name": "4号楼1层（男）",
                     "gender_limit": "male", "status": "1",
                     "idleNum": self.idle, "totalNum": max(self.idle, 0) + 4}]
        if act == "selectDeviceAreas":
            return [{"device_area_id": 12, "device_area_name": "4号楼1层（男）"}]
        if act == "selectDevicesByAreaId":
            return [{"device_key": "dev-31", "device_name": "31", "device_status": "ready"}]
        if act == "exchangeMsg":
            devices = [{"uuid": "d%d" % i,
                        "deviceStatus": "ready" if i < self.idle else "running"}
                       for i in range(max(self.idle, 0) + 4)]
            messages = [{"id": 0, "type": "deviceState", "content": devices},
                        {"id": 1, "type": "waitingInfo",
                         "content": {"queuingNumber": self.queue_people,
                                     "expectedWaitingTime": self.wait_sec}}]
            if self.reserved:
                name, device, queue = "reserved", self._device_info(), ""
            elif self.queued:
                self.q_polls += 1
                if self.q_polls >= 2:
                    self.reserved = True
                    name, device, queue = "reserved", self._device_info(), ""
                else:
                    name, device, queue = "queuing", "", {"queuingNumber": self.queue_people}
            else:
                name, device, queue = "normal", "", ""
            messages.append({"id": 2, "type": "userState",
                             "content": {"userState": name, "deviceInfo": device,
                                         "queueInfo": queue, "remainTime": 120}})
            return messages
        if act == "queueUp":
            self.queue_calls += 1
            self.queued = True
            return {"result": "queued", "queuingNumber": self.queue_people,
                    "expectedWaitingTime": self.wait_sec}
        if act == "cancelQueue":
            self.queued = False
            return {"result": 1}
        if act == "cancelReserve":
            self.reserved = False
            return {"result": 1}
        if act == "reserve":
            self.reserve_calls += 1
            self.reserved = True
            return {"deviceNumber": "31", "deviceAreaName": "4号楼1层（男）",
                    "reserveTime": 1789554900, "maxWaitTime": 1200}
        if act == "createLog":
            return []
        raise ApiError(-9, "模拟环境未定义接口 %s/%s" % (mod, act))

    # 供界面冒烟测试使用（模拟登录态存取）
    def restore_session(self, session):
        return True

    def dump_session(self):
        return {"name": "PHPSESSID", "id": "sim", "cookies": []}


def simulate_flow(idle, plan_min_away=3, lead=5, wait_sec=240, already_reserved=False,
                  expect="reserve", max_rounds=6):
    """在没有网络的情况下走一遍定时预约流程。

    expect: reserve=抢到空位 / queue=排队后预约成功 / queue_early=提前排队但被叫到太早而自动取消
            none=不做任何动作
    """
    global _LOG_DISABLED
    import contextlib
    import io

    class _Bot(Bot):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.rounds = 0

        def snapshot(self, target):
            self.rounds += 1
            if self.rounds > max_rounds:
                raise KeyboardInterrupt("轮次上限")
            return super().snapshot(target)

        def validate_plan(self, plan, row=None, types=None):
            return True, []          # 合法性校验由单独的自检项覆盖，这里只测动作逻辑

    target = datetime.now() + timedelta(minutes=plan_min_away)
    state = dict(DEFAULT_STATE)
    state.update({"account": "selftest", "password": "selftest", "device_type_key": "faucet",
                  "targets": [{"area_id": 12, "area_name": "4号楼1层（男）"}],
                  "target_time": target.strftime("%H:%M"),
                  "arrive_lead_min": lead, "conservative_factor": 0.8,
                  "give_up_min": 120, "poll_interval": 1})
    client = SimClient(idle=idle, wait_sec=wait_sec, already_reserved=already_reserved)

    previous = _LOG_DISABLED
    _LOG_DISABLED = True
    try:
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            try:
                done = _Bot(client, state).monitor()
            except KeyboardInterrupt:
                done = "loop"
        text = buffer.getvalue()
        result = {"done": done, "text": text, "client": client}
    except Exception as e:
        _LOG_DISABLED = previous
        out("模拟流程异常：%s" % e, "ERROR")
        return False
    _LOG_DISABLED = previous

    if expect == "reserve":
        return result["done"] is True and "预约成功" in text
    if expect == "queue":
        return "排队成功" in text and "预约成功" in text
    if expect == "queue_early":
        return "排队成功" in text and "早于计划" in text
    if expect == "none":
        return (client.reserve_calls == 0 and client.queue_calls == 0
                and "预约成功" not in text and "排队成功" not in text)
    return False


def menu_smoke_test():
    """离线冒烟：把各设置界面依次跑一遍。

    菜单层不参与流程模拟，也不联网，却最容易出"函数缺失/签名不符"这类问题，
    所以单独跑一遍，任何异常都算失败。
    """
    import contextlib
    import io

    answers = []
    stubs = {
        "ask": lambda prompt, default=None: (answers.pop(0) if answers else (default if default is not None else "")),
        "ask_choice": lambda prompt, options, default=1: str(default),
        "ask_secret": lambda prompt: "placeholder",
        "confirm": lambda prompt, default_yes=False: True,
        "pause": lambda text="": None,
        "clear": lambda: None,
        "banner": lambda: None,
        "title": lambda text: None,
        "line": lambda text="": None,
        "out": lambda *a, **k: None,
    }
    saved = {k: globals().get(k) for k in stubs}
    errors = []
    try:
        globals().update(stubs)
        client = SimClient(idle=2)
        base = dict(DEFAULT_STATE)
        base.update({"account": "selftest", "password": "selftest",
                     "device_type_key": "faucet",
                     "targets": [{"area_id": 12, "area_name": "4号楼1层（男）"}],
                     "target_time": "21:30"})
        cases = [
            ("定时预约设置", lambda: set_bath_plan(dict(base), client)),
            ("检测周期与通知", lambda: set_misc(dict(base))),
            ("目标浴室选择", lambda: set_targets(dict(base), client)),
            ("取消排队/预约", lambda: screen_cancel(dict(base), client)),
            ("启动方式修复检查", lambda: screen_open_with()),
        ]
        for name, fn in cases:
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    fn()
            except Exception as e:
                errors.append("%s → %s: %s" % (name, type(e).__name__, e))
    finally:
        for key, value in saved.items():
            if value is not None:
                globals()[key] = value
    if errors:
        for item in errors:
            out("菜单冒烟失败：" + item, "ERROR")
    return not errors


def self_test():
    ok = True

    plain = '{"header":{"auth":"00001"},"data":{"code":102,"msg":"密码不正确","data":[]}}'
    checks = [
        ("接口返回解析（明文）", HydreamClient._parse(plain)["data"]["code"] == 102),
        ("接口返回解析（编码）", HydreamClient._parse(
            base64.b64encode(plain.encode()).decode())["data"]["code"] == 102),
    ]
    try:
        HydreamClient._parse("<html>Access Denied!</html>")
        checks.append(("安全拦截识别", False))
    except ApiError as e:
        checks.append(("安全拦截识别", e.code == -2))

    cond_ok = True
    for value, th, cond, want in [(1, 1, "le", True), (0, 1, "le", True), (2, 1, "le", False),
                                  (1, 1, "eq", True), (2, 1, "eq", False), (3, 1, "ge", True),
                                  (0, 2, "ge", False)]:
        if matched(value, th, cond) != want:
            cond_ok = False
    checks.append(("触发条件判断", cond_ok))

    a1 = normalize_areas([{"device_area_id": 7, "device_area_name": "4号楼1层（男）",
                           "idleNum": "3", "totalNum": "8"}])[0]
    a2 = normalize_areas([{"deviceAreaId": 9, "freeNum": 0, "total_num": 6,
                           "queuingNumber": 4}])[0]
    checks.append(("浴室状态解析", a1["idle"] == 3 and a1["total"] == 8
                   and a2["idle"] == 0 and a2["total"] == 6 and a2["waiting"] == 4))

    msgs = [{"id": 1, "type": "waitingInfo", "content": {"queuingNumber": 3,
                                                         "expectedWaitingTime": 240}},
            {"id": 2, "type": "userState", "content": {"userState": "queuing",
                                                       "queueInfo": {"queuingNumber": 3}}}]
    bot_stub = Bot(HydreamClient(), dict(DEFAULT_STATE))
    checks.append(("排队人数读取", bot_stub.waiting_count(msgs) == 3))
    checks.append(("本人状态读取", bot_stub.my_status(msgs).get("state") == "queuing"))
    checks.append(("排队结果判定",
                   Bot.judge_queue_result({"result": "queued", "queuingNumber": 3})[0]
                   and not Bot.judge_queue_result({"result": "fail", "msg": "已满员"})[0]))

    c1 = HydreamClient()
    c1.set_cookie("PHPSESSID", "sample123")
    c1.session_name, c1.session_id = "PHPSESSID", "sample123"
    c2 = HydreamClient()
    checks.append(("登录状态保存与复用",
                   c2.restore_session(c1.dump_session()) and c2.session_id == "sample123"))

    checks.append(("流程模拟：到时间且有空位 → 直接抢位置",
                   simulate_flow(idle=1, plan_min_away=3, lead=5, expect="reserve")))
    checks.append(("流程模拟：到时间但满员 → 加入排队并排到",
                   simulate_flow(idle=0, plan_min_away=3, lead=5, expect="queue")))
    checks.append(("流程模拟：未到时间但预计等待够长 → 提前排队占位",
                   simulate_flow(idle=3, plan_min_away=60, lead=5, wait_sec=5400,
                                 expect="queue_early")))
    checks.append(("流程模拟：未到时间且等待不足 → 不做任何动作",
                   simulate_flow(idle=3, plan_min_away=60, lead=5, wait_sec=600,
                                 expect="none")))
    checks.append(("流程模拟：已有预约 → 不重复操作",
                   simulate_flow(idle=1, plan_min_away=3, lead=5, already_reserved=True,
                                 expect="none")))

    sim = SimClient(idle=1)
    check_bot = Bot(sim, dict(DEFAULT_STATE, device_type_key="faucet"))
    check_bot.device_type_key = "faucet"
    types = sim.api("DeviceAreaApi", "selectDeviceTypeByOrgAreaId")
    area = normalize_areas(sim.api("DeviceAreaApi", "selectDeviceAreasWithDeviceState"))[0]
    now = datetime.now()
    plan_ok = {"raw": "x", "target": now + timedelta(minutes=30), "rolled": False,
               "gender": "male", "avg_min": 10, "lead": 5, "factor": 0.8, "give_up": 30}
    plan_late = dict(plan_ok, target=now + timedelta(minutes=2))      # 距到场准备只剩 2 分钟
    plan_long = dict(plan_ok, avg_min=90)                             # 超过站点单次 60 分钟
    plan_sex = dict(plan_ok, gender="female")                          # 浴室限男
    ok_a, _ = check_bot.validate_plan(plan_ok, area, types)
    ok_b, n_b = check_bot.validate_plan(plan_late, area, types)
    ok_c, n_c = check_bot.validate_plan(plan_long, area, types)
    ok_d, n_d = check_bot.validate_plan(plan_sex, area, types)
    checks.append(("预约时间合法性校验（来不及 / 超时长 / 性别不符）",
                   ok_a and not ok_b and not ok_c and not ok_d
                   and any("来不及" in x for x in n_b)
                   and any("最长" in x for x in n_c)
                   and any("性别" in x for x in n_d)))

    checks.append(("条件退化识别（空闲 ≥ 0 属无条件）",
                   cond_issue("ge", 0, "空闲位置") is not None
                   and cond_issue("le", 0, "空闲位置") is not None
                   and cond_issue("le", 1, "空闲位置") is None))
    base = 1000000.0
    target = base + 3600                      # 计划 1 小时后开始洗（到场准备 5 分钟 → 55 分钟后才该拿位置）
    r1, q1, _ = plan_gate(base, target, 5, wait_sec=None)
    r2, q2, _ = plan_gate(base, target, 5, wait_sec=3600, factor=1.0)
    r3, q3, _ = plan_gate(base, target, 5, wait_sec=1800, factor=1.0)
    r4, q4, _ = plan_gate(target - 180, target, 5, wait_sec=None)
    r5, q5, _ = plan_gate(base, target, 5, wait_sec=3600, factor=0.8)
    checks.append(("时间计划闸门（保守策略）",
                   (r1 is False and q1 is False)          # 未知等待 → 不动
                   and (r2 is False and q2 is True)       # 等待够长 → 可排队、不可抢位
                   and (r3 is False and q3 is False)      # 等待不够 → 再等等
                   and (r4 is True and q4 is True)        # 进入窗口 → 可抢位
                   and (r5 is False and q5 is False)))    # 保守系数把边缘情况压成"不排"

    checks.append(("状态冲突识别（101212）",
                   status_conflict(ApiError("101212", "你同时只能使用一台设备"))
                   and not status_conflict(ApiError(102, "密码不正确"))))

    # 静态审计：被调用的函数必须都已定义（防"整个函数被误删"这类自检盲区）
    try:
        import ast as _ast
        tree = _ast.parse(open(__file__, encoding="utf-8").read())
        icons = {n.name for n in _ast.walk(tree)
                 if isinstance(n, (_ast.FunctionDef, _ast.AsyncFunctionDef, _ast.ClassDef))}
        icons |= {t.id for n in _ast.walk(tree) if isinstance(n, _ast.Assign)
                  for t in n.targets if isinstance(t, _ast.Name)}
        for n in _ast.walk(tree):
            if isinstance(n, _ast.Import):
                icons |= {(a.asname or a.name.split(".")[0]) for a in n.names}
            if isinstance(n, _ast.ImportFrom):
                icons |= {(a.asname or a.name) for a in n.names}
        import builtins as _builtins
        icons |= set(dir(_builtins))
        # 局部名（函数参数、赋值目标、循环变量、with as、except as、推导式变量）也要算进来
        for node in _ast.walk(tree):
            if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                for arg in (node.args.args + node.args.kwonlyargs + node.args.posonlyargs):
                    icons.add(arg.arg)
                if node.args.vararg:
                    icons.add(node.args.vararg.arg)
                if node.args.kwarg:
                    icons.add(node.args.kwarg.arg)
            if isinstance(node, _ast.Name) and isinstance(node.ctx, _ast.Store):
                icons.add(node.id)
            if isinstance(node, _ast.ExceptHandler) and node.name:
                icons.add(node.name)
            if isinstance(node, _ast.comprehension) and isinstance(node.target, _ast.Name):
                icons.add(node.target.id)
            if isinstance(node, _ast.withitem) and isinstance(node.optional_vars, _ast.Name):
                icons.add(node.optional_vars.id)
        unknown = sorted({n.func.id for n in _ast.walk(tree) if isinstance(n, _ast.Call)
                          and isinstance(n.func, _ast.Name) and n.func.id not in icons})
        checks.append(("静态审计：所有被调用的函数均已定义", not unknown))
        if unknown:
            out("未定义的函数：%s" % "、".join(unknown), "ERROR")
    except Exception as e:
        checks.append(("静态审计：所有被调用的函数均已定义", False))
        out("静态审计失败：%s" % e, "ERROR")

    checks.append(("界面冒烟：各设置界面可正常执行（不联网）", menu_smoke_test()))

    print()
    for name, passed in checks:
        print("   [%s] %s" % ("通过" if passed else "失败", name))
        ok = ok and passed
    print()
    print("   自检结果：%s" % ("全部通过" if ok else "存在失败项，请联系维护人员"))
    return ok


# ============================================================ 入口

def headless(client, state):
    """无交互环境（计划任务、后台启动）：直接以已保存配置运行。"""
    if not is_configured(state):
        out("当前环境无键盘输入，且配置不完整，无法启动", "ERROR")
        return 1
    out("检测到无交互环境，使用已保存配置启动自动预约监控")
    if not safe_login(client, state, interactive=False):
        return 1
    try:
        Bot(client, state).monitor()
    except NotLoggedIn:
        out("登录状态已失效，无法继续", "ERROR")
        return 1
    return 0


def main():
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass
    state = load_state()
    client = HydreamClient()

    if not can_interact():
        return headless(client, state)

    if not is_configured(state):
        # 首次使用：引导配置
        clear()
        banner()
        title("首次使用")
        print("   欢迎使用 %s。完成以下配置后即可自动预约：" % PROJECT)
        print("   · 使用账号密码登录")
        print("   · 选择要监控的浴室与触发条件")
        print()
        if not confirm("现在开始配置", default_yes=True):
            return 0
        if not safe_login(client, state):
            pause("配置未完成，按回车退出")
            return 1
        state["session"] = client.dump_session()
        save_state(state)
        set_targets(state, client)
        set_bath_plan(state, client)
        set_misc(state)
        out("配置完成")
        pause("按回车进入主菜单")

    # 配置完备 -> 快速启动；否则进入主菜单
    while True:
        if is_configured(state):
            action = fast_start(state, client)
            if action == "quit":
                return 0
            if action == "monitor":
                monitor_flow(state, client)
                continue
        screen_main(state, client)
        return 0


if __name__ == "__main__":
    try:
        code = main()
    except NoInput:
        code = headless(HydreamClient(), load_state())
    except KeyboardInterrupt:
        out("程序已终止", "WARN")
        code = 130
    except SystemExit:
        raise
    except Exception as e:
        out("程序异常终止：%s: %s" % (type(e).__name__, e), "ERROR")
        code = 1
    if can_interact():
        try:
            input("\n  按回车关闭窗口…")
        except Exception:
            pass
    sys.exit(code)
