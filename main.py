# Tested with: flet==0.25.2
# Requires Python 3.9+
# Опциональные зависимости: pip install pystray reportlab pillow
import json
import os
import re
import uuid
import threading
import calendar
import shutil
import time as _time
import atexit
import queue
import asyncio
import logging
import math
import io
import base64
import struct
import csv
from datetime import date, datetime, timedelta
from typing import List, Optional, Dict, Tuple
from dataclasses import dataclass, asdict, field
from logging.handlers import RotatingFileHandler

import flet as ft

try:
    import pystray
    from PIL import Image, ImageDraw
    PYSTRAY_AVAILABLE = True
except ImportError:
    PYSTRAY_AVAILABLE = False

try:
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.units import cm
    from reportlab.pdfgen import canvas
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False

# ==================== ЛОГИРОВАНИЕ ====================

LOG_FILE = "tasks.log"
logger = logging.getLogger("taskmanager")
if not logger.handlers:
    logger.setLevel(logging.INFO)
    try:
        _fh = RotatingFileHandler(LOG_FILE, maxBytes=1_000_000, backupCount=3, encoding="utf-8")
        _fh.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(name)s: %(message)s"))
        logger.addHandler(_fh)
    except Exception:
        pass
    _ch = logging.StreamHandler()
    _ch.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
    logger.addHandler(_ch)

# ==================== МОДЕЛИ ====================

DAYS = [("Mon", "Пн"), ("Tue", "Вт"), ("Wed", "Ср"), ("Thu", "Чт"),
        ("Fri", "Пт"), ("Sat", "Сб"), ("Sun", "Вс")]
DAY_RU = dict(DAYS)
WEEKDAY_NAMES = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]
MONTH_NAMES = ["Январь", "Февраль", "Март", "Апрель", "Май", "Июнь",
               "Июль", "Август", "Сентябрь", "Октябрь", "Ноябрь", "Декабрь"]

KNOWN_NOTIFICATION_TYPES = {"sound", "popup", "both", "none"}
KNOWN_RECURRENCE_TYPES = {"none", "daily", "weekly", "monthly"}
FOLDER_ICONS = [ft.Icons.FOLDER, ft.Icons.WORK, ft.Icons.HOME, ft.Icons.SCHOOL,
                ft.Icons.FAVORITE, ft.Icons.STAR, ft.Icons.BOOK, ft.Icons.SHOPPING_CART]
FOLDER_COLORS = [ft.Colors.BLUE, ft.Colors.GREEN, ft.Colors.ORANGE, ft.Colors.PURPLE,
                 ft.Colors.RED, ft.Colors.TEAL, ft.Colors.AMBER, ft.Colors.PINK]


@dataclass
class Subtask:
    id: str
    title: str
    completed: bool = False


@dataclass
class ShoppingItem:
    id: str
    title: str
    bought: bool = False
    quantity: float = 1.0
    price: float = 0.0


@dataclass
class Task:
    id: str
    title: str
    folder: str
    is_shopping_list: bool = False
    move_to_tomorrow: bool = False
    use_time_blocking: bool = False
    use_pomodoro: bool = False
    use_timer: bool = False
    use_alarm: bool = False
    completed: bool = False
    planned_date: str = ""
    notification_type: str = "both"
    time_block_start: str = ""
    time_block_duration: int = 0
    time_block_days: List[str] = field(default_factory=list)
    time_block_dates: List[str] = field(default_factory=list)
    shopping_items: List[ShoppingItem] = field(default_factory=list)
    comment: str = ""
    alarm_time: str = ""
    last_alarm_triggered: str = ""
    last_block_triggered: str = ""
    last_block_ended_triggered: str = ""
    subtasks: List[Subtask] = field(default_factory=list)
    auto_complete_on_subtasks: bool = False
    recurrence: str = "none"
    completed_cycles: int = 0
    series_id: str = ""
    next_iteration_created: bool = False
    completed_at: str = ""
    created_at: str = ""
    estimated_minutes: int = 0
    reminder_minutes: int = 0
    last_reminder_triggered: str = ""

    def __post_init__(self):
        if not self.planned_date:
            self.planned_date = date.today().isoformat()
        if not self.created_at:
            self.created_at = datetime.now().isoformat()
        if self.recurrence not in KNOWN_RECURRENCE_TYPES:
            self.recurrence = "none"


@dataclass
class FolderInfo:
    name: str
    color: str = ft.Colors.BLUE
    icon: str = ft.Icons.FOLDER


@dataclass
class AppSettings:
    pomodoro_work: int = 25
    pomodoro_break: int = 5
    pomodoro_long_break: int = 15
    pomodoro_cycles: int = 4
    long_break_enabled: bool = True
    auto_continue: bool = True
    regular_timer_minutes: int = 15
    theme_mode: str = "light"
    volume: float = 0.8
    dark_theme_schedule_enabled: bool = False
    dark_theme_schedule_start: str = "20:00"
    dark_theme_schedule_end: str = "07:00"
    minimize_to_tray: bool = False
    show_in_title: bool = True


# ==================== УТИЛИТЫ ДАТ ====================

def parse_date_input(text: str) -> Optional[str]:
    """ДДММГГГГ / ДД.ММ.ГГГГ / ДД-ММ-ГГГГ / ДД/ММ/ГГГГ → ISO."""
    if not text:
        return None
    text = text.strip()
    m = re.fullmatch(r'(\d{1,2})[.\-/\s](\d{1,2})[.\-/\s](\d{4})', text)
    if m:
        try:
            d, mo, y = int(m.group(1)), int(m.group(2)), int(m.group(3))
            return date(y, mo, d).isoformat()
        except ValueError:
            return None
    cleaned = re.sub(r'\D', '', text)
    if len(cleaned) != 8:
        return None
    try:
        d = int(cleaned[0:2])
        mo = int(cleaned[2:4])
        y = int(cleaned[4:8])
        return date(y, mo, d).isoformat()
    except ValueError:
        return None


def format_date_display_ru(iso_date: str) -> str:
    if not iso_date:
        return ""
    try:
        d = date.fromisoformat(iso_date)
        return d.strftime("%d.%m.%Y")
    except (ValueError, TypeError):
        return ""


def parse_dates_multi(text: str) -> tuple:
    parsed, invalid = [], []
    if not text:
        return parsed, invalid
    for part in re.split(r'[,;\n]', text):
        part = part.strip()
        if not part:
            continue
        iso = parse_date_input(part)
        if iso:
            parsed.append(iso)
        else:
            invalid.append(part)
    return parsed, invalid


def _normalize_stored_dates(dates: list) -> list:
    if not dates:
        return []
    result = []
    for d in dates:
        d = str(d).strip()
        if not d:
            continue
        if len(d) == 10 and d.count("-") == 2:
            try:
                date.fromisoformat(d)
                result.append(d)
                continue
            except ValueError:
                pass
        iso = parse_date_input(d)
        if iso:
            result.append(iso)
    return result


def _normalize_planned_date(raw: str) -> str:
    """FIX: сначала YYYYMMDD, потом DDMMYYYY, потом форматы с разделителями."""
    pd = (raw or "").strip()
    if not pd:
        return date.today().isoformat()
    if len(pd) == 10 and pd.count("-") == 2:
        try:
            date.fromisoformat(pd)
            return pd
        except ValueError:
            return date.today().isoformat()
    if len(pd) == 8 and pd.isdigit():
        # Сначала YYYYMMDD (год в первых 4 цифрах)
        try:
            y = int(pd[0:4])
            m = int(pd[4:6])
            d = int(pd[6:8])
            if 1900 <= y <= 2100:
                return date(y, m, d).isoformat()
        except ValueError:
            pass
        # Потом DDMMYYYY
        try:
            d = int(pd[0:2])
            m = int(pd[2:4])
            y = int(pd[4:8])
            return date(y, m, d).isoformat()
        except ValueError:
            pass
    iso = parse_date_input(pd)
    return iso if iso else date.today().isoformat()


def weekday_code(d: date) -> str:
    return ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"][d.weekday()]


def safe_iso(d: str) -> Optional[date]:
    try:
        return date.fromisoformat(d)
    except (ValueError, TypeError):
        return None


def get_week_range(d: date) -> Tuple[date, date]:
    monday = d - timedelta(days=d.weekday())
    sunday = monday + timedelta(days=6)
    return monday, sunday


def get_month_range(d: date) -> Tuple[date, date]:
    first = d.replace(day=1)
    if d.month == 12:
        last = d.replace(year=d.year + 1, month=1, day=1) - timedelta(days=1)
    else:
        last = d.replace(month=d.month + 1, day=1) - timedelta(days=1)
    return first, last


# ==================== ЛОГИКА TIME-BLOCK ====================

def _get_task_active_dates(task: Task, horizon_days: int = 366) -> set:
    """FIX: единая функция определения дат действия блока."""
    dates = set()
    if task.time_block_dates:
        dates.update(task.time_block_dates)
    if task.time_block_days:
        pd = safe_iso(task.planned_date) or date.today()
        for i in range(horizon_days):
            d = pd + timedelta(days=i)
            if weekday_code(d) in task.time_block_days:
                dates.add(d.isoformat())
    if not dates:
        pd = safe_iso(task.planned_date)
        if pd:
            dates.add(pd.isoformat())
    return dates


def block_status(task: Task, now: datetime) -> Optional[dict]:
    """FIX: использует _get_task_active_dates для единообразия."""
    if not task.use_time_blocking or task.completed:
        return None
    if not task.time_block_start or task.time_block_duration <= 0:
        return None
    today = now.date()
    today_iso = today.isoformat()
    active_dates = _get_task_active_dates(task, horizon_days=1)
    if today_iso not in active_dates:
        return None
    if not valid_hhmm(task.time_block_start):
        return None
    try:
        h, m = map(int, task.time_block_start.split(":"))
    except ValueError:
        return None
    start_dt = datetime.combine(today, datetime.min.time()).replace(hour=h, minute=m)
    end_dt = start_dt + timedelta(minutes=task.time_block_duration)
    if now < start_dt:
        return {"state": "upcoming",
                "seconds_until": int((start_dt - now).total_seconds()),
                "start_dt": start_dt, "end_dt": end_dt}
    if now >= end_dt:
        return {"state": "past", "start_dt": start_dt, "end_dt": end_dt}
    return {"state": "active",
            "seconds_left": int((end_dt - now).total_seconds()),
            "start_dt": start_dt, "end_dt": end_dt}


def find_block_conflicts(task: Task, all_tasks: List[Task]) -> List[Task]:
    """FIX: учитывает planned_date для блоков без расписания."""
    if not task.use_time_blocking or not task.time_block_start:
        return []
    if task.time_block_duration <= 0 or not valid_hhmm(task.time_block_start):
        return []
    try:
        h, m = map(int, task.time_block_start.split(":"))
    except ValueError:
        return []
    t_start = h * 60 + m
    t_end = t_start + task.time_block_duration
    task_dates = _get_task_active_dates(task)
    if not task_dates:
        return []
    result = []
    for other in all_tasks:
        if other.id == task.id or other.completed:
            continue
        if not other.use_time_blocking or not other.time_block_start:
            continue
        if other.time_block_duration <= 0 or not valid_hhmm(other.time_block_start):
            continue
        other_dates = _get_task_active_dates(other)
        if not other_dates:
            continue
        if not (task_dates & other_dates):
            continue
        try:
            oh, om = map(int, other.time_block_start.split(":"))
        except ValueError:
            continue
        o_start = oh * 60 + om
        o_end = o_start + other.time_block_duration
        if t_start < o_end and o_start < t_end:
            result.append(other)
    return result


# ==================== УТИЛИТЫ ====================

def parse_positive_float(text: str, default: float = 0.0) -> float:
    try:
        text = (text or "").strip().replace(",", ".")
        if not text:
            return default
        v = float(text)
        if not math.isfinite(v) or v < 0:
            return default
        return v
    except (ValueError, OverflowError):
        return default


def parse_positive_int(text: str, default: int, max_val: int = 999999) -> int:
    """FIX: единая валидация с верхней границей."""
    raw = (text or "").strip()
    if not raw or not raw.isdigit():
        return default
    v = int(raw)
    if v <= 0 or v > max_val:
        return default
    return v


def generate_beep_wav_base64(frequency=880, duration_ms=250, sample_rate=22050):
    n_samples = int(sample_rate * duration_ms / 1000)
    max_amplitude = 32767
    wave_data = io.BytesIO()
    for i in range(n_samples):
        t = float(i) / sample_rate
        value = int(max_amplitude * math.sin(2.0 * math.pi * frequency * t))
        wave_data.write(struct.pack('<h', value))
    wave_bytes = wave_data.getvalue()
    wav_header = struct.pack(
        '<4sI4s4sIHHIIHH4sI',
        b'RIFF', 36 + len(wave_bytes), b'WAVE', b'fmt ',
        16, 1, 1, sample_rate, sample_rate * 2, 2, 16,
        b'data', len(wave_bytes)
    )
    return base64.b64encode(wav_header + wave_bytes).decode('ascii')


def fmt_time(seconds: int) -> str:
    m, s = divmod(max(0, int(seconds)), 60)
    if m >= 60:
        h, m = divmod(m, 60)
        return f"{h:d}:{m:02d}:{s:02d}"
    return f"{m:02d}:{s:02d}"


def fmt_money(value: float) -> str:
    return f"{value:,.2f}".replace(",", "\u00A0").replace(".", ",")


def valid_hhmm(text: str) -> bool:
    return bool(re.fullmatch(r"([01]\d|2[0-3]):[0-5]\d", (text or "").strip()))


def normalize_hhmm(text: str) -> str:
    text = (text or "").strip()
    if not text:
        return ""
    m = re.fullmatch(r"(\d{1,2}):(\d{1,2})", text)
    if m:
        h, mi = int(m.group(1)), int(m.group(2))
        if 0 <= h <= 23 and 0 <= mi <= 59:
            return f"{h:02d}:{mi:02d}"
        return text
    if text.isdigit():
        if len(text) == 4:
            h_str, m_str = text[:2], text[2:]
        elif len(text) == 3:
            h_str, m_str = text[:1], text[1:]
        elif len(text) <= 2:
            h_str, m_str = text, "00"
        else:
            return text
        h, mi = int(h_str), int(m_str)
        if 0 <= h <= 23 and 0 <= mi <= 59:
            return f"{h:02d}:{mi:02d}"
    return text


# ==================== ПЕРСИСТ ТАЙМЕРА ЗАДАЧИ ====================

TASK_TIMER_FILE = "task_timer.json"


def save_task_timer_state(state: dict):
    try:
        tmp = TASK_TIMER_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
        os.replace(tmp, TASK_TIMER_FILE)
    except Exception as ex:
        logger.error("save_task_timer_state: %s", ex)


def load_task_timer_state() -> Optional[dict]:
    if not os.path.exists(TASK_TIMER_FILE):
        return None
    try:
        with open(TASK_TIMER_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as ex:
        logger.error("load_task_timer_state: %s", ex)
        return None


def clear_task_timer_state():
    try:
        if os.path.exists(TASK_TIMER_FILE):
            os.remove(TASK_TIMER_FILE)
    except Exception as ex:
        logger.error("clear_task_timer_state: %s", ex)


# ==================== НЕЗАВИСИМЫЕ ТАЙМЕРЫ ====================

class StandaloneTimer:
    def __init__(self, timer_type: str, duration_seconds: int,
                 completion_queue, app_stop_event: threading.Event,
                 notification_type: str = "both"):
        self.id = str(uuid.uuid4())
        self.timer_type = timer_type
        self.time_left = duration_seconds
        self.total_time = duration_seconds
        self.is_running = False
        self.paused = False
        self._thread: Optional[threading.Thread] = None
        self._stop_event = threading.Event()
        self._app_stop_event = app_stop_event
        self._completion_queue = completion_queue
        self._lock = threading.RLock()
        self.notification_type = notification_type
        self._end_time: Optional[float] = None

    def _tick(self):
        while not self._stop_event.wait(0.5):
            if self._app_stop_event.is_set():
                return
            with self._lock:
                if self._end_time is None:
                    return
                remaining = self._end_time - _time.monotonic()
                if remaining <= 0:
                    self.time_left = 0
                    self.is_running = False
                    self.paused = False
                    self._end_time = None
                    current = 0
                else:
                    self.time_left = int(math.ceil(remaining))
                    current = self.time_left
            if current <= 0:
                if self._stop_event.is_set() or self._app_stop_event.is_set():
                    return
                try:
                    self._completion_queue.put_nowait(self)
                except queue.Full:
                    logger.error("[STANDALONE] queue full, dropped: %s", self.id[:8])
                except Exception as ex:
                    logger.error("[STANDALONE] queue error: %s", ex)
                return

    def start(self):
        with self._lock:
            if self.is_running:
                return
            self._end_time = _time.monotonic() + self.time_left
            self._stop_event = threading.Event()
            self.is_running = True
            self.paused = False
            self._thread = threading.Thread(target=self._tick, daemon=True)
            self._thread.start()

    def pause(self):
        with self._lock:
            if not self.is_running:
                return
            if self._end_time is not None:
                self.time_left = max(0, int(math.ceil(self._end_time - _time.monotonic())))
            self._stop_event.set()
            self.is_running = False
            self.paused = True
            self._end_time = None

    def resume(self):
        with self._lock:
            if not self.paused:
                return
            self._end_time = _time.monotonic() + self.time_left
            self.paused = False
            self.is_running = True
            self._stop_event = threading.Event()
            self._thread = threading.Thread(target=self._tick, daemon=True)
            self._thread.start()

    def stop(self):
        with self._lock:
            self._stop_event.set()
            self.is_running = False
            self.paused = False
            self.time_left = 0
            self._end_time = None

    def join(self, timeout: float = 1.0):
        t = self._thread
        if t and t.is_alive():
            self._stop_event.set()
            if t is not threading.current_thread():
                t.join(timeout=timeout)


class TimerState:
    def __init__(self, page: ft.Page, on_tick, on_complete, app_stop_event: threading.Event):
        self.page = page
        self.on_tick = on_tick
        self.on_complete = on_complete
        self.is_running = False
        self.paused = False
        self.time_left = 0
        self.total_time = 0
        self.mode = "work"
        self.type = "pomodoro"
        self.task_id: Optional[str] = None
        self.cycles_completed = 0
        self._thread: Optional[threading.Thread] = None
        self._stop_event = threading.Event()
        self._lock = threading.RLock()
        self._app_stop_event = app_stop_event
        self._end_time: Optional[float] = None

    def _persist(self):
        if self.time_left <= 0 and not self.is_running and not self.paused:
            clear_task_timer_state()
            return
        save_task_timer_state({
            "time_left": int(self.time_left),
            "total_time": int(self.total_time),
            "mode": self.mode,
            "type": self.type,
            "task_id": self.task_id,
            "cycles_completed": self.cycles_completed,
            "paused": self.paused,
            "saved_at": datetime.now().isoformat(),
        })

    def _emit(self, handler, *args):
        if self._app_stop_event.is_set():
            return
        try:
            self.page.run_task(handler, *args)
        except Exception:
            pass

    def _cancel_thread(self):
        self._stop_event.set()
        self.is_running = False
        t = self._thread
        if t and t.is_alive() and t is not threading.current_thread():
            t.join(timeout=0.5)
        self._end_time = None

    def _spawn(self):
        self._stop_event = threading.Event()
        self._thread = threading.Thread(target=self._tick, daemon=True)
        self._thread.start()

    def start(self, seconds: int, mode: str, timer_type: str,
              task_id: Optional[str], keep_cycles: bool = False,
              cycles: Optional[int] = None):
        with self._lock:
            self._cancel_thread()
            if cycles is not None:
                self.cycles_completed = cycles
            elif not keep_cycles:
                self.cycles_completed = 0
            self.time_left = max(1, int(seconds))
            self.total_time = self.time_left
            self.mode = mode
            self.type = timer_type
            self.task_id = task_id
            self.is_running = True
            self.paused = False
            self._end_time = _time.monotonic() + self.time_left
            self._spawn()
            self._persist()
        self._emit(self.on_tick)

    def pause(self):
        with self._lock:
            if not self.is_running:
                return
            if self._end_time is not None:
                self.time_left = max(0, int(math.ceil(self._end_time - _time.monotonic())))
            self._cancel_thread()
            self.paused = True
            self._persist()
        self._emit(self.on_tick)

    def resume(self):
        with self._lock:
            if not (self.paused and self.time_left > 0):
                return
            self.paused = False
            self.is_running = True
            self._end_time = _time.monotonic() + self.time_left
            self._spawn()
            self._persist()
        self._emit(self.on_tick)

    def stop(self):
        with self._lock:
            self._cancel_thread()
            self.paused = False
            self.time_left = 0
            self.total_time = 0
            self.cycles_completed = 0
            self.task_id = None
            self.mode = "work"
            clear_task_timer_state()
        self._emit(self.on_tick)

    def _tick(self):
        last_displayed = -1
        while not self._stop_event.wait(0.5):
            if self._app_stop_event.is_set():
                return
            with self._lock:
                if self._end_time is None:
                    return
                remaining = self._end_time - _time.monotonic()
                if remaining <= 0:
                    self.time_left = 0
                    self.is_running = False
                    self._end_time = None
                    current = 0
                else:
                    self.time_left = int(math.ceil(remaining))
                    current = self.time_left
            if current <= 0:
                self._emit(self.on_complete)
                return
            if current != last_displayed:
                last_displayed = current
                self._emit(self.on_tick)


# ==================== ПРОВЕРКА БУДИЛЬНИКОВ ====================

class BackgroundChecker:
    def __init__(self, tm, page, on_alarm_triggered, on_block_started,
                 on_block_ended, on_reminder, stop_event: threading.Event):
        self.tm = tm
        self.page = page
        self.on_alarm_triggered = on_alarm_triggered
        self.on_block_started = on_block_started
        self.on_block_ended = on_block_ended
        self.on_reminder = on_reminder
        self._thread: Optional[threading.Thread] = None
        self._stop_event = stop_event

    def start(self):
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()

    def _loop(self):
        try:
            self.tm.carry_over()
        except Exception as ex:
            logger.error("carry_over on start: %s", ex)
        tick = 0
        while not self._stop_event.wait(3):
            try:
                self._check_alarms()
                tick += 1
                if tick >= 20:
                    self.tm.carry_over()
                    tick = 0
            except Exception as ex:
                logger.error("Background thread error: %s", ex)

    def _safe_run_task(self, handler, *args):
        if self._stop_event.is_set():
            return
        try:
            self.page.run_task(handler, *args)
        except Exception:
            pass

    def _check_alarms(self):
        if self._stop_event.is_set():
            return
        now = datetime.now()
        current_time = now.strftime("%H:%M")
        current_date_iso = now.date().isoformat()
        current_stamp = f"{current_date_iso} {current_time}"
        triggered_any = block_changed = ended_changed = reminder_triggered = False
        with self.tm._tasks_lock:
            for task in self.tm.tasks:
                if not task.use_alarm or not task.alarm_time or task.completed:
                    continue
                task_alarm_norm = normalize_hhmm(task.alarm_time)
                if (task.last_alarm_triggered != current_stamp
                        and task.planned_date == current_date_iso
                        and task_alarm_norm == current_time):
                    task.last_alarm_triggered = current_stamp
                    triggered_any = True
                    self._safe_run_task(self.on_alarm_triggered, task)
                # Напоминания
                if task.reminder_minutes > 0 and task.planned_date == current_date_iso:
                    reminder_stamp = f"{current_date_iso} {task_alarm_norm} {task.reminder_minutes}"
                    if task.last_reminder_triggered != reminder_stamp:
                        try:
                            h, m = map(int, task_alarm_norm.split(":"))
                            reminder_dt = datetime.combine(now.date(), datetime.min.time()).replace(
                                hour=h, minute=m) - timedelta(minutes=task.reminder_minutes)
                            if abs((now - reminder_dt).total_seconds()) < 90:
                                task.last_reminder_triggered = reminder_stamp
                                reminder_triggered = True
                                self._safe_run_task(self.on_reminder, task, task.reminder_minutes)
                        except ValueError:
                            pass
            for task in self.tm.tasks:
                status = block_status(task, now)
                if not status or status["state"] != "active":
                    continue
                if (now - status["start_dt"]).total_seconds() > 180:
                    continue
                stamp = f"{current_date_iso} {task.time_block_start}"
                if task.last_block_triggered == stamp:
                    continue
                task.last_block_triggered = stamp
                block_changed = True
                self._safe_run_task(self.on_block_started, task)
            for task in self.tm.tasks:
                status = block_status(task, now)
                if not status or status["state"] != "past":
                    continue
                if (now - status["end_dt"]).total_seconds() > 300:
                    continue
                stamp = f"{current_date_iso} {task.time_block_start}"
                if task.last_block_ended_triggered == stamp:
                    continue
                task.last_block_ended_triggered = stamp
                ended_changed = True
                self._safe_run_task(self.on_block_ended, task)
        if triggered_any or block_changed or ended_changed or reminder_triggered:
            self.tm.save_tasks()


# ==================== ХРАНИЛИЩЕ ====================

class TaskManager:
    def __init__(self, data_file: str = "tasks.json"):
        self.data_file = data_file
        self.settings_file = "settings.json"
        self.timers_file = "timers.json"
        self.templates_file = "templates.json"
        self.tasks: List[Task] = []
        self.folders: List[FolderInfo] = [
            FolderInfo("Дом", ft.Colors.BLUE, ft.Icons.HOME),
            FolderInfo("Работа", ft.Colors.GREEN, ft.Icons.WORK),
            FolderInfo("Личное", ft.Colors.ORANGE, ft.Icons.FAVORITE),
        ]
        self.settings = AppSettings()
        self.templates: List[dict] = []
        self._tasks_lock = threading.RLock()
        self._save_lock = threading.RLock()
        self.last_backup_error: Optional[str] = None
        self.last_save_error: Optional[str] = None
        self.last_save_ts: Optional[datetime] = None
        self.load()
        self._migrate_loaded_data()

    # ---- миграция ключей JSON (пробелы) ----

    @staticmethod
    def _strip_keys(obj):
        if isinstance(obj, dict):
            return {(k.strip() if isinstance(k, str) else k): TaskManager._strip_keys(v)
                    for k, v in obj.items()}
        if isinstance(obj, list):
            return [TaskManager._strip_keys(i) for i in obj]
        return obj

    @staticmethod
    def _strip_keys_and_values(obj):
        if isinstance(obj, dict):
            out = {}
            for k, v in obj.items():
                kk = k.strip() if isinstance(k, str) else k
                if isinstance(v, str):
                    out[kk] = v.strip()
                else:
                    out[kk] = TaskManager._strip_keys_and_values(v)
            return out
        if isinstance(obj, list):
            return [TaskManager._strip_keys_and_values(i) for i in obj]
        return obj

    def load(self):
        if os.path.exists(self.data_file):
            try:
                with open(self.data_file, "r", encoding="utf-8") as f:
                    raw = json.load(f)
                data = self._strip_keys(raw)
                known_task = set(Task.__dataclass_fields__.keys()) - {"shopping_items", "subtasks"}
                known_item = set(ShoppingItem.__dataclass_fields__.keys())
                known_sub = set(Subtask.__dataclass_fields__.keys())
                for i, t in enumerate(data.get("tasks", [])):
                    try:
                        t = self._strip_keys(t)
                        raw_items = t.get("shopping_items", []) or []
                        raw_subs = t.get("subtasks", []) or []
                        filtered = {k: v for k, v in t.items() if k in known_task}
                        for str_field in ["planned_date", "alarm_time", "time_block_start",
                                          "comment", "notification_type", "recurrence",
                                          "series_id", "completed_at", "created_at"]:
                            if str_field in filtered and isinstance(filtered[str_field], str):
                                filtered[str_field] = filtered[str_field].strip()
                        task = Task(**filtered)
                        task.shopping_items = [
                            ShoppingItem(**{k: v for k, v in self._strip_keys(it).items() if k in known_item})
                            for it in raw_items
                        ]
                        task.subtasks = [
                            Subtask(**{k: v for k, v in self._strip_keys(sb).items() if k in known_sub})
                            for sb in raw_subs
                        ]
                        self.tasks.append(task)
                    except Exception as ex:
                        logger.warning("Пропускаю битую задачу #%s: %s", i, ex)
                raw_folders = data.get("folders") or []
                self.folders = []
                for f in raw_folders:
                    if isinstance(f, str):
                        name = f.strip()
                        if name and name != "Все":
                            self.folders.append(FolderInfo(name))
                    elif isinstance(f, dict):
                        f = self._strip_keys(f)
                        name = f.get("name", "").strip()
                        if name and name != "Все":
                            self.folders.append(FolderInfo(
                                name,
                                f.get("color", ft.Colors.BLUE),
                                f.get("icon", ft.Icons.FOLDER)
                            ))
                if not self.folders:
                    self.folders = [
                        FolderInfo("Дом", ft.Colors.BLUE, ft.Icons.HOME),
                        FolderInfo("Работа", ft.Colors.GREEN, ft.Icons.WORK),
                        FolderInfo("Личное", ft.Colors.ORANGE, ft.Icons.FAVORITE),
                    ]
            except Exception as ex:
                logger.error("Ошибка чтения задач: %s", ex)

        if os.path.exists(self.settings_file):
            try:
                with open(self.settings_file, "r", encoding="utf-8") as f:
                    raw = json.load(f)
                data = self._strip_keys_and_values(raw)
                known = set(AppSettings.__dataclass_fields__.keys())
                self.settings = AppSettings(**{k: v for k, v in data.items() if k in known})
            except Exception as ex:
                logger.error("Ошибка чтения настроек: %s", ex)

        if os.path.exists(self.templates_file):
            try:
                with open(self.templates_file, "r", encoding="utf-8") as f:
                    self.templates = json.load(f) or []
            except Exception as ex:
                logger.error("Ошибка чтения шаблонов: %s", ex)

    def _migrate_loaded_data(self):
        valid_days = {c for c, _ in DAYS}
        extra_folders = set()
        changed = False
        with self._tasks_lock:
            for task in self.tasks:
                new_pd = _normalize_planned_date(task.planned_date)
                if new_pd != task.planned_date:
                    task.planned_date = new_pd
                    changed = True
                new_dates = _normalize_stored_dates(task.time_block_dates)
                if new_dates != task.time_block_dates:
                    task.time_block_dates = new_dates
                    changed = True
                new_days = [d for d in task.time_block_days if d in valid_days]
                if new_days != task.time_block_days:
                    task.time_block_days = new_days
                    changed = True
                if task.notification_type not in KNOWN_NOTIFICATION_TYPES:
                    task.notification_type = "both"
                    changed = True
                if task.recurrence not in KNOWN_RECURRENCE_TYPES:
                    task.recurrence = "none"
                    changed = True
                if task.alarm_time:
                    norm = normalize_hhmm(task.alarm_time)
                    if norm != task.alarm_time:
                        task.alarm_time = norm
                        changed = True
                if task.time_block_start:
                    norm = normalize_hhmm(task.time_block_start)
                    if norm != task.time_block_start:
                        task.time_block_start = norm
                        changed = True
                if not task.series_id and task.recurrence != "none":
                    task.series_id = str(uuid.uuid4())
                    changed = True
                if not task.created_at:
                    task.created_at = datetime.now().isoformat()
                    changed = True
                if task.folder and task.folder != "Все" and task.folder not in [f.name for f in self.folders]:
                    extra_folders.add(task.folder)
            for folder in sorted(extra_folders):
                if folder not in [f.name for f in self.folders]:
                    self.folders.append(FolderInfo(folder))
                    changed = True
            if changed:
                logger.info("Миграция данных: схема обновлена")
                self._save_tasks_locked()

    def _make_backups(self):
        today_str = date.today().isoformat()
        base, ext = os.path.splitext(self.data_file)
        today_path = f"{base}_{today_str}{ext}"
        try:
            if not os.path.exists(today_path):
                data_dir = os.path.dirname(self.data_file) or "."
                base_name = os.path.basename(base)
                pattern = re.compile(
                    rf"^{re.escape(base_name)}_(\d{{4}}-\d{{2}}-\d{{2}}){re.escape(ext)}$")
                for filename in os.listdir(data_dir):
                    if pattern.match(filename):
                        try:
                            os.remove(os.path.join(data_dir, filename))
                        except Exception:
                            pass
                tmp_path = today_path + ".tmp"
                shutil.copy2(self.data_file, tmp_path)
                os.replace(tmp_path, today_path)
            self.last_backup_error = None
        except Exception as ex:
            self.last_backup_error = f"Ошибка бэкапа: {ex}"
            logger.error(self.last_backup_error)

    def _save_tasks_locked(self):
        try:
            if os.path.exists(self.data_file):
                try:
                    shutil.copy2(self.data_file, self.data_file + ".bak")
                except Exception as ex:
                    logger.warning("Не удалось создать .bak: %s", ex)
            tmp_path = self.data_file + ".tmp"
            with self._tasks_lock:
                folders_data = [{"name": f.name, "color": f.color, "icon": f.icon} for f in self.folders]
                payload = {"tasks": [asdict(t) for t in self.tasks], "folders": folders_data}
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(payload, f, ensure_ascii=False, indent=2)
            os.replace(tmp_path, self.data_file)
            self._make_backups()
            self.last_save_error = None
            self.last_save_ts = datetime.now()
        except Exception as ex:
            self.last_save_error = f"Ошибка сохранения: {ex}"
            logger.exception("save_tasks failed")
            try:
                tmp_path = self.data_file + ".tmp"
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except Exception:
                pass

    def save_tasks(self):
        with self._tasks_lock:
            self._save_tasks_locked()

    def save_settings(self):
        with self._save_lock:
            tmp_path = self.settings_file + ".tmp"
            try:
                with open(tmp_path, "w", encoding="utf-8") as f:
                    json.dump(asdict(self.settings), f, ensure_ascii=False, indent=2)
                os.replace(tmp_path, self.settings_file)
            except Exception as ex:
                logger.exception("save_settings failed: %s", ex)
                try:
                    if os.path.exists(tmp_path):
                        os.remove(tmp_path)
                except Exception:
                    pass

    def save_templates(self):
        try:
            tmp_path = self.templates_file + ".tmp"
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(self.templates, f, ensure_ascii=False, indent=2)
            os.replace(tmp_path, self.templates_file)
        except Exception as ex:
            logger.error("save_templates: %s", ex)

    def save_standalone_timers(self, timers):
        try:
            data = []
            now_ts = datetime.now().isoformat()
            for t in timers:
                if t.time_left > 0:
                    data.append({
                        "id": t.id, "timer_type": t.timer_type,
                        "time_left": t.time_left, "total_time": t.total_time,
                        "paused": t.paused, "notification_type": t.notification_type,
                        "saved_at": now_ts,
                    })
            tmp_path = self.timers_file + ".tmp"
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            os.replace(tmp_path, self.timers_file)
        except Exception as ex:
            logger.error("save_standalone_timers: %s", ex)

    def load_standalone_timers(self) -> List[dict]:
        if not os.path.exists(self.timers_file):
            return []
        try:
            with open(self.timers_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            now = datetime.now()
            restored = []
            for item in data:
                try:
                    saved_at = datetime.fromisoformat(item["saved_at"])
                    elapsed = int((now - saved_at).total_seconds())
                    remaining = item["time_left"] - (elapsed if not item["paused"] else 0)
                    if remaining > 0:
                        restored.append({
                            "timer_type": item["timer_type"],
                            "time_left": remaining,
                            "total_time": item["total_time"],
                            "notification_type": item.get("notification_type", "both"),
                            "was_paused": item["paused"],
                        })
                except Exception as ex:
                    logger.warning("Пропускаю битый таймер: %s", ex)
            return restored
        except Exception as ex:
            logger.error("load_standalone_timers: %s", ex)
            return []

    def add(self, task: Task):
        with self._tasks_lock:
            self.tasks.append(task)
            self._save_tasks_locked()

    def update(self, task: Task):
        with self._tasks_lock:
            self.tasks = [task if t.id == task.id else t for t in self.tasks]
            self._save_tasks_locked()

    def delete(self, task_id: str):
        with self._tasks_lock:
            self.tasks = [t for t in self.tasks if t.id != task_id]
            self._save_tasks_locked()

    def by_id(self, task_id: Optional[str]) -> Optional[Task]:
        with self._tasks_lock:
            return next((t for t in self.tasks if t.id == task_id), None)

    def add_folder(self, name: str, color: str = ft.Colors.BLUE, icon: str = ft.Icons.FOLDER) -> bool:
        with self._tasks_lock:
            if name and name not in [f.name for f in self.folders] and name != "Все":
                self.folders.append(FolderInfo(name, color, icon))
                self._save_tasks_locked()
                return True
            return False

    def update_folder(self, old_name: str, new_name: str, color: str, icon: str) -> bool:
        with self._tasks_lock:
            for f in self.folders:
                if f.name == old_name:
                    f.name = new_name
                    f.color = color
                    f.icon = icon
                    break
            for t in self.tasks:
                if t.folder == old_name:
                    t.folder = new_name
            self._save_tasks_locked()
            return True

    def delete_folder(self, name: str):
        with self._tasks_lock:
            self.folders = [f for f in self.folders if f.name != name]
            self.tasks = [t for t in self.tasks if t.folder != name]
            self._save_tasks_locked()

    def get_folder_info(self, name: str) -> Optional[FolderInfo]:
        with self._tasks_lock:
            return next((f for f in self.folders if f.name == name), None)

    def carry_over(self):
        today_iso = date.today().isoformat()
        changed = False
        with self._tasks_lock:
            for t in self.tasks:
                pd = safe_iso(t.planned_date)
                if t.move_to_tomorrow and not t.completed and (pd is None or pd < date.today()):
                    t.planned_date = today_iso
                    if t.use_alarm and t.alarm_time:
                        t.last_alarm_triggered = ""
                    changed = True
            if changed:
                self._save_tasks_locked()

    def tasks_for_date(self, d: date) -> List[Task]:
        """FIX: включает задачи с повторяющимися блоками."""
        iso = d.isoformat()
        wd = weekday_code(d)
        with self._tasks_lock:
            result = []
            for t in self.tasks:
                if t.planned_date == iso:
                    result.append(t)
                    continue
                if t.use_time_blocking:
                    active_dates = _get_task_active_dates(t, horizon_days=1)
                    if iso in active_dates:
                        result.append(t)
                        continue
                    if t.time_block_days and wd in t.time_block_days:
                        pd = safe_iso(t.planned_date)
                        if pd is None or pd <= d:
                            result.append(t)
                            continue
            return result

    def check_missed_alarms_on_startup(self) -> List[Task]:
        now = datetime.now()
        today = now.date()
        today_iso = today.isoformat()
        missed: List[Task] = []
        changed = False
        with self._tasks_lock:
            for task in self.tasks:
                if not task.use_alarm or not task.alarm_time or task.completed:
                    continue
                if task.planned_date != today_iso:
                    continue
                alarm_norm = normalize_hhmm(task.alarm_time)
                if not valid_hhmm(alarm_norm):
                    continue
                try:
                    h, m = map(int, alarm_norm.split(":"))
                except ValueError:
                    continue
                alarm_dt = datetime.combine(today, datetime.min.time()).replace(hour=h, minute=m)
                if alarm_dt >= now:
                    continue
                stamp = f"{today_iso} {alarm_norm}"
                if task.last_alarm_triggered == stamp:
                    continue
                task.last_alarm_triggered = stamp
                missed.append(task)
                changed = True
            if changed:
                self._save_tasks_locked()
        return missed

    def create_next_recurrence(self, task: Task) -> Optional[Task]:
        """FIX: проверяет next_iteration_created для предотвращения дублирования."""
        if task.recurrence == "none" or task.next_iteration_created:
            return None
        current_date = safe_iso(task.planned_date) or date.today()
        if task.recurrence == "daily":
            next_date = current_date + timedelta(days=1)
        elif task.recurrence == "weekly":
            next_date = current_date + timedelta(weeks=1)
        elif task.recurrence == "monthly":
            month = current_date.month + 1
            year = current_date.year
            if month > 12:
                month = 1
                year += 1
            last_day = calendar.monthrange(year, month)[1]
            next_date = date(year, month, min(current_date.day, last_day))
        else:
            return None

        series_id = task.series_id or str(uuid.uuid4())
        new_task = Task(
            id=str(uuid.uuid4()),
            title=task.title,
            folder=task.folder,
            is_shopping_list=task.is_shopping_list,
            move_to_tomorrow=task.move_to_tomorrow,
            use_time_blocking=task.use_time_blocking,
            use_pomodoro=task.use_pomodoro,
            use_timer=task.use_timer,
            use_alarm=task.use_alarm,
            completed=False,
            planned_date=next_date.isoformat(),
            notification_type=task.notification_type,
            time_block_start=task.time_block_start,
            time_block_duration=task.time_block_duration,
            time_block_days=list(task.time_block_days),
            time_block_dates=list(task.time_block_dates),
            shopping_items=[
                ShoppingItem(id=str(uuid.uuid4()), title=it.title, bought=False,
                             quantity=it.quantity, price=it.price)
                for it in task.shopping_items
            ],
            comment=task.comment,
            alarm_time=task.alarm_time,
            subtasks=[Subtask(id=str(uuid.uuid4()), title=s.title, completed=False)
                      for s in task.subtasks],
            auto_complete_on_subtasks=task.auto_complete_on_subtasks,
            recurrence=task.recurrence,
            completed_cycles=0,
            series_id=series_id,
            next_iteration_created=False,
            created_at=datetime.now().isoformat(),
            estimated_minutes=task.estimated_minutes,
            reminder_minutes=task.reminder_minutes,
        )
        task.next_iteration_created = True
        return new_task

    def calculate_streak(self) -> int:
        with self._tasks_lock:
            completed_dates = set()
            for t in self.tasks:
                if t.completed and t.completed_at:
                    try:
                        d = datetime.fromisoformat(t.completed_at).date()
                        completed_dates.add(d)
                    except (ValueError, TypeError):
                        pass
            if not completed_dates:
                return 0
            today = date.today()
            streak = 0
            check_date = today
            while check_date in completed_dates:
                streak += 1
                check_date -= timedelta(days=1)
            return streak

    def get_statistics(self) -> dict:
        """FIX: использует completed_at для честной аналитики."""
        today = date.today()
        week_start, week_end = get_week_range(today)
        month_start, month_end = get_month_range(today)
        week_completed = 0
        month_completed = 0
        weekday_stats = {i: 0 for i in range(7)}
        hourly_stats = {h: 0 for h in range(24)}
        hourly_planned = {h: 0 for h in range(24)}
        hourly_active = {h: 0 for h in range(24)}
        completion_times = []
        total_expenses = 0.0
        block_durations = []
        estimated_vs_actual = []

        with self._tasks_lock:
            for t in self.tasks:
                if t.is_shopping_list:
                    total_expenses += sum(it.quantity * it.price for it in t.shopping_items if it.bought)
                if t.completed and t.completed_at:
                    try:
                        completed_dt = datetime.fromisoformat(t.completed_at)
                        completed_date = completed_dt.date()
                        if week_start <= completed_date <= week_end:
                            week_completed += 1
                        if month_start <= completed_date <= month_end:
                            month_completed += 1
                        weekday_stats[completed_date.weekday()] += 1
                        hourly_stats[completed_dt.hour] += 1
                        if t.created_at:
                            created_dt = datetime.fromisoformat(t.created_at)
                            duration_minutes = (completed_dt - created_dt).total_seconds() / 60
                            if duration_minutes > 0:
                                completion_times.append(duration_minutes)
                        if t.estimated_minutes > 0 and t.completed_cycles > 0:
                            actual_minutes = t.completed_cycles * 25
                            estimated_vs_actual.append((t.estimated_minutes, actual_minutes))
                    except (ValueError, TypeError):
                        pass
                if t.planned_date:
                    try:
                        planned_dt = datetime.fromisoformat(t.planned_date + "T00:00:00")
                        hourly_planned[planned_dt.hour] += 1
                    except (ValueError, TypeError):
                        pass
                if t.use_time_blocking and t.time_block_start:
                    try:
                        h, m = map(int, t.time_block_start.split(":"))
                        hourly_active[h] += 1
                    except ValueError:
                        pass
                if t.use_time_blocking and t.time_block_duration > 0:
                    block_durations.append(t.time_block_duration)

        avg_completion = sum(completion_times) / len(completion_times) if completion_times else 0
        avg_block = sum(block_durations) / len(block_durations) if block_durations else 0
        peak_completion_hour = max(hourly_stats, key=hourly_stats.get) if hourly_stats else 0
        peak_planned_hour = max(hourly_planned, key=hourly_planned.get) if hourly_planned else 0
        peak_active_hour = max(hourly_active, key=hourly_active.get) if hourly_active else 0

        return {
            "week_completed": week_completed,
            "month_completed": month_completed,
            "weekday_stats": weekday_stats,
            "hourly_stats": hourly_stats,
            "hourly_planned": hourly_planned,
            "hourly_active": hourly_active,
            "total_expenses": total_expenses,
            "avg_block_time": avg_block,
            "avg_completion_time": avg_completion,
            "total_tasks": len(self.tasks),
            "completed_tasks": sum(1 for t in self.tasks if t.completed),
            "streak": self.calculate_streak(),
            "peak_completion_hour": peak_completion_hour,
            "peak_planned_hour": peak_planned_hour,
            "peak_active_hour": peak_active_hour,
            "estimated_vs_actual": estimated_vs_actual,
        }

    def export_tasks_csv(self, filepath: str):
        with open(filepath, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f, delimiter=";")
            w.writerow(["ID", "Название", "Папка", "Дата плана", "Дата выполнения",
                        "Выполнено", "Повторение", "Циклы", "Подзадачи всего",
                        "Подзадачи выполнено", "Оценка (мин)", "Комментарий"])
            for t in self.tasks:
                w.writerow([
                    t.id, t.title, t.folder,
                    format_date_display_ru(t.planned_date),
                    format_date_display_ru(t.completed_at) if t.completed_at else "",
                    "Да" if t.completed else "Нет",
                    t.recurrence, t.completed_cycles,
                    len(t.subtasks), sum(1 for s in t.subtasks if s.completed),
                    t.estimated_minutes, t.comment,
                ])

    def export_stats_csv(self, filepath: str, stats: dict):
        with open(filepath, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f, delimiter=";")
            w.writerow(["Показатель", "Значение"])
            w.writerow(["Всего задач", stats["total_tasks"]])
            w.writerow(["Выполнено всего", stats["completed_tasks"]])
            w.writerow(["Выполнено за неделю", stats["week_completed"]])
            w.writerow(["Выполнено за месяц", stats["month_completed"]])
            w.writerow(["Streak (дней подряд)", stats["streak"]])
            w.writerow(["Среднее время выполнения, мин", f"{stats['avg_completion_time']:.1f}"])
            w.writerow(["Среднее время блока, мин", f"{stats['avg_block_time']:.1f}"])
            w.writerow(["Расходы, ₽", f"{stats['total_expenses']:.2f}"])
            w.writerow(["Пик активности (завершение)", f"{stats['peak_completion_hour']}:00"])
            w.writerow(["Пик планирования", f"{stats['peak_planned_hour']}:00"])
            w.writerow(["Пик работы (блоки)", f"{stats['peak_active_hour']}:00"])
            w.writerow([])
            w.writerow(["Час", "Завершено", "Запланировано", "Активные блоки"])
            for h in range(24):
                w.writerow([f"{h:02d}:00",
                            stats["hourly_stats"].get(h, 0),
                            stats["hourly_planned"].get(h, 0),
                            stats["hourly_active"].get(h, 0)])
            w.writerow([])
            w.writerow(["День недели", "Выполнено"])
            for i, name in enumerate(WEEKDAY_NAMES):
                w.writerow([name, stats["weekday_stats"].get(i, 0)])

    def export_day_pdf(self, filepath: str, target_date: date):
        if not REPORTLAB_AVAILABLE:
            raise ImportError("reportlab не установлен")
        tasks = self.tasks_for_date(target_date)
        tasks.sort(key=lambda t: (t.time_block_start or "99:99", t.title.lower()))
        c = canvas.Canvas(filepath, pagesize=A4)
        width, height = A4
        c.setFont("Helvetica-Bold", 16)
        c.drawString(2*cm, height - 2*cm, f"Задачи на {target_date.strftime('%d.%m.%Y')}")
        y = height - 3*cm
        c.setFont("Helvetica", 10)
        for t in tasks:
            if y < 2*cm:
                c.showPage()
                y = height - 2*cm
            status = "✓" if t.completed else "○"
            time_str = t.time_block_start if t.time_block_start else ""
            c.drawString(2*cm, y, f"{status} {time_str} {t.title}")
            y -= 0.6*cm
        c.save()


# ==================== ПРИЛОЖЕНИЕ ====================

def main(page: ft.Page):
    page.title = "Менеджер задач + Pomodoro"
    page.padding = 10
    page.window.width = 1450
    page.window.height = 900

    try:
        page.window.prevent_close = True
        logger.info("page.window.prevent_close = True")
    except Exception as ex:
        logger.warning("prevent_close not set: %s", ex)

    def pal(light, dark):
        return dark if page.theme_mode == ft.ThemeMode.DARK else light

    # Подавление шума asyncio
    class _SuppressAsyncioShutdown(logging.Filter):
        def filter(self, record):
            try:
                msg = record.getMessage()
            except Exception:
                return True
            if "cannot schedule new futures after shutdown" in msg:
                return False
            if "Event loop is closed" in msg:
                return False
            return True

    for _name in ("asyncio", "asyncio.base_events", "asyncio.events",
                  "asyncio.futures", "asyncio.tasks", "asyncio.proactor_events",
                  "asyncio.selector_events"):
        try:
            logging.getLogger(_name).addFilter(_SuppressAsyncioShutdown())
        except Exception:
            pass

    def _quiet_exception_handler(loop, context):
        exc = context.get("exception")
        if isinstance(exc, RuntimeError):
            msg = str(exc)
            if ("cannot schedule new futures after shutdown" in msg
                    or "Event loop is closed" in msg):
                return
        try:
            loop.default_exception_handler(context)
        except Exception:
            pass

    async def _deferred_install_handler():
        try:
            asyncio.get_running_loop().set_exception_handler(_quiet_exception_handler)
            logger.info("asyncio exception handler installed (deferred)")
        except Exception as ex:
            logger.error("deferred install failed: %s", ex)

    try:
        page.run_task(_deferred_install_handler)
    except Exception as ex:
        logger.error("Could not schedule deferred handler: %s", ex)

    # Звук
    audio_player = None
    try:
        BEEP_BASE64 = generate_beep_wav_base64()
        audio_player = ft.Audio(src=f"data:audio/wav;base64,{BEEP_BASE64}", volume=0.8)
        page.overlay.append(audio_player)
        page.update()
    except Exception as ex:
        logger.error("Не удалось сгенерировать WAV: %s", ex)

    def play_notification_sound(volume: float = 0.8):
        try:
            import winsound
            winsound.Beep(1200, 300)
            winsound.Beep(1600, 300)
            return
        except ImportError:
            pass
        except Exception as ex:
            logger.warning("winsound error: %s", ex)
        if audio_player is not None:
            try:
                audio_player.volume = max(0.0, min(1.0, volume))
                audio_player.pause()
                audio_player.seek(0)
                audio_player.play()
                return
            except Exception as ex:
                logger.warning("Audio play error: %s", ex)
        print("\a", end="")

    tm = TaskManager()

    if audio_player is not None:
        try:
            audio_player.volume = max(0.0, min(1.0, tm.settings.volume))
        except Exception:
            pass

    page.theme_mode = (ft.ThemeMode.DARK if tm.settings.theme_mode == "dark"
                       else ft.ThemeMode.LIGHT)

    tm.carry_over()

    current_folder = "Все"
    current_view = "all"
    app_stop_event = threading.Event()
    timer_completion_queue = queue.Queue(maxsize=1000)
    standalone_timers_lock = threading.RLock()
    standalone_timers: List[StandaloneTimer] = []
    standalone_timers_view = ft.Column(spacing=4, scroll=ft.ScrollMode.AUTO, height=240)
    timer_ui_refs: Dict[str, Dict] = {}
    dialog_state = {"current_dialog": None, "save_handler": None}

    MODE_RU = {
        "work": "🍅 Работа",
        "short_break": "☕ Короткий перерыв",
        "long_break": "🌴 Длинный перерыв",
    }
    RECURRENCE_RU = {
        "none": "Не повторять",
        "daily": "Ежедневно",
        "weekly": "Еженедельно",
        "monthly": "Ежемесячно",
    }

    def toast(text: str, error: bool = False):
        if app_stop_event.is_set():
            return
        try:
            page.open(ft.SnackBar(
                content=ft.Text(text),
                bgcolor=ft.Colors.RED_400 if error else ft.Colors.GREEN_600))
            page.update()
        except Exception:
            pass

    def register_dialog(dlg, save_handler=None):
        dialog_state["current_dialog"] = dlg
        dialog_state["save_handler"] = save_handler

    def unregister_dialog():
        dialog_state["current_dialog"] = None
        dialog_state["save_handler"] = None

    # Расписание тёмной темы
    def desired_theme_mode() -> str:
        s = tm.settings
        if not s.dark_theme_schedule_enabled:
            return s.theme_mode
        if not (valid_hhmm(s.dark_theme_schedule_start) and valid_hhmm(s.dark_theme_schedule_end)):
            return s.theme_mode
        now = datetime.now().strftime("%H:%M")
        start, end = s.dark_theme_schedule_start, s.dark_theme_schedule_end
        if start <= end:
            dark = start <= now < end
        else:
            dark = now >= start or now < end
        return "dark" if dark else "light"

    def apply_theme_if_needed():
        want = desired_theme_mode()
        want_mode = ft.ThemeMode.DARK if want == "dark" else ft.ThemeMode.LIGHT
        if page.theme_mode == want_mode:
            return
        page.theme_mode = want_mode
        try:
            render_folders()
            render_tasks()
            render_standalone_timers()
            render_timer_banner()
            page.update()
            logger.info("Тема переключена по расписанию: %s", want)
        except Exception:
            pass

    # Мини-виджет в заголовке
    def update_window_title():
        if not tm.settings.show_in_title:
            page.title = "Менеджер задач + Pomodoro"
            return
        active = []
        for t in standalone_timers:
            if t.is_running or t.paused:
                active.append(t)
        if timer_state.is_running or timer_state.paused:
            class _Tmp:
                pass
            tmp = _Tmp()
            tmp.timer_type = timer_state.type
            tmp.time_left = timer_state.time_left
            tmp.is_running = timer_state.is_running
            tmp.paused = timer_state.paused
            active.insert(0, tmp)
        if not active:
            page.title = "Менеджер задач + Pomodoro"
            return
        parts = []
        for t in active[:3]:
            mins, secs = divmod(max(0, t.time_left), 60)
            icon = "🍅" if t.timer_type == "pomodoro" else "⏳"
            parts.append(f"{icon} {mins:02d}:{secs:02d}")
        title = " | ".join(parts)
        if len(active) > 3:
            title += f" +{len(active) - 3}"
        page.title = f"🏃 Работа: {title}"

    # Очистка
    cleanup_done = {"flag": False}

    def cleanup():
        if cleanup_done["flag"]:
            return
        cleanup_done["flag"] = True
        logger.info("Cleanup started")
        app_stop_event.set()
        try:
            with standalone_timers_lock:
                timers_snapshot = list(standalone_timers)
            tm.save_standalone_timers(timers_snapshot)
            logger.info("Saved %s timers", len(timers_snapshot))
        except Exception as ex:
            logger.exception("cleanup: save timers failed: %s", ex)
        logger.info("Cleanup done")

    atexit.register(cleanup)

    _installed_handlers: List[str] = []

    def _handle_close(reason: str):
        logger.info("[CLOSE] triggered by %s", reason)
        try:
            cleanup()
        finally:
            try:
                page.window.destroy()
                logger.info("[CLOSE] window.destroy() called")
            except Exception as ex:
                logger.warning("[CLOSE] destroy failed: %s, trying close()", ex)
                try:
                    page.window.close()
                except Exception as ex2:
                    logger.warning("[CLOSE] close() also failed: %s", ex2)
            def _watchdog():
                _time.sleep(0.5)
                logger.info("[CLOSE] watchdog: force exit (os._exit)")
                os._exit(0)
            threading.Thread(target=_watchdog, daemon=True).start()

    def _make_window_event_handler():
        def on_window_event(e):
            evt_type = getattr(e, "type", None)
            evt_data = getattr(e, "data", None)
            logger.info("[WINDOW] event received: type=%r data=%r", evt_type, evt_data)
            is_close = False
            try:
                if evt_type == ft.WindowEventType.CLOSE:
                    is_close = True
            except Exception:
                pass
            if not is_close and (evt_data == "close"
                                 or str(evt_type).lower().endswith(".close")
                                 or str(evt_type).lower() == "close"):
                is_close = True
            if is_close:
                if tm.settings.minimize_to_tray and PYSTRAY_AVAILABLE:
                    try:
                        page.window.minimize()
                    except Exception:
                        pass
                else:
                    _handle_close("window.on_event")
        return on_window_event

    try:
        page.window.on_event = _make_window_event_handler()
        _installed_handlers.append("window.on_event")
    except Exception as ex:
        logger.warning("page.window.on_event not installed: %s", ex)

    try:
        def _on_window_close(e):
            _handle_close("window.on_close")
        page.window.on_close = _on_window_close
        _installed_handlers.append("window.on_close")
    except Exception as ex:
        logger.warning("page.window.on_close not installed: %s", ex)

    try:
        def on_disconnect(e):
            _handle_close("on_disconnect")
        page.on_disconnect = on_disconnect
        _installed_handlers.append("on_disconnect")
    except Exception as ex:
        logger.warning("page.on_disconnect not installed: %s", ex)

    logger.info("Window close handlers: %s", ", ".join(_installed_handlers) or "atexit only")

    # Колбэки таймера задачи
    async def on_timer_tick():
        if app_stop_event.is_set():
            return
        try:
            render_timer_banner()
            update_window_title()
            page.update()
        except Exception:
            pass

    async def on_timer_complete():
        if app_stop_event.is_set():
            return
        task = tm.by_id(timer_state.task_id)
        title = task.title if task else "Задача"
        finished_mode = timer_state.mode
        notif = task.notification_type if task else "both"
        if notif in ("sound", "both"):
            threading.Thread(target=play_notification_sound,
                             args=(tm.settings.volume,), daemon=True).start()
        if notif in ("popup", "both"):
            try:
                page.open(ft.SnackBar(
                    content=ft.Text(f"⏰ {MODE_RU.get(finished_mode, finished_mode)} — завершено: {title}"),
                    bgcolor=ft.Colors.GREEN_600))
            except Exception:
                pass
        s = tm.settings
        if timer_state.type == "pomodoro" and s.auto_continue:
            tid = timer_state.task_id
            if finished_mode == "work":
                cycles = timer_state.cycles_completed + 1
                if s.long_break_enabled and s.pomodoro_cycles > 0 and cycles % s.pomodoro_cycles == 0:
                    mode, secs = "long_break", s.pomodoro_long_break * 60
                else:
                    mode, secs = "short_break", s.pomodoro_break * 60
                timer_state.start(secs, mode, "pomodoro", tid, cycles=cycles)
            else:
                timer_state.start(s.pomodoro_work * 60, "work", "pomodoro", tid, keep_cycles=True)
        else:
            timer_state.stop()
        try:
            render_timer_banner()
            render_tasks()
            update_window_title()
            page.update()
        except Exception:
            pass

    timer_state = TimerState(page, on_timer_tick, on_timer_complete, app_stop_event)

    _saved_tt = load_task_timer_state()
    if _saved_tt and _saved_tt.get("time_left", 0) > 0:
        _saved_task = tm.by_id(_saved_tt.get("task_id"))
        if _saved_task is not None:
            try:
                saved_at = datetime.fromisoformat(_saved_tt.get("saved_at", datetime.now().isoformat()))
            except Exception:
                saved_at = datetime.now()
            elapsed = int((datetime.now() - saved_at).total_seconds())
            remaining = _saved_tt["time_left"]
            if not _saved_tt.get("paused", False):
                remaining -= elapsed
            if remaining > 0:
                timer_state.start(remaining, _saved_tt.get("mode", "work"),
                                  _saved_tt.get("type", "pomodoro"),
                                  _saved_tt.get("task_id"),
                                  cycles=_saved_tt.get("cycles_completed", 0))
                if _saved_tt.get("paused", False):
                    timer_state.pause()
            else:
                toast(f"⏰ Таймер задачи истёк: {_saved_task.title}", error=True)
                clear_task_timer_state()
        else:
            clear_task_timer_state()

    # Колбэки standalone
    async def on_standalone_timer_complete(timer: StandaloneTimer):
        if app_stop_event.is_set():
            return
        try:
            notif = timer.notification_type
            if notif in ("sound", "both"):
                threading.Thread(target=play_notification_sound,
                                 args=(tm.settings.volume,), daemon=True).start()
            if notif in ("popup", "both"):
                kind = "Pomodoro" if timer.timer_type == "pomodoro" else "Таймер"
                page.open(ft.SnackBar(content=ft.Text(f"⏱ {kind} завершён!"),
                                      bgcolor=ft.Colors.GREEN_600))
            with standalone_timers_lock:
                timer_ui_refs.pop(timer.id, None)
                if timer in standalone_timers:
                    standalone_timers.remove(timer)
            render_standalone_timers()
            update_window_title()
        except Exception as e:
            logger.exception("[STANDALONE COMPLETE ERROR] %s", e)

    def _build_play_pause_button(t: StandaloneTimer) -> ft.IconButton:
        if t.is_running and not t.paused:
            return ft.IconButton(ft.Icons.PAUSE, tooltip="Пауза",
                                  on_click=lambda e, timer=t: (timer.pause(), render_standalone_timers()))
        elif t.paused:
            return ft.IconButton(ft.Icons.PLAY_ARROW, tooltip="Продолжить",
                                  on_click=lambda e, timer=t: (timer.resume(), render_standalone_timers()))
        return ft.IconButton(ft.Icons.PLAY_ARROW, tooltip="Старт",
                              on_click=lambda e, timer=t: (timer.start(), render_standalone_timers()))

    def _current_btn_state(t: StandaloneTimer) -> str:
        return "pause" if (t.is_running and not t.paused) else ("resume" if t.paused else "start")

    def render_standalone_timers():
        with standalone_timers_lock:
            current_ids = {t.id for t in standalone_timers}
            timers_snapshot = list(standalone_timers)
        for tid in list(timer_ui_refs.keys()):
            if tid not in current_ids:
                del timer_ui_refs[tid]
        new_controls = []
        for t in timers_snapshot:
            mins, secs = divmod(max(0, t.time_left), 60)
            time_str = f"{mins:02d}:{secs:02d}"
            kind = "🍅 Pomodoro" if t.timer_type == "pomodoro" else "⏳ Таймер"
            state = " ▶" if t.is_running and not t.paused else (" ⏸" if t.paused else " ⏹")
            state_str = f"{kind}{state}"
            btn_state = _current_btn_state(t)
            refs = timer_ui_refs.get(t.id)
            if refs is None:
                time_text = ft.Text(time_str, size=20, weight=ft.FontWeight.BOLD,
                                    color=pal(ft.Colors.BLUE_800, ft.Colors.BLUE_100))
                state_text = ft.Text(state_str, size=12, weight=ft.FontWeight.BOLD,
                                     color=pal(ft.Colors.BLACK, ft.Colors.WHITE))
                play_pause_btn = _build_play_pause_button(t)
                delete_btn = ft.IconButton(ft.Icons.DELETE, icon_color=ft.Colors.RED_400,
                                            tooltip="Удалить",
                                            on_click=lambda e, timer=t: safe_remove_timer(timer))
                btn_row = ft.Row([play_pause_btn, delete_btn], spacing=2)
                container = ft.Container(
                    padding=ft.padding.symmetric(horizontal=10, vertical=4),
                    border_radius=8,
                    bgcolor=pal(ft.Colors.BLUE_50, ft.Colors.BLUE_GREY_900),
                    border=ft.border.all(1, pal(ft.Colors.BLUE_200, ft.Colors.BLUE_700)),
                    content=ft.Row([
                        ft.Column([state_text, time_text], spacing=0),
                        btn_row,
                    ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                       vertical_alignment=ft.CrossAxisAlignment.CENTER),
                )
                timer_ui_refs[t.id] = {
                    "container": container, "time_text": time_text,
                    "state_text": state_text, "btn_row": btn_row,
                    "delete_btn": delete_btn, "btn_state": btn_state,
                }
            else:
                refs["time_text"].value = time_str
                refs["state_text"].value = state_str
                refs["container"].bgcolor = pal(ft.Colors.BLUE_50, ft.Colors.BLUE_GREY_900)
                if refs.get("btn_state") != btn_state:
                    refs["btn_row"].controls = [_build_play_pause_button(t), refs["delete_btn"]]
                    refs["btn_state"] = btn_state
            new_controls.append(timer_ui_refs[t.id]["container"])
        standalone_timers_view.controls = new_controls
        if not app_stop_event.is_set():
            try:
                page.update()
            except Exception:
                pass

    def safe_remove_timer(timer: StandaloneTimer):
        try:
            timer.stop()
            timer.join(timeout=0.3)
        except Exception:
            pass
        with standalone_timers_lock:
            timer_ui_refs.pop(timer.id, None)
            if timer in standalone_timers:
                standalone_timers.remove(timer)
        render_standalone_timers()
        update_window_title()

    def start_standalone_timer(timer_type: str, notification_type: str = "both"):
        s = tm.settings
        duration = (s.pomodoro_work if timer_type == "pomodoro" else s.regular_timer_minutes) * 60
        duration = max(60, duration)
        new_timer = StandaloneTimer(timer_type, duration, timer_completion_queue,
                                    app_stop_event, notification_type=notification_type)
        with standalone_timers_lock:
            standalone_timers.append(new_timer)
        new_timer.start()
        render_standalone_timers()
        update_window_title()

    # Тикер UI
    _theme_tick = {"n": 0}
    _title_tick = {"n": 0}

    async def _ticker_tick():
        if app_stop_event.is_set():
            return
        try:
            processed = 0
            while not timer_completion_queue.empty() and processed < 50:
                try:
                    timer = timer_completion_queue.get_nowait()
                    await on_standalone_timer_complete(timer)
                    processed += 1
                except queue.Empty:
                    break
                except Exception as e:
                    logger.exception("[TICKER] process error: %s", e)
            if app_stop_event.is_set():
                return
            with standalone_timers_lock:
                has_active = any(t.is_running or t.paused for t in standalone_timers)
            if has_active:
                render_standalone_timers()
            _theme_tick["n"] += 1
            if _theme_tick["n"] >= 30:
                _theme_tick["n"] = 0
                apply_theme_if_needed()
            _title_tick["n"] += 1
            if _title_tick["n"] >= 2:
                _title_tick["n"] = 0
                update_window_title()
            if tm.last_save_ts:
                age = (datetime.now() - tm.last_save_ts).total_seconds()
                if age < 0.4:
                    new_val, new_color = "💾 Сохранение...", ft.Colors.BLUE_400
                elif age < 2.5:
                    new_val, new_color = "✓ Сохранено", ft.Colors.GREEN_600
                else:
                    new_val, new_color = "", ft.Colors.GREY_500
                if save_status.value != new_val:
                    save_status.value = new_val
                    save_status.color = new_color
                    try:
                        save_status.update()
                    except Exception:
                        pass
            elif save_status.value:
                save_status.value = ""
                try:
                    save_status.update()
                except Exception:
                    pass
            if tm.last_backup_error:
                toast(f"⚠ {tm.last_backup_error}", error=True)
                tm.last_backup_error = None
            if tm.last_save_error:
                toast(f"⚠ {tm.last_save_error}", error=True)
                tm.last_save_error = None
        except Exception as e:
            logger.exception("[TICKER_TICK] error: %s", e)

    def _standalone_timers_ticker():
        consecutive_errors = 0
        while not app_stop_event.wait(1):
            if app_stop_event.is_set():
                break
            try:
                page.run_task(_ticker_tick)
                consecutive_errors = 0
            except RuntimeError as ex:
                logger.info("[TICKER] event loop closed, exit: %s", ex)
                break
            except Exception as ex:
                consecutive_errors += 1
                logger.error("[TICKER] error #%s: %s", consecutive_errors, ex)
                if consecutive_errors >= 5 or app_stop_event.is_set():
                    break

    threading.Thread(target=_standalone_timers_ticker, daemon=True).start()

    for rt in tm.load_standalone_timers():
        nt = StandaloneTimer(rt["timer_type"], rt["time_left"], timer_completion_queue,
                             app_stop_event, notification_type=rt.get("notification_type", "both"))
        nt.total_time = rt["total_time"]
        with standalone_timers_lock:
            standalone_timers.append(nt)
        if not rt.get("was_paused", False):
            nt.start()
        else:
            nt.paused = True

    # Баннер таймера задачи
    tb_title = ft.Text("", size=15, weight=ft.FontWeight.BOLD)
    tb_clock = ft.Text("00:00", size=30, weight=ft.FontWeight.BOLD)
    tb_cycle = ft.Text("", size=12)
    tb_progress = ft.ProgressBar(value=0, width=260)
    btn_pause = ft.ElevatedButton("Пауза", icon=ft.Icons.PAUSE,
                                   on_click=lambda e: timer_state.pause())
    btn_resume = ft.ElevatedButton("Продолжить", icon=ft.Icons.PLAY_ARROW,
                                    visible=False, on_click=lambda e: timer_state.resume())
    btn_stop = ft.ElevatedButton("Стоп", icon=ft.Icons.STOP,
                                  style=ft.ButtonStyle(color=ft.Colors.RED),
                                  on_click=lambda e: (timer_state.stop(), render_tasks()))
    timer_banner = ft.Container(
        visible=False, padding=15, border_radius=10,
        content=ft.Row([
            ft.Icon(ft.Icons.TIMER, size=32),
            ft.Column([tb_title, tb_clock, tb_cycle, tb_progress], spacing=3, expand=True),
            ft.Row([btn_pause, btn_resume, btn_stop], spacing=8),
        ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
           vertical_alignment=ft.CrossAxisAlignment.CENTER),
    )

    def render_timer_banner():
        active = timer_state.time_left > 0
        timer_banner.visible = active
        if not active:
            return
        timer_banner.bgcolor = pal(ft.Colors.BLUE_50, ft.Colors.BLUE_GREY_900)
        timer_banner.border = ft.border.all(2, pal(ft.Colors.BLUE_200, ft.Colors.BLUE_700))
        tb_title.color = pal(ft.Colors.BLUE_900, ft.Colors.BLUE_100)
        tb_clock.color = pal(ft.Colors.BLUE_900, ft.Colors.BLUE_100)
        tb_cycle.color = pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)
        tb_progress.color = pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)
        tb_progress.bgcolor = pal(ft.Colors.BLUE_100, ft.Colors.BLUE_GREY_800)
        task = tm.by_id(timer_state.task_id)
        kind = "Pomodoro" if timer_state.type == "pomodoro" else "Обычный таймер"
        state_mark = " (пауза)" if timer_state.paused else ""
        tb_title.value = (f"{kind} · {MODE_RU.get(timer_state.mode, timer_state.mode)}"
                          f"{state_mark} — {task.title if task else 'Без задачи'}")
        tb_clock.value = fmt_time(timer_state.time_left)
        if timer_state.type == "pomodoro":
            tb_cycle.value = f"Завершено циклов работы: {timer_state.cycles_completed}"
        else:
            tb_cycle.value = f"Всего: {fmt_time(timer_state.total_time)}"
        tb_progress.value = (min(1.0, max(0.0, 1 - timer_state.time_left / timer_state.total_time))
                             if timer_state.total_time else 0)
        btn_pause.visible = timer_state.is_running
        btn_resume.visible = timer_state.paused

    async def on_alarm_triggered(task: Task):
        if app_stop_event.is_set():
            return
        try:
            if task.notification_type in ("sound", "both"):
                threading.Thread(target=play_notification_sound,
                                 args=(tm.settings.volume,), daemon=True).start()
            if task.notification_type in ("popup", "both"):
                page.open(ft.SnackBar(content=ft.Text(f"⏰ БУДИЛЬНИК: {task.title}"),
                                      bgcolor=ft.Colors.ORANGE_700, duration=8000))
            render_tasks()
            page.update()
        except Exception as e:
            logger.exception("[ALARM UI ERROR] %s", e)

    async def on_block_started(task: Task):
        if app_stop_event.is_set():
            return
        try:
            if task.notification_type in ("sound", "both"):
                threading.Thread(target=play_notification_sound,
                                 args=(tm.settings.volume,), daemon=True).start()
            if task.notification_type in ("popup", "both"):
                page.open(ft.SnackBar(
                    content=ft.Text(f"🎯 Блок начался: {task.title} ({task.time_block_duration} мин)"),
                    bgcolor=ft.Colors.TEAL_700, duration=6000))
            render_tasks()
            page.update()
        except Exception as e:
            logger.exception("[BLOCK UI ERROR] %s", e)

    async def on_block_ended(task: Task):
        if app_stop_event.is_set():
            return
        try:
            if task.notification_type in ("sound", "both"):
                threading.Thread(target=play_notification_sound,
                                 args=(tm.settings.volume,), daemon=True).start()
            if task.notification_type in ("popup", "both"):
                page.open(ft.SnackBar(content=ft.Text(f"✅ Блок завершён: {task.title}"),
                                      bgcolor=ft.Colors.BLUE_GREY_700, duration=6000))
            render_tasks()
            page.update()
        except Exception as e:
            logger.exception("[BLOCK END UI ERROR] %s", e)

    async def on_reminder(task: Task, minutes: int):
        if app_stop_event.is_set():
            return
        try:
            if task.notification_type in ("sound", "both"):
                threading.Thread(target=play_notification_sound,
                                 args=(tm.settings.volume,), daemon=True).start()
            if task.notification_type in ("popup", "both"):
                page.open(ft.SnackBar(
                    content=ft.Text(f"⏰ Напоминание за {minutes} мин: {task.title}"),
                    bgcolor=ft.Colors.AMBER_700, duration=6000))
        except Exception as e:
            logger.exception("[REMINDER UI ERROR] %s", e)

    bg_checker = BackgroundChecker(tm, page, on_alarm_triggered, on_block_started,
                                    on_block_ended, on_reminder, app_stop_event)
    bg_checker.start()

    _missed = tm.check_missed_alarms_on_startup()
    if _missed:
        _names = ", ".join(f"«{t.title}» ({t.alarm_time})" for t in _missed[:3])
        if len(_missed) > 3:
            _names += f" и ещё {len(_missed) - 3}"
        toast(f"⚠ Пропущены будильники: {_names}", error=True)

    # Горячие клавиши
    def on_keyboard(e: ft.KeyboardEvent):
        key = (e.key or "").upper()
        ctrl = bool(e.ctrl or e.meta)
        if ctrl and key == "N":
            open_editor()
        elif key in ("ESCAPE", "ESC"):
            dlg = dialog_state.get("current_dialog")
            if dlg is not None:
                unregister_dialog()
                try:
                    page.close(dlg)
                    page.update()
                except Exception:
                    pass
        elif ctrl and key == "S":
            handler = dialog_state.get("save_handler")
            if handler:
                try:
                    handler(None)
                except Exception:
                    pass

    page.on_keyboard_event = on_keyboard
    logger.info("Горячие клавиши установлены: Ctrl+N, Esc, Ctrl+S")

    # Календарь с Timeline и Drag&Drop
    def show_calendar():
        today = date.today()
        view_state = {"year": today.year, "month": today.month}
        title_text = ft.Text("", size=18, weight=ft.FontWeight.BOLD)
        grid = ft.Column(spacing=4)
        legend_row = ft.Row(spacing=12, alignment=ft.MainAxisAlignment.CENTER, wrap=True)
        day_tasks_view = ft.Column(spacing=4, scroll=ft.ScrollMode.AUTO)
        timeline_view = ft.Column(spacing=2, scroll=ft.ScrollMode.AUTO)
        day_tasks_title = ft.Text("Выберите день", size=14, weight=ft.FontWeight.BOLD)
        selected_day = {"d": today}
        show_timeline = {"flag": False}

        def get_day_status(d: date):
            tasks = tm.tasks_for_date(d)
            if not tasks:
                return pal(ft.Colors.GREY_100, ft.Colors.GREY_800), None, False
            total = len(tasks)
            done = sum(1 for t in tasks if t.completed)
            has_carry = any(t.move_to_tomorrow and not t.completed for t in tasks)
            if done == total:
                return ft.Colors.GREEN_200, ft.Icons.CHECK_CIRCLE, has_carry
            if done > 0:
                return ft.Colors.AMBER_200, None, has_carry
            return ft.Colors.RED_200, None, has_carry

        def render_timeline(d: date):
            timeline_view.controls.clear()
            tasks = tm.tasks_for_date(d)
            blocks = []
            for t in tasks:
                if t.use_time_blocking and t.time_block_start and t.time_block_duration > 0:
                    try:
                        h, m = map(int, t.time_block_start.split(":"))
                        start_minutes = h * 60 + m
                        end_minutes = start_minutes + t.time_block_duration
                        blocks.append({"task": t, "start": start_minutes,
                                       "end": end_minutes, "title": t.title})
                    except ValueError:
                        pass
            blocks.sort(key=lambda b: b["start"])
            timeline_view.controls.append(ft.Text("📅 Шкала дня (08:00 - 22:00)",
                                                   size=13, weight=ft.FontWeight.BOLD,
                                                   color=pal(ft.Colors.TEAL_700, ft.Colors.TEAL_200)))
            for hour in range(8, 23):
                hour_start = hour * 60
                hour_blocks = [b for b in blocks if b["start"] < hour_start + 60 and b["end"] > hour_start]
                row_content = [ft.Text(f"{hour:02d}:00", size=11, width=50,
                                        color=pal(ft.Colors.GREY_700, ft.Colors.GREY_300))]
                if hour_blocks:
                    for b in hour_blocks:
                        color = ft.Colors.GREEN_200 if b["task"].completed else ft.Colors.BLUE_200
                        row_content.append(ft.Container(
                            width=20, height=20, bgcolor=color, border_radius=4,
                            tooltip=f"{b['title']} ({b['start']//60:02d}:{b['start']%60:02d})"))
                timeline_view.controls.append(ft.Row(row_content, spacing=4,
                                                      vertical_alignment=ft.CrossAxisAlignment.CENTER))
            try:
                dlg.update()
            except Exception:
                pass

        def render_day_tasks(d: date):
            selected_day["d"] = d
            day_tasks_view.controls.clear()
            tasks = tm.tasks_for_date(d)
            tasks.sort(key=lambda t: (t.time_block_start or "99:99", t.title.lower()))
            if not tasks:
                day_tasks_view.controls.append(ft.Text("Нет задач на этот день", size=13,
                                                         color=ft.Colors.GREY_500, italic=True))
                try:
                    dlg.update()
                except Exception:
                    pass
                if show_timeline["flag"]:
                    render_timeline(d)
                return
            now = datetime.now()
            for t in tasks:
                status_icon = ft.Icons.CHECK_CIRCLE if t.completed else ft.Icons.RADIO_BUTTON_UNCHECKED
                status_color = ft.Colors.GREEN_700 if t.completed else ft.Colors.GREY_500
                carried_mark = " 🔄" if (t.move_to_tomorrow and not t.completed) else ""
                badges = []
                if t.is_shopping_list:
                    badges.append(ft.Text("🛒", size=13))
                if t.use_pomodoro:
                    badges.append(ft.Text("🍅", size=13))
                if t.use_alarm and t.alarm_time:
                    badges.append(ft.Text(f"⏰ {t.alarm_time}", size=12, color=ft.Colors.ORANGE_700))
                if t.recurrence != "none":
                    badges.append(ft.Text("🔁", size=12, color=ft.Colors.PURPLE_700))
                if t.subtasks:
                    badges.append(ft.Text(f"📋 {sum(1 for s in t.subtasks if s.completed)}/{len(t.subtasks)}",
                                          size=12, color=ft.Colors.TEAL_700))
                if t.use_time_blocking and t.time_block_start:
                    parts = ["📅", t.time_block_start]
                    if t.time_block_duration:
                        parts.append(f"+{t.time_block_duration}м")
                    st = block_status(t, now)
                    if st and st["state"] == "active":
                        parts.append("🟢")
                    badges.insert(0, ft.Text(" ".join(parts), size=12, color=ft.Colors.TEAL_700))
                row_content = ft.Row([
                    ft.Icon(status_icon, size=18, color=status_color),
                    ft.Column([
                        ft.Row([ft.Text(t.title + carried_mark, size=14,
                                        weight=ft.FontWeight.BOLD,
                                        color=ft.Colors.GREY_500 if t.completed else None),
                                *badges], spacing=6, wrap=True),
                        ft.Text(f"Папка: {t.folder}", size=11, color=ft.Colors.GREY_600),
                    ], spacing=2, expand=True),
                ], vertical_alignment=ft.CrossAxisAlignment.CENTER)
                card = ft.Container(
                    padding=ft.padding.symmetric(horizontal=10, vertical=6),
                    border=ft.border.all(1, ft.Colors.GREY_300), border_radius=6,
                    content=row_content)
                draggable = ft.Draggable(
                    group="cal_task", data=t.id, content=card,
                    content_feedback=ft.Container(
                        padding=6, bgcolor=ft.Colors.BLUE_100, border_radius=6,
                        content=ft.Text(f"📅 {t.title}", size=12)))
                day_tasks_view.controls.append(draggable)
            try:
                dlg.update()
            except Exception:
                pass
            if show_timeline["flag"]:
                render_timeline(d)

        def on_day_drop(target_date: date, e):
            src_id = None
            try:
                src_id = page.get_control(e.src_id).data
            except Exception:
                src_id = None
            if not src_id:
                return
            task = tm.by_id(src_id)
            if task is None:
                return
            # FIX: проверяем, не дублируется ли задача через time_block
            if task.use_time_blocking:
                active_dates = _get_task_active_dates(task, horizon_days=1)
                if target_date.isoformat() in active_dates:
                    toast("Задача уже отображается в этом дне через time-blocking", error=True)
                    return
            task.planned_date = target_date.isoformat()
            task.last_alarm_triggered = ""
            tm.update(task)
            if tm.last_save_error:
                toast(tm.last_save_error, error=True)
                tm.last_save_error = None
            toast(f"📅 «{task.title}» → {format_date_display_ru(task.planned_date)}")
            render_month()
            selected_day["d"] = target_date
            day_tasks_title.value = (f"📅 {target_date.strftime('%d.%m.%Y')} "
                                     f"({WEEKDAY_NAMES[target_date.weekday()]})")
            render_day_tasks(target_date)
            render_tasks()

        def render_month():
            y, m = view_state["year"], view_state["month"]
            title_text.value = f"{MONTH_NAMES[m - 1]} {y}"
            grid.controls.clear()
            grid.controls.append(ft.Row(
                [ft.Text(d, size=12, weight=ft.FontWeight.BOLD, width=44,
                         text_align=ft.TextAlign.CENTER) for d in WEEKDAY_NAMES],
                alignment=ft.MainAxisAlignment.CENTER, spacing=4))
            first_weekday, days_in_month = calendar.monthrange(y, m)
            current_day = 1
            week_row = ft.Row(spacing=4, alignment=ft.MainAxisAlignment.CENTER)
            for _ in range(first_weekday):
                week_row.controls.append(ft.Container(width=44, height=44))
            while current_day <= days_in_month:
                d = date(y, m, current_day)
                bg_color, icon, is_carried = get_day_status(d)
                is_today = (d == today)
                children = [ft.Text(str(current_day), size=13,
                                    weight=ft.FontWeight.BOLD if is_today else None)]
                if icon:
                    children.append(ft.Icon(icon, size=12, color=ft.Colors.GREEN_800))
                if is_carried:
                    children.append(ft.Text("🔄", size=10))

                def make_click_handler(cd):
                    def handler(e):
                        day_tasks_title.value = (f"📅 {cd.strftime('%d.%m.%Y')} "
                                                  f"({WEEKDAY_NAMES[cd.weekday()]}) — перетащите задачу сюда")
                        render_day_tasks(cd)
                        if show_timeline["flag"]:
                            render_timeline(cd)
                    return handler

                cell = ft.Container(
                    width=44, height=44, bgcolor=bg_color, border_radius=6,
                    border=ft.border.all(2, ft.Colors.BLUE_700) if is_today else None,
                    content=ft.Column(children, horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=0),
                    alignment=ft.alignment.center, on_click=make_click_handler(d), ink=True)

                def make_accept(cd):
                    def accept(e):
                        on_day_drop(cd, e)
                    return accept

                target = ft.DragTarget(group="cal_task", content=cell, on_accept=make_accept(d))
                week_row.controls.append(target)
                if len(week_row.controls) == 7:
                    grid.controls.append(week_row)
                    week_row = ft.Row(spacing=4, alignment=ft.MainAxisAlignment.CENTER)
                current_day += 1
            if week_row.controls:
                while len(week_row.controls) < 7:
                    week_row.controls.append(ft.Container(width=44, height=44))
                grid.controls.append(week_row)
            legend_row.controls = [
                ft.Row([ft.Container(width=14, height=14, bgcolor=ft.Colors.GREEN_200,
                                     border_radius=3), ft.Text("Все", size=11)], spacing=4),
                ft.Row([ft.Container(width=14, height=14, bgcolor=ft.Colors.AMBER_200,
                                     border_radius=3), ft.Text("Частично", size=11)], spacing=4),
                ft.Row([ft.Container(width=14, height=14, bgcolor=ft.Colors.RED_200,
                                     border_radius=3), ft.Text("Нет", size=11)], spacing=4),
                ft.Row([ft.Text("🔄", size=12), ft.Text("Перенос", size=11)], spacing=4),
                ft.Text("🖱️ Перетащите задачу на день", size=11, italic=True,
                        color=ft.Colors.GREY_600),
            ]
            try:
                dlg.update()
            except Exception:
                pass

        def prev_month(e):
            m, y = (view_state["month"] - 1, view_state["year"]) if view_state["month"] > 1 else (12, view_state["year"] - 1)
            view_state["month"], view_state["year"] = m, y
            render_month()

        def next_month(e):
            m, y = (view_state["month"] + 1, view_state["year"]) if view_state["month"] < 12 else (1, view_state["year"] + 1)
            view_state["month"], view_state["year"] = m, y
            render_month()

        def go_today(e):
            view_state["year"], view_state["month"] = today.year, today.month
            render_month()
            day_tasks_title.value = (f"📅 Сегодня — {today.strftime('%d.%m.%Y')} "
                                     f"({WEEKDAY_NAMES[today.weekday()]})")
            render_day_tasks(today)
            if show_timeline["flag"]:
                render_timeline(today)

        def toggle_timeline(e):
            show_timeline["flag"] = not show_timeline["flag"]
            if show_timeline["flag"]:
                render_timeline(selected_day["d"])
            else:
                timeline_view.controls.clear()
            try:
                dlg.update()
            except Exception:
                pass

        def close_dlg():
            unregister_dialog()
            page.close(dlg)
            page.update()

        dlg = ft.AlertDialog(
            modal=False,
            title=ft.Row([
                ft.IconButton(ft.Icons.CHEVRON_LEFT, on_click=prev_month),
                title_text,
                ft.IconButton(ft.Icons.CHEVRON_RIGHT, on_click=next_month),
                ft.ElevatedButton("Сегодня", icon=ft.Icons.TODAY, on_click=go_today),
                ft.ElevatedButton("📊 Шкала", icon=ft.Icons.TIMELINE, on_click=toggle_timeline),
            ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            content=ft.Container(width=750, content=ft.Column([
                grid, legend_row, ft.Divider(), day_tasks_title,
                ft.Container(height=200, content=day_tasks_view,
                             border=ft.border.all(1, ft.Colors.GREY_300),
                             border_radius=6, padding=8),
                timeline_view,
            ], spacing=10, scroll=ft.ScrollMode.AUTO)),
            actions=[ft.TextButton("Закрыть", on_click=lambda e: close_dlg())],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg)
        page.open(dlg)
        page.update()
        render_month()
        day_tasks_title.value = (f"📅 Сегодня — {today.strftime('%d.%m.%Y')} "
                                 f"({WEEKDAY_NAMES[today.weekday()]})")
        render_day_tasks(today)

    # Dashboard
    def show_dashboard():
        stats = tm.get_statistics()

        def make_bar_chart(values: List[float], labels: List[str], color: str):
            max_v = max(values) if values else 0
            groups = []
            for i, v in enumerate(values):
                groups.append(ft.BarChartGroup(
                    x=i, bar_rods=[ft.BarChartRod(
                        from_y=0, to_y=float(v), width=22, color=color,
                        border_radius=4, tooltip=str(int(v)))]))
            bottom_labels = [ft.ChartAxisLabel(value=i, label=ft.Text(labels[i], size=11))
                            for i in range(len(labels))]
            step = max(1, int(math.ceil(max_v / 4))) if max_v > 0 else 1
            left_labels = []
            v = 0
            while v <= max(step * 4, int(max_v) + step):
                left_labels.append(ft.ChartAxisLabel(value=v, label=ft.Text(str(v), size=10)))
                v += step
            return ft.BarChart(
                bar_groups=groups, max_y=max(step * 4, int(max_v) + step),
                border=ft.border.all(1, pal(ft.Colors.GREY_300, ft.Colors.GREY_700)),
                horizontal_grid_lines=ft.ChartGridLines(
                    color=pal(ft.Colors.GREY_200, ft.Colors.GREY_800), width=1),
                left_axis=ft.ChartAxis(labels=left_labels, labels_size=32),
                bottom_axis=ft.ChartAxis(labels=bottom_labels, labels_size=28),
                groups_space=14, expand=True)

        summary = ft.Column([
            ft.Text(f"Всего задач: {stats['total_tasks']}", size=15),
            ft.Text(f"Выполнено всего: {stats['completed_tasks']}", size=15,
                    color=ft.Colors.GREEN_600, weight=ft.FontWeight.BOLD),
            ft.Text(f"🔥 Streak: {stats['streak']} дней подряд", size=16,
                    color=ft.Colors.ORANGE_700, weight=ft.FontWeight.BOLD),
            ft.Text(f"Выполнено за неделю: {stats['week_completed']}", size=15),
            ft.Text(f"Выполнено за месяц: {stats['month_completed']}", size=15),
            ft.Text(f"Среднее время выполнения: {stats['avg_completion_time']:.0f} мин", size=15),
            ft.Text(f"Среднее время блока: {stats['avg_block_time']:.0f} мин", size=15),
            ft.Text(f"Расходы по покупкам: {fmt_money(stats['total_expenses'])} ₽",
                    size=15, color=ft.Colors.ORANGE_700, weight=ft.FontWeight.BOLD),
            ft.Text(f"Пик активности (завершение): {stats['peak_completion_hour']}:00", size=14),
            ft.Text(f"Пик планирования: {stats['peak_planned_hour']}:00", size=14),
            ft.Text(f"Пик работы (блоки): {stats['peak_active_hour']}:00", size=14),
        ], spacing=6)

        period_chart = ft.Container(height=200, content=make_bar_chart(
            [stats["week_completed"], stats["month_completed"]],
            ["Неделя", "Месяц"], ft.Colors.GREEN_600))
        weekday_chart = ft.Container(height=220, content=make_bar_chart(
            [stats["weekday_stats"].get(i, 0) for i in range(7)],
            WEEKDAY_NAMES, ft.Colors.PURPLE_500))
        hourly_chart = ft.Container(height=220, content=make_bar_chart(
            [stats["hourly_stats"].get(h, 0) for h in range(24)],
            [f"{h:02d}" for h in range(24)], ft.Colors.BLUE_500))

        cycles_rows = []
        for t in sorted(tm.tasks, key=lambda x: -x.completed_cycles):
            if t.completed_cycles > 0:
                cycles_rows.append(ft.Row([
                    ft.Text(t.title, size=13, expand=True),
                    ft.Text(f"🍅 {t.completed_cycles}", size=13,
                            weight=ft.FontWeight.BOLD, color=ft.Colors.RED_600)]))
        if not cycles_rows:
            cycles_rows.append(ft.Text("Пока нет завершённых циклов", size=13,
                                       color=ft.Colors.GREY_500, italic=True))

        est_rows = []
        for est, act in stats.get("estimated_vs_actual", [])[:10]:
            diff = act - est
            color = ft.Colors.GREEN_600 if diff <= 0 else ft.Colors.RED_600
            est_rows.append(ft.Row([
                ft.Text(f"План: {est} мин", size=12, width=100),
                ft.Text(f"Факт: {act} мин", size=12, width=100),
                ft.Text(f"{'+' if diff > 0 else ''}{diff} мин", size=12, color=color)]))
        if not est_rows:
            est_rows.append(ft.Text("Нет данных план/факт", size=13,
                                    color=ft.Colors.GREY_500, italic=True))

        def export_stats(e):
            try:
                fp = f"stats_{date.today().isoformat()}.csv"
                tm.export_stats_csv(fp, stats)
                toast(f"✓ Статистика: {os.path.abspath(fp)}")
            except Exception as ex:
                toast(f"Ошибка экспорта: {ex}", error=True)

        def export_tasks(e):
            try:
                fp = f"tasks_{date.today().isoformat()}.csv"
                tm.export_tasks_csv(fp)
                toast(f"✓ Задачи: {os.path.abspath(fp)}")
            except Exception as ex:
                toast(f"Ошибка экспорта: {ex}", error=True)

        def export_backup(e):
            try:
                stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                folder = f"backup_{stamp}"
                os.makedirs(folder, exist_ok=True)
                for fn in (tm.data_file, tm.settings_file, tm.templates_file, tm.timers_file):
                    if os.path.exists(fn):
                        shutil.copy2(fn, os.path.join(folder, os.path.basename(fn)))
                toast(f"✓ Бэкап: {os.path.abspath(folder)}")
            except Exception as ex:
                toast(f"Ошибка бэкапа: {ex}", error=True)

        def close_dlg():
            unregister_dialog()
            page.close(dlg)
            page.update()

        dlg = ft.AlertDialog(
            modal=False, title=ft.Text("📊 Статистика"),
            content=ft.Container(width=750, content=ft.Column([
                summary, ft.Divider(),
                ft.Text("Выполнено за неделю / месяц:", weight=ft.FontWeight.BOLD),
                period_chart,
                ft.Text("Продуктивность по дням недели:", weight=ft.FontWeight.BOLD),
                weekday_chart,
                ft.Text("Активность по часам:", weight=ft.FontWeight.BOLD),
                hourly_chart,
                ft.Divider(),
                ft.Text("Завершённые циклы по задачам:", weight=ft.FontWeight.BOLD),
                ft.Container(height=140, content=ft.Column(cycles_rows, spacing=4,
                                                            scroll=ft.ScrollMode.AUTO)),
                ft.Divider(),
                ft.Text("План vs Факт:", weight=ft.FontWeight.BOLD),
                ft.Container(height=140, content=ft.Column(est_rows, spacing=4,
                                                            scroll=ft.ScrollMode.AUTO)),
            ], spacing=10, scroll=ft.ScrollMode.AUTO)),
            actions=[
                ft.ElevatedButton("Статистика CSV", icon=ft.Icons.DOWNLOAD, on_click=export_stats),
                ft.ElevatedButton("Задачи CSV", icon=ft.Icons.DOWNLOAD, on_click=export_tasks),
                ft.ElevatedButton("Бэкап", icon=ft.Icons.SAVE, on_click=export_backup),
                ft.TextButton("Закрыть", on_click=lambda e: close_dlg()),
            ],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg)
        page.open(dlg)
        page.update()

    # Шаблоны
    def show_templates():
        def create_from_template(tpl):
            new_task = Task(
                id=str(uuid.uuid4()),
                title=tpl.get("title") or tpl.get("name") or "Задача",
                folder=tpl.get("folder") or (tm.folders[0].name if tm.folders else "Дом"),
                is_shopping_list=tpl.get("is_shopping_list", False),
                move_to_tomorrow=tpl.get("move_to_tomorrow", False),
                use_time_blocking=tpl.get("use_time_blocking", False),
                use_pomodoro=tpl.get("use_pomodoro", False),
                use_timer=tpl.get("use_timer", False),
                use_alarm=tpl.get("use_alarm", False),
                planned_date=date.today().isoformat(),
                notification_type=tpl.get("notification_type", "both"),
                time_block_start=tpl.get("time_block_start", ""),
                time_block_duration=tpl.get("time_block_duration", 0),
                time_block_days=list(tpl.get("time_block_days", [])),
                time_block_dates=list(tpl.get("time_block_dates", [])),
                alarm_time=tpl.get("alarm_time", ""),
                recurrence=tpl.get("recurrence", "none"),
                comment=tpl.get("comment", ""),
                subtasks=[Subtask(id=str(uuid.uuid4()), title=s, completed=False)
                          for s in tpl.get("subtasks", [])],
                shopping_items=[ShoppingItem(id=str(uuid.uuid4()), title=s, bought=False)
                                for s in tpl.get("shopping_items", [])],
                estimated_minutes=tpl.get("estimated_minutes", 0),
                reminder_minutes=tpl.get("reminder_minutes", 0),
            )
            tm.add(new_task)
            close_dlg()
            render_tasks()
            toast(f"✓ Создано из шаблона «{tpl.get('name', '')}»")

        def delete_template(idx: int):
            if 0 <= idx < len(tm.templates):
                tm.templates.pop(idx)
                tm.save_templates()
            close_dlg()
            show_templates()

        def open_save_template(e):
            name_f = ft.TextField(label="Название шаблона", width=420)
            title_f = ft.TextField(label="Название задачи", width=420)
            folder_f = ft.Dropdown(label="Папка", width=220,
                                   options=[ft.dropdown.Option(f.name) for f in tm.folders],
                                   value=tm.folders[0].name if tm.folders else None)
            sw_shop = ft.Switch(label="Список покупок")
            sw_carry = ft.Switch(label="Переносить на завтра")
            sw_block = ft.Switch(label="Time blocking")
            sw_pomo = ft.Switch(label="Pomodoro")
            sw_timer = ft.Switch(label="Обычный таймер")
            sw_alarm = ft.Switch(label="Будильник")
            rec_f = ft.Dropdown(label="Повторение", width=220, value="none",
                                options=[ft.dropdown.Option(k, v) for k, v in RECURRENCE_RU.items()])
            tb_start = ft.TextField(label="Начало блока (ЧЧ:ММ)", width=170)
            tb_dur = ft.TextField(label="Длительность (мин)", width=170,
                                  keyboard_type=ft.KeyboardType.NUMBER)
            alarm_f = ft.TextField(label="Будильник (ЧЧ:ММ)", width=170)
            est_f = ft.TextField(label="Оценка времени (мин)", width=170,
                                 keyboard_type=ft.KeyboardType.NUMBER)
            reminder_f = ft.Dropdown(label="Напоминание за", width=170, value="0",
                                     options=[ft.dropdown.Option("0", "Нет"),
                                              ft.dropdown.Option("5", "5 мин"),
                                              ft.dropdown.Option("15", "15 мин"),
                                              ft.dropdown.Option("30", "30 мин")])
            day_boxes = {c: ft.Checkbox(label=ru) for c, ru in DAYS}
            subs_f = ft.TextField(label="Подзадачи (через запятую)", width=420)
            items_f = ft.TextField(label="Товары (через запятую)", width=420)
            err = ft.Text("", color=ft.Colors.RED, size=12)

            def do_save(ev):
                name = (name_f.value or "").strip()
                title = (title_f.value or "").strip()
                if not name or not title:
                    err.value = "Заполните название шаблона и задачи"
                    page.update()
                    return
                tpl = {
                    "name": name, "title": title, "folder": folder_f.value,
                    "is_shopping_list": sw_shop.value, "move_to_tomorrow": sw_carry.value,
                    "use_time_blocking": sw_block.value, "use_pomodoro": sw_pomo.value,
                    "use_timer": sw_timer.value, "use_alarm": sw_alarm.value,
                    "notification_type": "both", "recurrence": rec_f.value,
                    "time_block_start": normalize_hhmm(tb_start.value) if sw_block.value else "",
                    "time_block_duration": parse_positive_int(tb_dur.value, 0, 1440) if sw_block.value else 0,
                    "time_block_days": [c for c, cb in day_boxes.items() if cb.value] if sw_block.value else [],
                    "alarm_time": normalize_hhmm(alarm_f.value) if sw_alarm.value else "",
                    "estimated_minutes": parse_positive_int(est_f.value, 0, 9999),
                    "reminder_minutes": int(reminder_f.value or 0),
                    "subtasks": [s.strip() for s in (subs_f.value or "").split(",") if s.strip()],
                    "shopping_items": [s.strip() for s in (items_f.value or "").split(",") if s.strip()],
                }
                tm.templates.append(tpl)
                tm.save_templates()
                page.close(save_dlg)
                page.update()
                close_dlg()
                show_templates()
                toast(f"✓ Шаблон «{name}» сохранён")

            def cancel(ev):
                page.close(save_dlg)
                register_dialog(dlg)
                page.update()

            save_dlg = ft.AlertDialog(
                modal=True, title=ft.Text("Новый шаблон"),
                content=ft.Container(width=470, content=ft.Column([
                    name_f, title_f, folder_f, rec_f,
                    sw_shop, sw_carry, sw_block, sw_pomo, sw_timer, sw_alarm,
                    ft.Row([tb_start, tb_dur], spacing=8, wrap=True),
                    ft.Row([day_boxes[c] for c, _ in DAYS], spacing=6, wrap=True),
                    alarm_f, est_f, reminder_f, subs_f, items_f, err,
                ], spacing=8, scroll=ft.ScrollMode.AUTO)),
                actions=[ft.TextButton("Отмена", on_click=cancel),
                         ft.ElevatedButton("Сохранить", icon=ft.Icons.SAVE, on_click=do_save)],
                actions_alignment=ft.MainAxisAlignment.END)
            register_dialog(save_dlg, do_save)
            page.open(save_dlg)
            page.update()

        def close_dlg():
            unregister_dialog()
            page.close(dlg)
            page.update()

        rows = []
        if not tm.templates:
            rows.append(ft.Text("Нет сохранённых шаблонов", size=14,
                                color=ft.Colors.GREY_500, italic=True))
        for idx, tpl in enumerate(list(tm.templates)):
            rows.append(ft.Container(
                padding=10, border=ft.border.all(1, ft.Colors.GREY_300), border_radius=8,
                content=ft.Row([
                    ft.Column([
                        ft.Text(tpl.get("name", "—"), size=15, weight=ft.FontWeight.BOLD),
                        ft.Text(tpl.get("title", ""), size=12, color=ft.Colors.GREY_600),
                    ], spacing=2, expand=True),
                    ft.ElevatedButton("Создать", icon=ft.Icons.ADD,
                                      on_click=lambda e, t=tpl: create_from_template(t)),
                    ft.IconButton(ft.Icons.DELETE, icon_color=ft.Colors.RED_400,
                                  on_click=lambda e, i=idx: delete_template(i)),
                ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN)))

        dlg = ft.AlertDialog(
            modal=False, title=ft.Text("📝 Шаблоны задач"),
            content=ft.Container(width=620, content=ft.Column(rows, spacing=8,
                                                               scroll=ft.ScrollMode.AUTO)),
            actions=[
                ft.ElevatedButton("Новый шаблон", icon=ft.Icons.ADD, on_click=open_save_template),
                ft.TextButton("Закрыть", on_click=lambda e: close_dlg()),
            ],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg)
        page.open(dlg)
        page.update()

    # Редактор задачи
    def open_editor(task: Optional[Task] = None):
        title_field = ft.TextField(label="Название задачи", width=520,
                                   value=task.title if task else "")
        folder_dd = ft.Dropdown(label="Папка", width=200,
                                options=[ft.dropdown.Option(f.name) for f in tm.folders],
                                value=(task.folder if task and task.folder in [f.name for f in tm.folders]
                                       else (current_folder if current_folder in [f.name for f in tm.folders]
                                             else (tm.folders[0].name if tm.folders else None))))
        date_field = ft.TextField(label="Дата задачи (ДД.ММ.ГГГГ)", width=220,
                                  value=(format_date_display_ru(task.planned_date) if task and task.planned_date
                                         else date.today().strftime("%d.%m.%Y")),
                                  hint_text="15112025 или 15.11.2025")

        def on_date_field_change(e):
            e.control.error_text = None
            try:
                e.control.update()
            except Exception:
                pass
        date_field.on_change = on_date_field_change

        recurrence_dd = ft.Dropdown(label="Повторение", width=200,
                                    value=task.recurrence if task else "none",
                                    options=[ft.dropdown.Option(k, v) for k, v in RECURRENCE_RU.items()])
        est_field = ft.TextField(label="Оценка времени (мин)", width=150,
                                 value=str(task.estimated_minutes) if task and task.estimated_minutes else "",
                                 keyboard_type=ft.KeyboardType.NUMBER, hint_text="0 = не оценивать")
        reminder_dd = ft.Dropdown(label="Напоминание за", width=150,
                                  value=str(task.reminder_minutes) if task else "0",
                                  options=[ft.dropdown.Option("0", "Нет"),
                                           ft.dropdown.Option("5", "5 мин"),
                                           ft.dropdown.Option("15", "15 мин"),
                                           ft.dropdown.Option("30", "30 мин")])

        sw_shopping = ft.Switch(label="Список покупок", value=task.is_shopping_list if task else False)
        sw_carry = ft.Switch(label="Переносить на завтра", value=task.move_to_tomorrow if task else False)
        sw_block = ft.Switch(label="Time blocking", value=task.use_time_blocking if task else False)
        sw_pomodoro = ft.Switch(label="Pomodoro", value=task.use_pomodoro if task else False)
        sw_timer = ft.Switch(label="Обычный таймер", value=task.use_timer if task else False)
        sw_alarm = ft.Switch(label="Будильник", value=task.use_alarm if task else False)
        notif_dd = ft.Dropdown(label="Уведомление по окончании", width=300,
                               value=task.notification_type if task else "both",
                               options=[ft.dropdown.Option("both", "🔊 Звук + окно"),
                                        ft.dropdown.Option("sound", "🔊 Только звук"),
                                        ft.dropdown.Option("popup", "💬 Только окно"),
                                        ft.dropdown.Option("none", "🔇 Без уведомления")])

        tb_time = ft.TextField(label="Начало (ЧЧ:ММ)", width=180,
                               value=task.time_block_start if task else "")
        tb_duration = ft.TextField(label="Длительность (мин)", width=180,
                                   keyboard_type=ft.KeyboardType.NUMBER,
                                   value=(str(task.time_block_duration)
                                          if task and task.time_block_duration else ""))
        day_boxes = {code: ft.Checkbox(label=ru, value=(code in task.time_block_days) if task else False)
                     for code, ru in DAYS}
        time_block_dates_field = ft.TextField(
            label="Конкретные даты (через запятую, ДД.ММ.ГГГГ)", width=560,
            value=", ".join(format_date_display_ru(iso)
                            for iso in (task.time_block_dates if task else [])),
            hint_text="15.11.2025, 20.11.2025, 25-11-2025")

        def on_tb_dates_change(e):
            e.control.error_text = None
            try:
                e.control.update()
            except Exception:
                pass
        time_block_dates_field.on_change = on_tb_dates_change

        time_blocking_fields = ft.Container(
            visible=task.use_time_blocking if task else False,
            content=ft.Column([
                ft.Row([tb_time, tb_duration], spacing=10),
                ft.Text("Дни недели (пусто = только в день задачи):", size=13),
                ft.Row([day_boxes[code] for code, _ in DAYS], spacing=8, wrap=True),
                ft.Divider(height=1),
                ft.Text("Конкретные даты (пусто = не используется). Работает как ИЛИ с днями недели:", size=13),
                time_block_dates_field,
            ], spacing=8))

        # Подзадачи
        subtasks_data: List[dict] = []
        if task:
            subtasks_data = [{"id": s.id, "title": s.title, "completed": s.completed}
                             for s in task.subtasks]
        subtasks_view = ft.Column(spacing=2)
        subtask_progress_text = ft.Text("", size=12, color=ft.Colors.TEAL_700)
        subtask_progress_bar = ft.ProgressBar(value=0, color=ft.Colors.GREEN_600,
                                              bgcolor=ft.Colors.GREY_300)
        new_subtask_field = ft.TextField(label="Новая подзадача", expand=True, dense=True)

        def refresh_subtasks_view():
            subtasks_view.controls.clear()
            for i, sub in enumerate(subtasks_data):
                def make_toggle(idx):
                    def handler(e):
                        subtasks_data[idx]["completed"] = bool(e.control.value)
                        refresh_subtasks_view()
                    return handler

                def make_delete(idx):
                    def handler(e):
                        if 0 <= idx < len(subtasks_data):
                            subtasks_data.pop(idx)
                        refresh_subtasks_view()
                    return handler

                def make_edit(idx):
                    def handler(e):
                        edit_field = ft.TextField(value=subtasks_data[idx]["title"], width=300)
                        def do_save(ev):
                            subtasks_data[idx]["title"] = (edit_field.value or "").strip() or subtasks_data[idx]["title"]
                            page.close(edit_dlg)
                            page.update()
                            refresh_subtasks_view()
                        edit_dlg = ft.AlertDialog(
                            modal=True, title=ft.Text("Редактировать подзадачу"),
                            content=edit_field,
                            actions=[ft.TextButton("Отмена", on_click=lambda e: page.close(edit_dlg)),
                                     ft.ElevatedButton("Сохранить", on_click=do_save)],
                            actions_alignment=ft.MainAxisAlignment.END)
                        page.open(edit_dlg)
                        page.update()
                    return handler

                cb = ft.Checkbox(value=sub["completed"], on_change=make_toggle(i))
                txt = ft.Text(sub["title"], expand=True, size=13,
                              color=ft.Colors.GREY_500 if sub["completed"] else None,
                              style=ft.TextStyle(
                                  decoration=ft.TextDecoration.LINE_THROUGH if sub["completed"] else None))
                subtasks_view.controls.append(ft.Row([
                    cb, txt,
                    ft.IconButton(ft.Icons.EDIT, icon_size=16, icon_color=ft.Colors.BLUE_400,
                                  on_click=make_edit(i), tooltip="Редактировать"),
                    ft.IconButton(ft.Icons.DELETE_OUTLINE, icon_size=16, icon_color=ft.Colors.RED_400,
                                  on_click=make_delete(i)),
                ], spacing=2))
            done = sum(1 for s in subtasks_data if s["completed"])
            total = len(subtasks_data)
            subtask_progress_text.value = f"Выполнено {done}/{total}"
            subtask_progress_bar.value = (done / total) if total else 0
            try:
                subtasks_view.update()
                subtask_progress_text.update()
                subtask_progress_bar.update()
            except Exception:
                pass

        def add_subtask(e):
            t = (new_subtask_field.value or "").strip()
            if not t:
                return
            subtasks_data.append({"id": str(uuid.uuid4()), "title": t, "completed": False})
            new_subtask_field.value = ""
            refresh_subtasks_view()
            try:
                new_subtask_field.focus()
            except Exception:
                pass
        new_subtask_field.on_submit = add_subtask

        sw_auto_complete = ft.Switch(
            label="Автозавершение задачи при выполнении всех подзадач",
            value=task.auto_complete_on_subtasks if task else False)

        subtasks_block = ft.Container(
            visible=bool(task and task.subtasks), padding=10, border_radius=6,
            bgcolor=pal(ft.Colors.TEAL_50, ft.Colors.TEAL_900),
            content=ft.Column([
                ft.Text("📋 Подзадачи:", size=12, weight=ft.FontWeight.BOLD,
                        color=pal(ft.Colors.TEAL_700, ft.Colors.TEAL_200)),
                subtask_progress_text, subtask_progress_bar, subtasks_view,
                ft.Row([new_subtask_field,
                        ft.IconButton(ft.Icons.ADD_CIRCLE, icon_color=ft.Colors.GREEN,
                                      on_click=add_subtask, tooltip="Добавить")]),
                sw_auto_complete,
            ], spacing=6))
        sw_subtasks = ft.Switch(label="Подзадачи (чек-лист)",
                                value=bool(task and task.subtasks))

        def toggle_subtasks(e):
            subtasks_block.visible = bool(sw_subtasks.value)
            try:
                dlg.update()
            except Exception:
                pass
        sw_subtasks.on_change = toggle_subtasks

        # Таймеры
        tf_pomo_work = ft.TextField(label="Работа, мин", width=100,
                                    value=str(tm.settings.pomodoro_work),
                                    keyboard_type=ft.KeyboardType.NUMBER)
        tf_pomo_break = ft.TextField(label="Перерыв, мин", width=100,
                                     value=str(tm.settings.pomodoro_break),
                                     keyboard_type=ft.KeyboardType.NUMBER)
        tf_pomo_long = ft.TextField(label="Длинный перерыв, мин", width=130,
                                    value=str(tm.settings.pomodoro_long_break),
                                    keyboard_type=ft.KeyboardType.NUMBER)
        tf_pomo_cycles = ft.TextField(label="Циклов", width=90,
                                      value=str(tm.settings.pomodoro_cycles),
                                      keyboard_type=ft.KeyboardType.NUMBER)
        sw_pomo_long = ft.Switch(label="Длинный перерыв", value=tm.settings.long_break_enabled)
        sw_pomo_auto = ft.Switch(label="Автопереход", value=tm.settings.auto_continue)
        pomodoro_settings_block = ft.Container(
            visible=task.use_pomodoro if task else False, padding=10,
            bgcolor=pal(ft.Colors.RED_50, ft.Colors.RED_900), border_radius=6,
            content=ft.Column([
                ft.Text("🍅 Настройки Pomodoro:", size=12, weight=ft.FontWeight.BOLD,
                        color=pal(ft.Colors.RED_700, ft.Colors.RED_200)),
                ft.Row([tf_pomo_work, tf_pomo_break], wrap=True),
                ft.Row([tf_pomo_long, tf_pomo_cycles], wrap=True),
                ft.Row([sw_pomo_long, sw_pomo_auto], wrap=True),
            ], spacing=6))
        tf_regular = ft.TextField(label="Длительность, мин", width=150,
                                  value=str(tm.settings.regular_timer_minutes),
                                  keyboard_type=ft.KeyboardType.NUMBER)
        timer_settings_block = ft.Container(
            visible=task.use_timer if task else False, padding=10,
            bgcolor=pal(ft.Colors.PURPLE_50, ft.Colors.PURPLE_900), border_radius=6,
            content=ft.Column([
                ft.Text("⏳ Настройки обычного таймера:", size=12, weight=ft.FontWeight.BOLD,
                        color=pal(ft.Colors.PURPLE_700, ft.Colors.PURPLE_200)),
                tf_regular,
            ], spacing=6))
        initial_alarm = normalize_hhmm(task.alarm_time) if task and task.alarm_time else ""
        alarm_time_field = ft.TextField(label="Время будильника (ЧЧ:ММ)", width=200,
                                        value=initial_alarm, hint_text="Например: 09:30",
                                        bgcolor=pal(ft.Colors.WHITE, ft.Colors.GREY_800),
                                        color=pal(ft.Colors.BLACK, ft.Colors.WHITE))
        alarm_hint = ft.Text(f"Текущее время: {datetime.now().strftime('%H:%M')}",
                             size=11, color=ft.Colors.GREY_600, italic=True)

        def on_alarm_time_blur(e):
            val = normalize_hhmm(alarm_time_field.value)
            if val != (alarm_time_field.value or ""):
                alarm_time_field.value = val
                try:
                    alarm_time_field.update()
                except Exception:
                    pass
        alarm_time_field.on_blur = on_alarm_time_blur

        alarm_settings_block = ft.Container(
            visible=task.use_alarm if task else False, padding=10,
            bgcolor=pal(ft.Colors.ORANGE_50, ft.Colors.ORANGE_900), border_radius=6,
            content=ft.Column([
                ft.Text("⏰ Настройки будильника:", size=12, weight=ft.FontWeight.BOLD,
                        color=pal(ft.Colors.ORANGE_700, ft.Colors.ORANGE_200)),
                ft.Row([alarm_time_field, alarm_hint], spacing=10),
            ], spacing=6))

        # Покупки
        working_items: List[ShoppingItem] = []
        if task:
            working_items = [ShoppingItem(id=it.id, title=it.title, bought=it.bought,
                                          quantity=it.quantity, price=it.price)
                             for it in task.shopping_items]
        shopping_list_view = ft.ListView(height=180, spacing=4)
        new_item_field = ft.TextField(label="Новый товар", expand=True, dense=True)

        def refresh_shopping_view():
            shopping_list_view.controls.clear()
            for item in working_items:
                def make_delete_handler(it_id):
                    def handler(e):
                        for i, x in enumerate(working_items):
                            if x.id == it_id:
                                working_items.pop(i)
                                break
                        refresh_shopping_view()
                    return handler

                def make_edit_handler(it):
                    def handler(e):
                        edit_field = ft.TextField(value=it.title, width=300)
                        def do_save(ev):
                            it.title = (edit_field.value or "").strip() or it.title
                            page.close(edit_dlg)
                            page.update()
                            refresh_shopping_view()
                        edit_dlg = ft.AlertDialog(
                            modal=True, title=ft.Text("Редактировать товар"),
                            content=edit_field,
                            actions=[ft.TextButton("Отмена", on_click=lambda e: page.close(edit_dlg)),
                                     ft.ElevatedButton("Сохранить", on_click=do_save)],
                            actions_alignment=ft.MainAxisAlignment.END)
                        page.open(edit_dlg)
                        page.update()
                    return handler

                shopping_list_view.controls.append(ft.Container(
                    content=ft.Row([
                        ft.Text(item.title, expand=True, size=14),
                        ft.IconButton(ft.Icons.EDIT, icon_size=16, icon_color=ft.Colors.BLUE_400,
                                      on_click=make_edit_handler(item), tooltip="Редактировать"),
                        ft.IconButton(ft.Icons.DELETE_OUTLINE, icon_size=18, icon_color=ft.Colors.RED_400,
                                      on_click=make_delete_handler(item.id)),
                    ]),
                    padding=ft.padding.only(left=10, right=5)))
            try:
                shopping_list_view.update()
            except Exception:
                pass

        def add_shopping_item(e):
            t = (new_item_field.value or "").strip()
            if not t:
                return
            working_items.append(ShoppingItem(id=str(uuid.uuid4()), title=t))
            new_item_field.value = ""
            refresh_shopping_view()
            try:
                new_item_field.focus()
            except Exception:
                pass
        new_item_field.on_submit = add_shopping_item

        shopping_block = ft.Container(
            visible=task.is_shopping_list if task else False,
            content=ft.Column([
                ft.Text("Товары в списке:", weight=ft.FontWeight.BOLD, size=14,
                        color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)),
                ft.Text("Количество и цену можно задать в карточке задачи (иконка ℹ️)",
                        size=11, color=ft.Colors.GREY_600, italic=True),
                shopping_list_view,
                ft.Row([new_item_field,
                        ft.IconButton(ft.Icons.ADD_CIRCLE, icon_color=ft.Colors.GREEN,
                                      on_click=add_shopping_item, tooltip="Добавить")]),
            ], spacing=8))

        def toggle_time_blocking(e):
            time_blocking_fields.visible = sw_block.value
            try:
                dlg.update()
            except Exception:
                pass

        def toggle_shopping(e):
            shopping_block.visible = sw_shopping.value
            try:
                dlg.update()
            except Exception:
                pass

        def toggle_pomodoro(e):
            pomodoro_settings_block.visible = sw_pomodoro.value
            try:
                dlg.update()
            except Exception:
                pass

        def toggle_timer(e):
            timer_settings_block.visible = sw_timer.value
            try:
                dlg.update()
            except Exception:
                pass

        def toggle_alarm(e):
            alarm_settings_block.visible = sw_alarm.value
            if not sw_alarm.value:
                alarm_time_field.value = ""
                alarm_time_field.error_text = None
            try:
                dlg.update()
            except Exception:
                pass

        sw_block.on_change = toggle_time_blocking
        sw_shopping.on_change = toggle_shopping
        sw_pomodoro.on_change = toggle_pomodoro
        sw_timer.on_change = toggle_timer
        sw_alarm.on_change = toggle_alarm

        def close_dlg(e=None):
            unregister_dialog()
            page.close(dlg)
            page.update()

        def save_task(e=None):
            title = (title_field.value or "").strip()
            title_field.error_text = None if title else "Введите название"
            date_field.error_text = None
            date_raw = (date_field.value or "").strip()
            parsed = parse_date_input(date_raw) if date_raw else None
            planned_iso = parsed if parsed else date.today().isoformat()
            if date_raw and not parsed:
                date_field.error_text = "Формат: ДД.ММ.ГГГГ или ДДММГГГГ"

            tb_time.error_text = None
            tb_duration.error_text = None
            time_block_dates_field.error_text = None
            start = normalize_hhmm(tb_time.value)
            dur_raw = (tb_duration.value or "").strip()
            duration = 0
            parsed_dates: List[str] = []

            if sw_block.value:
                if not start:
                    tb_time.error_text = "Укажите начало блока"
                elif not valid_hhmm(start):
                    tb_time.error_text = "Формат 09:30"
                if not dur_raw:
                    tb_duration.error_text = "Укажите длительность"
                elif not dur_raw.isdigit() or int(dur_raw) <= 0:
                    tb_duration.error_text = "Целое > 0"
                elif int(dur_raw) > 1440:
                    tb_duration.error_text = "Не больше 1440"
                elif start and valid_hhmm(start):
                    hh, mm = map(int, start.split(":"))
                    if hh * 60 + mm + int(dur_raw) > 24 * 60:
                        tb_duration.error_text = "Блок выходит за полночь"
                    else:
                        duration = int(dur_raw)
                dates_raw = (time_block_dates_field.value or "").strip()
                parsed_dates, invalid_dates = parse_dates_multi(dates_raw)
                if invalid_dates:
                    time_block_dates_field.error_text = (
                        "Неверные даты: " + ", ".join(invalid_dates[:3]))
                if not (tb_time.error_text or tb_duration.error_text
                        or time_block_dates_field.error_text):
                    probe = Task(
                        id=task.id if task else "__probe__",
                        title="probe", folder="probe",
                        planned_date=planned_iso,
                        use_time_blocking=True,
                        time_block_start=start,
                        time_block_duration=duration,
                        time_block_days=[c for c, cb in day_boxes.items() if cb.value],
                        time_block_dates=parsed_dates)
                    conflicts = find_block_conflicts(probe, tm.tasks)
                    if conflicts:
                        names = ", ".join(f"«{c.title}»" for c in conflicts[:3])
                        tb_time.error_text = f"Пересекается с: {names}"
            elif dur_raw:
                if not dur_raw.isdigit():
                    tb_duration.error_text = "Целое число"
                else:
                    duration = min(1440, int(dur_raw))

            alarm_time_value = ""
            alarm_time_field.error_text = None
            if sw_alarm.value:
                raw_time = normalize_hhmm(alarm_time_field.value)
                if not valid_hhmm(raw_time):
                    alarm_time_field.error_text = "Формат: ЧЧ:ММ (например, 09:30)"
                else:
                    alarm_time_field.value = raw_time
                    alarm_time_value = raw_time

            if (title_field.error_text or date_field.error_text or tb_time.error_text
                    or tb_duration.error_text or alarm_time_field.error_text
                    or (sw_block.value and time_block_dates_field.error_text)):
                page.update()
                return

            days = [c for c, cb in day_boxes.items() if cb.value] if sw_block.value else []
            dates = parsed_dates if sw_block.value else []

            # FIX: единая валидация настроек
            if sw_pomodoro.value:
                tm.settings.pomodoro_work = parse_positive_int(tf_pomo_work.value, 25, 999)
                tm.settings.pomodoro_break = parse_positive_int(tf_pomo_break.value, 5, 999)
                tm.settings.pomodoro_long_break = parse_positive_int(tf_pomo_long.value, 15, 999)
                tm.settings.pomodoro_cycles = parse_positive_int(tf_pomo_cycles.value, 4, 1000)
                tm.settings.long_break_enabled = sw_pomo_long.value
                tm.settings.auto_continue = sw_pomo_auto.value
            if sw_timer.value:
                tm.settings.regular_timer_minutes = parse_positive_int(tf_regular.value, 15, 9999)
            if sw_pomodoro.value or sw_timer.value:
                try:
                    tm.save_settings()
                except Exception:
                    toast("Не удалось сохранить настройки таймеров", error=True)

            subtasks_list = []
            if sw_subtasks.value:
                subtasks_list = [Subtask(id=s["id"], title=s["title"], completed=s["completed"])
                                 for s in subtasks_data]

            est_minutes = parse_positive_int(est_field.value, 0, 9999)
            reminder_min = int(reminder_dd.value or 0)

            data = dict(
                title=title,
                folder=folder_dd.value or (tm.folders[0].name if tm.folders else "Без папки"),
                is_shopping_list=sw_shopping.value,
                move_to_tomorrow=sw_carry.value,
                use_time_blocking=sw_block.value,
                use_pomodoro=sw_pomodoro.value,
                use_timer=sw_timer.value,
                use_alarm=sw_alarm.value,
                notification_type=notif_dd.value or "both",
                planned_date=planned_iso,
                time_block_start=start if sw_block.value else "",
                time_block_duration=duration if sw_block.value else 0,
                time_block_days=days,
                time_block_dates=dates,
                alarm_time=alarm_time_value,
                recurrence=recurrence_dd.value or "none",
                subtasks=subtasks_list,
                auto_complete_on_subtasks=sw_auto_complete.value if sw_subtasks.value else False,
                estimated_minutes=est_minutes,
                reminder_minutes=reminder_min,
            )

            if task:
                for k, v in data.items():
                    setattr(task, k, v)
                task.shopping_items = list(working_items) if sw_shopping.value else []
                maybe_autocomplete(task)
                tm.update(task)
            else:
                new_task = Task(id=str(uuid.uuid4()), **data)
                new_task.shopping_items = list(working_items) if sw_shopping.value else []
                if new_task.recurrence != "none" and not new_task.series_id:
                    new_task.series_id = str(uuid.uuid4())
                maybe_autocomplete(new_task)
                tm.add(new_task)

            if tm.last_save_error:
                toast(tm.last_save_error, error=True)
                tm.last_save_error = None
            close_dlg()
            render_tasks()

        dlg = ft.AlertDialog(
            modal=True,
            title=ft.Text("Редактирование задачи" if task else "Новая задача"),
            content=ft.Container(width=700, padding=10, content=ft.Column([
                ft.Text("Основное", weight=ft.FontWeight.BOLD, size=14,
                        color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)),
                title_field,
                ft.Row([folder_dd, date_field, recurrence_dd], spacing=10, wrap=True),
                ft.Row([est_field, reminder_dd], spacing=10),
                ft.Divider(),
                ft.Text("Параметры задачи", weight=ft.FontWeight.BOLD, size=14,
                        color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)),
                sw_shopping, shopping_block, sw_carry, sw_subtasks, subtasks_block,
                ft.Divider(),
                ft.Text("Таймеры и будильник", weight=ft.FontWeight.BOLD, size=14,
                        color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)),
                sw_pomodoro, pomodoro_settings_block, sw_timer, timer_settings_block,
                sw_alarm, alarm_settings_block, notif_dd,
                ft.Divider(),
                ft.Text("Time blocking", weight=ft.FontWeight.BOLD, size=14,
                        color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)),
                sw_block, time_blocking_fields,
            ], spacing=8, scroll=ft.ScrollMode.AUTO)),
            actions=[ft.TextButton("Отмена", on_click=close_dlg),
                     ft.ElevatedButton("Сохранить", icon=ft.Icons.CHECK, on_click=save_task)],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg, save_task)
        refresh_shopping_view()
        refresh_subtasks_view()
        page.open(dlg)
        page.update()

    # Карточка задачи
    def open_task_card(task: Task):
        comment_field = ft.TextField(label="Комментарии", multiline=True, min_lines=3, max_lines=8,
                                     value=task.comment or "", expand=True)
        info_section = ft.Column([
            ft.Row([ft.Icon(ft.Icons.FOLDER_OUTLINED, size=16, color=ft.Colors.GREY_700),
                    ft.Text(f"Папка: {task.folder}", size=13)], spacing=4),
            ft.Row([ft.Icon(ft.Icons.CALENDAR_TODAY, size=16, color=ft.Colors.GREY_700),
                    ft.Text(f"Дата: {format_date_display_ru(task.planned_date)}", size=13)], spacing=4),
            ft.Row([ft.Icon(ft.Icons.CHECK_CIRCLE_OUTLINE if task.completed else ft.Icons.RADIO_BUTTON_UNCHECKED,
                            size=16, color=ft.Colors.GREEN_700 if task.completed else ft.Colors.GREY_700),
                    ft.Text("Выполнено" if task.completed else "Не выполнено", size=13)], spacing=4),
            *([ft.Row([ft.Icon(ft.Icons.ALARM, size=16, color=ft.Colors.ORANGE_700),
                       ft.Text(f"Будильник: {task.alarm_time}", size=13, color=ft.Colors.ORANGE_700)], spacing=4)]
              if task.use_alarm and task.alarm_time else []),
            *([ft.Row([ft.Icon(ft.Icons.REPEAT, size=16, color=ft.Colors.PURPLE_700),
                       ft.Text(f"Повторение: {RECURRENCE_RU.get(task.recurrence)}",
                               size=13, color=ft.Colors.PURPLE_700)], spacing=4)]
              if task.recurrence != "none" else []),
            *([ft.Row([ft.Icon(ft.Icons.ACCESS_TIME, size=16, color=ft.Colors.RED_600),
                       ft.Text(f"Завершено циклов: {task.completed_cycles}", size=13,
                               color=ft.Colors.RED_600)], spacing=4)]
              if task.completed_cycles > 0 else []),
            *([ft.Row([ft.Icon(ft.Icons.CALENDAR_TODAY, size=16, color=ft.Colors.TEAL_700),
                       ft.Text(f"Блок: {task.time_block_start} (+{task.time_block_duration} мин)"
                               + (f" [{', '.join(DAY_RU.get(d, d) for d in task.time_block_days)}]"
                                  if task.time_block_days else ""),
                               size=13, color=ft.Colors.TEAL_700)], spacing=4)]
              if task.use_time_blocking and task.time_block_start else []),
            *([ft.Row([ft.Icon(ft.Icons.EVENT, size=16, color=ft.Colors.TEAL_700),
                       ft.Text("Даты: " + ", ".join(format_date_display_ru(d)
                                                    for d in task.time_block_dates),
                               size=13, color=ft.Colors.TEAL_700)], spacing=4)]
              if task.use_time_blocking and task.time_block_dates else []),
            *([ft.Row([ft.Icon(ft.Icons.ARROW_FORWARD, size=16, color=ft.Colors.PURPLE_700),
                       ft.Text("Переносится на следующий день, пока не выполнена", size=13,
                               color=ft.Colors.PURPLE_700)], spacing=4)]
              if task.move_to_tomorrow else []),
            *([ft.Row([ft.Icon(ft.Icons.ACCESS_TIME, size=16, color=ft.Colors.BLUE_700),
                       ft.Text(f"Оценка: {task.estimated_minutes} мин", size=13,
                               color=ft.Colors.BLUE_700)], spacing=4)]
              if task.estimated_minutes > 0 else []),
            *([ft.Row([ft.Icon(ft.Icons.NOTIFICATIONS, size=16, color=ft.Colors.AMBER_700),
                       ft.Text(f"Напоминание за {task.reminder_minutes} мин", size=13,
                               color=ft.Colors.AMBER_700)], spacing=4)]
              if task.reminder_minutes > 0 else []),
        ], spacing=4)

        # Подзадачи в карточке
        subtasks_section = ft.Container(visible=False)
        sub_progress_text = ft.Text("", size=13, weight=ft.FontWeight.BOLD, color=ft.Colors.TEAL_700)
        sub_progress_bar = ft.ProgressBar(value=0, color=ft.Colors.GREEN_600, bgcolor=ft.Colors.GREY_300)
        sub_list = ft.Column(spacing=2)

        def refresh_sub_progress():
            done = sum(1 for s in task.subtasks if s.completed)
            total = len(task.subtasks)
            sub_progress_text.value = f"📋 Подзадачи: {done}/{total}"
            sub_progress_bar.value = (done / total) if total else 0
            try:
                sub_progress_text.update()
                sub_progress_bar.update()
            except Exception:
                pass

        def rebuild_subtasks():
            sub_list.controls.clear()
            for sub in task.subtasks:
                def make_handler(s):
                    def handler(e):
                        s.completed = bool(e.control.value)
                        maybe_autocomplete(task)
                        tm.update(task)
                        refresh_sub_progress()
                        rebuild_subtasks()
                        render_tasks()
                    return handler

                def make_edit_handler(s):
                    def handler(e):
                        edit_field = ft.TextField(value=s.title, width=300)
                        def do_save(ev):
                            s.title = (edit_field.value or "").strip() or s.title
                            tm.update(task)
                            page.close(edit_dlg)
                            page.update()
                            rebuild_subtasks()
                        edit_dlg = ft.AlertDialog(
                            modal=True, title=ft.Text("Редактировать подзадачу"),
                            content=edit_field,
                            actions=[ft.TextButton("Отмена", on_click=lambda e: page.close(edit_dlg)),
                                     ft.ElevatedButton("Сохранить", on_click=do_save)],
                            actions_alignment=ft.MainAxisAlignment.END)
                        page.open(edit_dlg)
                        page.update()
                    return handler

                def make_delete_handler(s):
                    def handler(e):
                        task.subtasks = [x for x in task.subtasks if x.id != s.id]
                        tm.update(task)
                        rebuild_subtasks()
                        refresh_sub_progress()
                        render_tasks()
                    return handler

                cb = ft.Checkbox(value=sub.completed, on_change=make_handler(sub))
                sub_list.controls.append(ft.Row([
                    cb,
                    ft.Text(sub.title, size=13, expand=True,
                            color=ft.Colors.GREY_500 if sub.completed else None,
                            style=ft.TextStyle(
                                decoration=ft.TextDecoration.LINE_THROUGH if sub.completed else None)),
                    ft.IconButton(ft.Icons.EDIT, icon_size=14, icon_color=ft.Colors.BLUE_400,
                                  on_click=make_edit_handler(sub), tooltip="Редактировать"),
                    ft.IconButton(ft.Icons.DELETE_OUTLINE, icon_size=14, icon_color=ft.Colors.RED_400,
                                  on_click=make_delete_handler(sub), tooltip="Удалить"),
                ], spacing=2))
            refresh_sub_progress()
            try:
                sub_list.update()
            except Exception:
                pass

        if task.subtasks:
            subtasks_section.visible = True
            subtasks_section.content = ft.Column([
                ft.Divider(), sub_progress_text, sub_progress_bar, sub_list,
            ], spacing=6)
            rebuild_subtasks()

        # Покупки
        shopping_section = ft.Container(visible=False)
        items_list_view = ft.Column(spacing=6)
        total_text = ft.Text("Итого: 0,00 ₽", size=18, weight=ft.FontWeight.BOLD, color=ft.Colors.GREEN_800)
        items_count_text = ft.Text("", size=12, color=ft.Colors.GREY_600)
        item_refs = {}

        def recalculate():
            grand_total = 0.0
            for item in task.shopping_items:
                refs = item_refs.get(item.id)
                if not refs:
                    continue
                qty = parse_positive_float(refs["qty_field"].value, item.quantity)
                price = parse_positive_float(refs["price_field"].value, item.price)
                item.quantity = qty
                item.price = price
                grand_total += qty * price
                refs["sum_text"].value = f"{fmt_money(qty * price)} ₽"
            total_text.value = f"Итого: {fmt_money(grand_total)} ₽"
            items_count_text.value = (f"Товаров: {len(task.shopping_items)} · "
                                      f"Куплено: {sum(1 for x in task.shopping_items if x.bought)}")

        def make_qty_handler(item_id):
            def handler(e):
                recalculate()
                tm.update(task)
                try:
                    total_text.update()
                    items_count_text.update()
                except Exception:
                    pass
            return handler

        def rebuild_items_list():
            items_list_view.controls.clear()
            item_refs.clear()
            if not task.shopping_items:
                items_list_view.controls.append(ft.Text("Список пуст. Добавьте товары через «+»",
                                                         size=13, color=ft.Colors.GREY_500, italic=True))
                recalculate()
                try:
                    items_list_view.update()
                    total_text.update()
                    items_count_text.update()
                except Exception:
                    pass
                return
            items_list_view.controls.append(ft.Container(
                bgcolor=pal(ft.Colors.GREY_100, ft.Colors.GREY_800), border_radius=6,
                padding=ft.padding.symmetric(horizontal=8, vertical=4),
                content=ft.Row([
                    ft.Text("", width=30),
                    ft.Text("Товар", expand=True, weight=ft.FontWeight.BOLD, size=13),
                    ft.Text("Кол-во", width=80, weight=ft.FontWeight.BOLD, size=13),
                    ft.Text("Цена", width=100, weight=ft.FontWeight.BOLD, size=13),
                    ft.Text("Сумма", width=90, weight=ft.FontWeight.BOLD, size=13),
                    ft.Text("", width=30),
                ], vertical_alignment=ft.CrossAxisAlignment.CENTER)))
            for item in task.shopping_items:
                qty_field = ft.TextField(
                    value=(str(item.quantity) if item.quantity != int(item.quantity)
                           else str(int(item.quantity))),
                    width=80, dense=True, text_size=13, keyboard_type=ft.KeyboardType.NUMBER,
                    content_padding=ft.padding.symmetric(horizontal=6, vertical=2))
                price_field = ft.TextField(
                    value=(str(item.price) if item.price != int(item.price)
                           else str(int(item.price))),
                    width=100, dense=True, text_size=13, keyboard_type=ft.KeyboardType.NUMBER,
                    content_padding=ft.padding.symmetric(horizontal=6, vertical=2))
                sum_text = ft.Text(f"{fmt_money(item.quantity * item.price)} ₽", width=90, size=13,
                                    weight=ft.FontWeight.BOLD,
                                    color=pal(ft.Colors.BLUE_800, ft.Colors.BLUE_200))
                checkbox = ft.Checkbox(value=item.bought)

                def make_checkbox_handler(it):
                    def handler(e):
                        it.bought = bool(e.control.value)
                        tm.update(task)
                        recalculate()
                        rebuild_items_list()
                        render_tasks()
                    return handler

                def make_delete_handler(it):
                    def handler(e):
                        task.shopping_items = [x for x in task.shopping_items if x.id != it.id]
                        tm.update(task)
                        rebuild_items_list()
                        render_tasks()
                    return handler

                def make_edit_handler(it):
                    def handler(e):
                        edit_field = ft.TextField(value=it.title, width=300)
                        def do_save(ev):
                            it.title = (edit_field.value or "").strip() or it.title
                            tm.update(task)
                            page.close(edit_dlg)
                            page.update()
                            rebuild_items_list()
                            render_tasks()
                        edit_dlg = ft.AlertDialog(
                            modal=True, title=ft.Text("Редактировать товар"),
                            content=edit_field,
                            actions=[ft.TextButton("Отмена", on_click=lambda e: page.close(edit_dlg)),
                                     ft.ElevatedButton("Сохранить", on_click=do_save)],
                            actions_alignment=ft.MainAxisAlignment.END)
                        page.open(edit_dlg)
                        page.update()
                    return handler

                qty_field.on_change = make_qty_handler(item.id)
                price_field.on_change = make_qty_handler(item.id)
                checkbox.on_change = make_checkbox_handler(item)
                item_refs[item.id] = {"qty_field": qty_field, "price_field": price_field, "sum_text": sum_text}
                items_list_view.controls.append(ft.Container(
                    border=ft.border.all(1, ft.Colors.GREY_300), border_radius=6,
                    padding=ft.padding.symmetric(horizontal=8, vertical=4),
                    content=ft.Row([
                        checkbox,
                        ft.Text(item.title, expand=True, size=13,
                                color=ft.Colors.GREY_500 if item.bought else None),
                        qty_field, price_field, sum_text,
                        ft.IconButton(ft.Icons.EDIT, icon_size=14, icon_color=ft.Colors.BLUE_400,
                                      on_click=make_edit_handler(item), tooltip="Редактировать"),
                        ft.IconButton(ft.Icons.DELETE_OUTLINE, icon_size=14, icon_color=ft.Colors.RED_400,
                                      on_click=make_delete_handler(item)),
                    ], vertical_alignment=ft.CrossAxisAlignment.CENTER)))
            recalculate()
            try:
                items_list_view.update()
                total_text.update()
                items_count_text.update()
            except Exception:
                pass

        new_item_field = ft.TextField(label="Новый товар", expand=True, dense=True)

        def add_item(e):
            t = (new_item_field.value or "").strip()
            if not t:
                return
            task.shopping_items.append(ShoppingItem(id=str(uuid.uuid4()), title=t, quantity=1, price=0))
            tm.update(task)
            new_item_field.value = ""
            rebuild_items_list()
            render_tasks()
            try:
                new_item_field.focus()
            except Exception:
                pass
        new_item_field.on_submit = add_item

        def clear_bought(e):
            task.shopping_items = [x for x in task.shopping_items if not x.bought]
            tm.update(task)
            rebuild_items_list()
            render_tasks()
            toast("Купленные товары удалены")

        def copy_list(e):
            lines = [f"🛒 {task.title}"]
            for it in task.shopping_items:
                mark = "☑" if it.bought else "☐"
                qty = (str(int(it.quantity)) if it.quantity == int(it.quantity) else str(it.quantity))
                lines.append(f"{mark} {it.title} — {qty}")
            text = "\n".join(lines)
            try:
                page.set_clipboard(text)
                toast("Список скопирован в буфер обмена")
            except Exception:
                toast("Не удалось скопировать", error=True)

        if task.is_shopping_list:
            shopping_section.visible = True
            shopping_section.content = ft.Column([
                ft.Divider(),
                ft.Row([ft.Text("🛒 Список покупок", weight=ft.FontWeight.BOLD, size=15,
                                 color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)),
                        ft.Row([ft.IconButton(ft.Icons.COPY_ALL, icon_size=18,
                                              tooltip="Скопировать список", on_click=copy_list),
                                ft.IconButton(ft.Icons.CLEAR_ALL, icon_size=18,
                                              icon_color=ft.Colors.ORANGE_700,
                                              tooltip="Удалить купленные", on_click=clear_bought)],
                               spacing=0)], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                items_list_view,
                ft.Row([new_item_field,
                        ft.IconButton(ft.Icons.ADD_CIRCLE, icon_color=ft.Colors.GREEN,
                                      on_click=add_item, tooltip="Добавить товар")]),
                ft.Divider(),
                ft.Row([items_count_text, total_text], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            ], spacing=8)
            rebuild_items_list()

        def save_and_close(e=None):
            task.comment = (comment_field.value or "").strip()
            maybe_autocomplete(task)
            tm.update(task)
            unregister_dialog()
            page.close(dlg)
            page.update()
            render_tasks()
            toast("Изменения сохранены")

        def just_close(e=None):
            task.comment = (comment_field.value or "").strip()
            tm.update(task)
            unregister_dialog()
            page.close(dlg)
            page.update()
            render_tasks()

        def open_full_editor(e):
            unregister_dialog()
            page.close(dlg)
            page.update()
            open_editor(task)

        dlg = ft.AlertDialog(
            modal=True,
            title=ft.Row([ft.Text(task.title, size=18, weight=ft.FontWeight.BOLD, expand=True),
                           ft.IconButton(ft.Icons.EDIT, tooltip="Редактировать параметры",
                                          on_click=open_full_editor)]),
            content=ft.Container(width=720, padding=10, content=ft.Column([
                info_section, subtasks_section, ft.Divider(),
                ft.Text("💬 Комментарии", weight=ft.FontWeight.BOLD, size=14,
                        color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)),
                comment_field, shopping_section,
            ], spacing=8, scroll=ft.ScrollMode.AUTO)),
            actions=[ft.TextButton("Закрыть", on_click=just_close),
                     ft.ElevatedButton("Сохранить", icon=ft.Icons.CHECK, on_click=save_and_close)],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg, save_and_close)
        page.open(dlg)
        page.update()

    # Настройки
    def show_settings(e=None):
        s = tm.settings
        tf_work = ft.TextField(label="Работа, мин", value=str(s.pomodoro_work),
                                keyboard_type=ft.KeyboardType.NUMBER, width=150)
        tf_break = ft.TextField(label="Короткий перерыв, мин", value=str(s.pomodoro_break),
                                 keyboard_type=ft.KeyboardType.NUMBER, width=180)
        tf_long = ft.TextField(label="Длинный перерыв, мин", value=str(s.pomodoro_long_break),
                                keyboard_type=ft.KeyboardType.NUMBER, width=180)
        tf_cycles = ft.TextField(label="Циклов до длинного", value=str(s.pomodoro_cycles),
                                  keyboard_type=ft.KeyboardType.NUMBER, width=170)
        tf_regular = ft.TextField(label="Обычный таймер, мин", value=str(s.regular_timer_minutes),
                                   keyboard_type=ft.KeyboardType.NUMBER, width=180)
        sw_long = ft.Switch(label="Использовать длинный перерыв", value=s.long_break_enabled)
        sw_auto = ft.Switch(label="Автопереход между фазами", value=s.auto_continue)
        sw_theme = ft.Switch(label="🌙 Тёмная тема", value=(s.theme_mode == "dark"))
        sw_theme_sched = ft.Switch(label="🕒 Тёмная тема по расписанию",
                                   value=s.dark_theme_schedule_enabled)
        tf_sched_start = ft.TextField(label="Начало (ЧЧ:ММ)", width=140,
                                      value=s.dark_theme_schedule_start)
        tf_sched_end = ft.TextField(label="Конец (ЧЧ:ММ)", width=140,
                                    value=s.dark_theme_schedule_end)
        sw_tray = ft.Switch(label="🗕 Свёртывать в трей при закрытии",
                            value=s.minimize_to_tray, disabled=not PYSTRAY_AVAILABLE)
        sw_title = ft.Switch(label="🏃 Показывать таймеры в заголовке", value=s.show_in_title)
        volume_slider = ft.Slider(min=0, max=1, divisions=20, value=s.volume,
                                  label="{value}", width=300)
        volume_preview_btn = ft.IconButton(ft.Icons.VOLUME_UP, tooltip="Проверить звук",
                                            on_click=lambda e: threading.Thread(
                                                target=play_notification_sound,
                                                args=(volume_slider.value,), daemon=True).start())
        err = ft.Text("", color=ft.Colors.RED, size=12)

        def _validate_int(field_obj, name, default, max_val):
            raw = (field_obj.value or "").strip()
            if not raw:
                return default
            if not raw.isdigit():
                raise ValueError(f"{name}: должно быть целым числом")
            v = int(raw)
            if v <= 0:
                raise ValueError(f"{name}: должно быть больше нуля")
            if v > max_val:
                raise ValueError(f"{name}: не больше {max_val}")
            return v

        def do_save(e=None):
            try:
                new_work = _validate_int(tf_work, "Работа", 25, 999)
                new_break = _validate_int(tf_break, "Короткий перерыв", 5, 999)
                new_long = _validate_int(tf_long, "Длинный перерыв", 15, 999)
                new_cycles = _validate_int(tf_cycles, "Циклов", 4, 1000)
                new_regular = _validate_int(tf_regular, "Обычный таймер", 15, 9999)
            except ValueError as ve:
                err.value = str(ve)
                page.update()
                return
            start_t = normalize_hhmm(tf_sched_start.value)
            end_t = normalize_hhmm(tf_sched_end.value)
            if sw_theme_sched.value:
                if not valid_hhmm(start_t) or not valid_hhmm(end_t):
                    err.value = "Расписание: формат ЧЧ:ММ"
                    page.update()
                    return

            s.pomodoro_work = new_work
            s.pomodoro_break = new_break
            s.pomodoro_long_break = new_long
            s.pomodoro_cycles = new_cycles
            s.regular_timer_minutes = new_regular
            s.long_break_enabled = sw_long.value
            s.auto_continue = sw_auto.value
            s.theme_mode = "dark" if sw_theme.value else "light"
            s.dark_theme_schedule_enabled = sw_theme_sched.value
            s.dark_theme_schedule_start = start_t if valid_hhmm(start_t) else "20:00"
            s.dark_theme_schedule_end = end_t if valid_hhmm(end_t) else "07:00"
            s.minimize_to_tray = sw_tray.value and PYSTRAY_AVAILABLE
            s.show_in_title = sw_title.value
            s.volume = max(0.0, min(1.0, float(volume_slider.value or 0.8)))
            try:
                tm.save_settings()
            except Exception as ex:
                err.value = f"Ошибка сохранения: {ex}"
                page.update()
                return
            if audio_player is not None:
                try:
                    audio_player.volume = s.volume
                except Exception:
                    pass
            page.theme_mode = (ft.ThemeMode.DARK if desired_theme_mode() == "dark"
                               else ft.ThemeMode.LIGHT)
            unregister_dialog()
            page.close(dlg)
            page.update()
            render_folders()
            render_tasks()
            render_standalone_timers()
            render_timer_banner()
            update_window_title()
            try:
                page.update()
            except Exception:
                pass
            toast("Настройки сохранены")

        def close_dlg():
            unregister_dialog()
            page.close(dlg)
            page.update()

        dlg = ft.AlertDialog(
            modal=True, title=ft.Text("Настройки"),
            content=ft.Container(width=500, content=ft.Column([
                ft.Text("Pomodoro", weight=ft.FontWeight.BOLD),
                ft.Row([tf_work, tf_break], wrap=True),
                ft.Row([tf_long, tf_cycles], wrap=True),
                sw_long, sw_auto,
                ft.Divider(),
                ft.Text("Обычный таймер", weight=ft.FontWeight.BOLD),
                tf_regular,
                ft.Divider(),
                ft.Text("Внешний вид", weight=ft.FontWeight.BOLD),
                sw_theme, sw_theme_sched,
                ft.Row([tf_sched_start, tf_sched_end], spacing=8),
                sw_tray, sw_title,
                ft.Divider(),
                ft.Text("🔊 Звук", weight=ft.FontWeight.BOLD),
                ft.Row([volume_slider, volume_preview_btn],
                       alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                err,
            ], spacing=12, scroll=ft.ScrollMode.AUTO)),
            actions=[ft.TextButton("Сохранить", on_click=do_save),
                     ft.TextButton("Отмена", on_click=lambda e: close_dlg())],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg, do_save)
        page.open(dlg)
        page.update()

    # Папки
    folders_view = ft.Column(spacing=2, scroll=ft.ScrollMode.AUTO, expand=True)
    new_folder_field = ft.TextField(label="Новая папка", dense=True)

    def select_folder(name: str):
        nonlocal current_folder
        current_folder = name
        render_folders()
        render_tasks()

    def add_folder(e):
        name = (new_folder_field.value or "").strip()
        if not name:
            return
        if tm.add_folder(name):
            new_folder_field.value = ""
            select_folder(name)
        else:
            toast("Папка с таким именем уже есть", error=True)

    def edit_folder_dialog(folder: FolderInfo):
        name_f = ft.TextField(label="Название", value=folder.name, width=300)
        color_dd = ft.Dropdown(label="Цвет", width=200, value=folder.color,
                               options=[ft.dropdown.Option(c, ft.Text("●", color=c))
                                        for c in FOLDER_COLORS])
        icon_dd = ft.Dropdown(label="Иконка", width=200, value=folder.icon,
                              options=[ft.dropdown.Option(i, ft.Icon(i)) for i in FOLDER_ICONS])
        err = ft.Text("", color=ft.Colors.RED, size=12)

        def do_save(e):
            new_name = (name_f.value or "").strip()
            if not new_name or new_name == "Все":
                err.value = "Некорректное имя"
                page.update()
                return
            if not tm.update_folder(folder.name, new_name, color_dd.value, icon_dd.value):
                err.value = "Ошибка обновления"
                page.update()
                return
            unregister_dialog()
            page.close(dlg)
            page.update()
            if current_folder == folder.name:
                select_folder(new_name)
            else:
                render_folders()
                render_tasks()

        def close():
            unregister_dialog()
            page.close(dlg)
            page.update()

        dlg = ft.AlertDialog(
            modal=True, title=ft.Text("Редактировать папку"),
            content=ft.Container(width=400, content=ft.Column([name_f, color_dd, icon_dd, err], spacing=8)),
            actions=[ft.TextButton("Сохранить", on_click=do_save),
                     ft.TextButton("Отмена", on_click=lambda e: close())],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg, do_save)
        page.open(dlg)
        page.update()

    def rename_folder_dialog(name: str):
        folder = tm.get_folder_info(name)
        if folder:
            edit_folder_dialog(folder)
        else:
            toast("Папка не найдена", error=True)

    def delete_folder_dialog(name: str):
        count = sum(1 for t in tm.tasks if t.folder == name)
        timer_task_id = timer_state.task_id

        def do_delete(e):
            tm.delete_folder(name)
            unregister_dialog()
            page.close(dlg)
            page.update()
            if timer_task_id and not any(t.id == timer_task_id for t in tm.tasks):
                timer_state.stop()
            select_folder("Все")

        def close():
            unregister_dialog()
            page.close(dlg)
            page.update()

        dlg = ft.AlertDialog(
            modal=True, title=ft.Text(f"Удалить папку «{name}»?"),
            content=ft.Text(f"Вместе с папкой будет удалено задач: {count}"),
            actions=[ft.TextButton("Удалить", style=ft.ButtonStyle(color=ft.Colors.RED), on_click=do_delete),
                     ft.TextButton("Отмена", on_click=lambda e: close())],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg, do_delete)
        page.open(dlg)
        page.update()

    def render_folders():
        controls = []
        for folder in tm.folders:
            trailing = ft.Row([
                ft.IconButton(ft.Icons.EDIT, icon_size=16, tooltip="Редактировать",
                              on_click=lambda e, f=folder: edit_folder_dialog(f)),
                ft.IconButton(ft.Icons.DELETE, icon_size=16, tooltip="Удалить",
                              icon_color=ft.Colors.RED_400,
                              on_click=lambda e, n=folder.name: delete_folder_dialog(n)),
            ], spacing=0, tight=True)
            controls.append(ft.ListTile(
                leading=ft.Icon(folder.icon, size=20, color=folder.color),
                title=ft.Text(folder.name, size=14,
                              weight=ft.FontWeight.BOLD if folder.name == current_folder else None),
                selected=(folder.name == current_folder), dense=True, trailing=trailing,
                on_click=lambda e, n=folder.name: select_folder(n)))
        folders_view.controls = controls
        try:
            page.update()
        except Exception:
            pass

    # Список задач
    tasks_view = ft.ListView(expand=True, spacing=8)
    header = ft.Text("Задачи", size=20, weight=ft.FontWeight.BOLD)
    save_status = ft.Text("", size=12, color=ft.Colors.GREY_500)

    def maybe_autocomplete(task: Task):
        """FIX: проверяет next_iteration_created."""
        if not task.auto_complete_on_subtasks or not task.subtasks:
            return
        if all(s.completed for s in task.subtasks) and not task.completed:
            task.completed = True
            task.completed_at = datetime.now().isoformat()
            if task.recurrence != "none" and not task.next_iteration_created:
                nxt = tm.create_next_recurrence(task)
                if nxt:
                    tm.add(nxt)
                    toast(f"🔁 Создана следующая итерация: {nxt.title}")

    def toggle_task(task: Task, value: bool):
        was_completed = task.completed
        task.completed = bool(value)
        if task.completed and not was_completed:
            task.completed_at = datetime.now().isoformat()
            if task.recurrence != "none" and not task.next_iteration_created:
                nxt = tm.create_next_recurrence(task)
                if nxt:
                    tm.add(nxt)
                    toast(f"🔁 Создана следующая итерация: {nxt.title}")
        elif not task.completed and was_completed:
            task.completed_at = ""
            task.next_iteration_created = False
        tm.update(task)
        if tm.last_save_error:
            toast(tm.last_save_error, error=True)
            tm.last_save_error = None
        render_tasks()

    def delete_task(task: Task):
        if timer_state.task_id == task.id:
            timer_state.stop()
            render_timer_banner()
        tm.delete(task.id)
        if tm.last_save_error:
            toast(tm.last_save_error, error=True)
            tm.last_save_error = None
        render_tasks()

    def start_timer(task: Task, timer_type: str):
        if timer_state.is_running or timer_state.paused:
            toast("Сначала остановите текущий таймер", error=True)
            return
        s = tm.settings
        secs = (s.pomodoro_work if timer_type == "pomodoro" else s.regular_timer_minutes) * 60
        timer_state.start(secs, "work", timer_type, task.id)
        render_timer_banner()
        render_tasks()
        update_window_title()

    def toggle_shopping_item(task: Task, item_id: str, value: bool,
                              cb_ctrl=None, text_ctrl=None, counter_ctrl=None):
        for item in task.shopping_items:
            if item.id == item_id:
                item.bought = bool(value)
                break
        tm.update(task)
        if tm.last_save_error:
            toast(tm.last_save_error, error=True)
            tm.last_save_error = None
        if text_ctrl is not None:
            text_ctrl.color = ft.Colors.GREY_500 if value else None
            try:
                text_ctrl.update()
            except Exception:
                pass
        if counter_ctrl is not None:
            bought = sum(1 for x in task.shopping_items if x.bought)
            counter_ctrl.value = f"🛒 Куплено: {bought}/{len(task.shopping_items)}"
            try:
                counter_ctrl.update()
            except Exception:
                pass

    def _make_item_on_change(task_obj, item_obj, text_ctrl, counter_ctrl):
        def on_change(e):
            toggle_shopping_item(task_obj, item_obj.id, e.control.value,
                                  cb_ctrl=e.control, text_ctrl=text_ctrl,
                                  counter_ctrl=counter_ctrl)
        return on_change

    def quick_add_item_dialog(task: Task):
        tf = ft.TextField(label="Название товара", autofocus=True)

        def do_add(e):
            title = (tf.value or "").strip()
            if title:
                task.shopping_items.append(ShoppingItem(id=str(uuid.uuid4()), title=title))
                tm.update(task)
            unregister_dialog()
            page.close(dlg)
            page.update()
            render_tasks()

        def do_cancel(e):
            unregister_dialog()
            page.close(dlg)
            page.update()

        tf.on_submit = do_add
        dlg = ft.AlertDialog(
            modal=True, title=ft.Text(f"Добавить в «{task.title}»"),
            content=ft.Container(width=350, content=tf),
            actions=[ft.TextButton("Отмена", on_click=do_cancel),
                     ft.ElevatedButton("Добавить", icon=ft.Icons.ADD, on_click=do_add)],
            actions_alignment=ft.MainAxisAlignment.END)
        register_dialog(dlg, do_add)
        page.open(dlg)
        page.update()

    def set_view(view: str):
        nonlocal current_view
        current_view = view
        render_tasks()

    def render_tasks():
        if current_view == "shopping":
            header.value = "🛒 Списки покупок"
        elif current_view == "tasks":
            header.value = "📋 Все задачи"
        else:
            header.value = f"Задачи — {current_folder}"
        if current_view == "shopping":
            tasks = [t for t in tm.tasks if t.is_shopping_list]
            if current_folder != "Все":
                tasks = [t for t in tasks if t.folder == current_folder]
        elif current_view == "tasks":
            tasks = [t for t in tm.tasks if not t.is_shopping_list]
            if current_folder != "Все":
                tasks = [t for t in tasks if t.folder == current_folder]
        else:
            tasks = (tm.tasks if current_folder == "Все"
                     else [t for t in tm.tasks if t.folder == current_folder])
        tasks = sorted(tasks, key=lambda t: (t.completed, t.planned_date,
                                               t.time_block_start or "99:99", t.title.lower()))
        tasks_view.controls.clear()
        if not tasks:
            tasks_view.controls.append(ft.Text("Пока пусто", color=ft.Colors.GREY_500))
        busy = timer_state.is_running or timer_state.paused
        today_iso = date.today().isoformat()
        now_dt = datetime.now()

        for t in tasks:
            badges = []
            is_carried = (t.move_to_tomorrow and not t.completed and t.planned_date != today_iso)
            if is_carried:
                badges.append(ft.Text("🔄", size=14, tooltip="Задача перенесена"))
            for flag, icon, color in (
                    (t.move_to_tomorrow and not is_carried, ft.Icons.ARROW_FORWARD, ft.Colors.ORANGE),
                    (t.use_time_blocking, ft.Icons.CALENDAR_TODAY, ft.Colors.GREEN),
                    (t.use_pomodoro, ft.Icons.ACCESS_TIME, ft.Colors.RED),  # FIX: ACCESS_TIME
                    (t.use_timer, ft.Icons.HOURGLASS_EMPTY, ft.Colors.PURPLE),
                    (t.use_alarm, ft.Icons.ALARM, ft.Colors.ORANGE_700)):
                if flag:
                    badges.append(ft.Icon(icon, size=16, color=color))
            if t.use_alarm and t.alarm_time:
                badges.append(ft.Text(f"⏰ {t.alarm_time}", size=12, color=ft.Colors.ORANGE_700,
                                      weight=ft.FontWeight.BOLD))
            if t.recurrence != "none":
                badges.append(ft.Text(f"🔁 {RECURRENCE_RU.get(t.recurrence, '')}", size=12,
                                      color=ft.Colors.PURPLE_700, tooltip="Повторяющаяся задача"))
            if t.completed_cycles > 0:
                badges.append(ft.Text(f"🍅×{t.completed_cycles}", size=11, color=ft.Colors.RED_600,
                                      tooltip="Завершено циклов"))
            if t.subtasks:
                done_s = sum(1 for s in t.subtasks if s.completed)
                badges.append(ft.Text(f"📋 {done_s}/{len(t.subtasks)}", size=11, color=ft.Colors.TEAL_700))
            if t.estimated_minutes > 0:
                badges.append(ft.Text(f"⏱ {t.estimated_minutes}м", size=11, color=ft.Colors.BLUE_700))
            if t.use_time_blocking and (t.time_block_start or t.time_block_duration
                                         or t.time_block_days or t.time_block_dates):
                parts = ["📅"]
                if t.time_block_start:
                    parts.append(t.time_block_start)
                if t.time_block_duration:
                    parts.append(f"({t.time_block_duration} мин)")
                if t.time_block_days:
                    parts.append("[" + ", ".join(DAY_RU.get(d, d) for d in t.time_block_days) + "]")
                if t.time_block_dates:
                    parts.append("{" + ", ".join(format_date_display_ru(d) for d in t.time_block_dates) + "}")
                status = block_status(t, now_dt)
                color = ft.Colors.TEAL_700
                if status:
                    if status["state"] == "active":
                        parts.append(f"🟢 идёт, {max(1, status['seconds_left'] // 60)} мин")
                        color = ft.Colors.GREEN_700
                    elif status["state"] == "upcoming":
                        secs = status["seconds_until"]
                        if secs < 3600:
                            parts.append(f"⏱ через {max(1, secs // 60)} мин")
                        else:
                            parts.append(f"⏱ через {secs // 3600}ч {(secs % 3600) // 60}м")
                        color = ft.Colors.BLUE_700
                    else:
                        parts.append("✔ прошёл")
                        color = ft.Colors.GREY_600
                badges.append(ft.Text(" ".join(parts), size=12, color=color))
            badges.append(ft.Text({"sound": "🔊", "popup": "💬", "both": "🔊💬", "none": "🔇"}.get(
                t.notification_type, "🔇"), size=13, tooltip=f"Уведомление: {t.notification_type}"))
            badges.append(ft.Text(format_date_display_ru(t.planned_date) or t.planned_date,
                                   size=12, color=ft.Colors.GREY_600))
            is_this = (timer_state.task_id == t.id and (timer_state.is_running or timer_state.paused))
            if is_this:
                badges.append(ft.Text(f"⏳ {fmt_time(timer_state.time_left)}", size=13,
                                      weight=ft.FontWeight.BOLD,
                                      color=pal(ft.Colors.BLUE_700, ft.Colors.BLUE_200)))

            shopping_section = None
            if t.is_shopping_list:
                total = len(t.shopping_items)
                bought = sum(1 for x in t.shopping_items if x.bought)
                grand_total = sum(x.quantity * x.price for x in t.shopping_items)
                if grand_total > 0:
                    badges.append(ft.Text(f"💰 {fmt_money(grand_total)} ₽", size=13,
                                          weight=ft.FontWeight.BOLD, color=ft.Colors.GREEN_800))
                counter_text = ft.Text(f"🛒 Куплено: {bought}/{total}", weight=ft.FontWeight.BOLD,
                                        size=13, color=pal(ft.Colors.AMBER_900, ft.Colors.AMBER_200))
                items_controls = []
                for item in t.shopping_items[:5]:
                    item_text = ft.Text(item.title, size=13,
                                         color=ft.Colors.GREY_500 if item.bought else None)
                    item_cb = ft.Checkbox(value=item.bought)
                    item_cb.on_change = _make_item_on_change(t, item, item_text, counter_text)
                    items_controls.append(ft.Container(
                        content=ft.Row([item_cb, item_text], tight=True, spacing=0),
                        padding=ft.padding.only(left=20)))
                if total > 5:
                    items_controls.append(ft.Text(f"... и ещё {total - 5} товаров", size=12,
                                                    color=ft.Colors.GREY_500, italic=True))
                shopping_section = ft.Container(
                    padding=ft.padding.only(left=10, top=5, bottom=5),
                    bgcolor=pal(ft.Colors.AMBER_50, ft.Colors.AMBER_900), border_radius=8,
                    content=ft.Column([
                        ft.Row([counter_text,
                                 ft.Row([ft.IconButton(ft.Icons.ADD_CIRCLE_OUTLINE, icon_size=18,
                                                        icon_color=ft.Colors.GREEN_700,
                                                        tooltip="Добавить товар",
                                                        on_click=lambda e, task=t: quick_add_item_dialog(task)),
                                         ft.IconButton(ft.Icons.INFO_OUTLINE, icon_size=18,
                                                        icon_color=ft.Colors.BLUE_700,
                                                        tooltip="Открыть карточку",
                                                        on_click=lambda e, task=t: open_task_card(task))],
                                        spacing=0, tight=True)],
                                alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                        *items_controls,
                    ], spacing=2, tight=True))

            folder_info = tm.get_folder_info(t.folder)
            folder_icon = folder_info.icon if folder_info else ft.Icons.FOLDER
            folder_color = folder_info.color if folder_info else ft.Colors.GREY_600

            card_content = [
                ft.Checkbox(value=t.completed,
                            on_change=lambda e, task=t: toggle_task(task, e.control.value)),
                ft.Column([
                    ft.Row([ft.Icon(folder_icon, size=14, color=folder_color),
                            ft.Text(t.title, size=16, weight=ft.FontWeight.BOLD,
                                    color=ft.Colors.GREY_500 if t.completed else None,
                                    style=ft.TextStyle(
                                        decoration=ft.TextDecoration.LINE_THROUGH if t.completed else None))],
                           spacing=4),
                    ft.Row(badges, spacing=6, wrap=True),
                ], spacing=4, expand=True),
                ft.Row([
                    ft.IconButton(ft.Icons.INFO_OUTLINE, tooltip="Открыть карточку",
                                  icon_color=ft.Colors.BLUE_700,
                                  on_click=lambda e, task=t: open_task_card(task)),
                    ft.IconButton(ft.Icons.HOURGLASS_EMPTY,
                                  tooltip=f"Обычный таймер ({tm.settings.regular_timer_minutes} мин)",
                                  icon_color=(ft.Colors.GREEN if is_this and timer_state.type == "regular"
                                              else ft.Colors.GREY_700),
                                  disabled=busy,
                                  on_click=lambda e, task=t: start_timer(task, "regular")),
                    ft.IconButton(ft.Icons.ACCESS_TIME,  # FIX: ACCESS_TIME
                                  tooltip=f"Pomodoro ({tm.settings.pomodoro_work} мин)",
                                  icon_color=(ft.Colors.RED if is_this and timer_state.type == "pomodoro"
                                              else ft.Colors.GREY_700),
                                  disabled=busy,
                                  on_click=lambda e, task=t: start_timer(task, "pomodoro")),
                    ft.IconButton(ft.Icons.EDIT, tooltip="Изменить",
                                  on_click=lambda e, task=t: open_editor(task)),
                    ft.IconButton(ft.Icons.DELETE, tooltip="Удалить", icon_color=ft.Colors.RED_400,
                                  on_click=lambda e, task=t: delete_task(task)),
                ], spacing=0, tight=True),
            ]
            if shopping_section:
                tasks_view.controls.append(ft.Card(content=ft.Container(
                    padding=8,
                    content=ft.Column([
                        ft.Row(card_content, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                        shopping_section,
                    ], spacing=6))))
            else:
                tasks_view.controls.append(ft.Card(content=ft.Container(
                    padding=8,
                    content=ft.Row(card_content, vertical_alignment=ft.CrossAxisAlignment.CENTER))))
        try:
            page.update()
        except Exception:
            pass

    # Компоновка
    page.add(ft.Row([
        ft.Container(width=290, padding=10, border_radius=10,
                      content=ft.Column([
                          ft.Text("Папки", size=18, weight=ft.FontWeight.BOLD),
                          folders_view, new_folder_field,
                          ft.ElevatedButton("Добавить папку", icon=ft.Icons.ADD, on_click=add_folder),
                      ], spacing=8)),
        ft.Container(expand=True, padding=10,
                      content=ft.Column([
                          ft.Row([
                              header,
                              save_status,
                              ft.ElevatedButton("Все", icon=ft.Icons.LIST,
                                                on_click=lambda e: set_view("all")),
                              ft.ElevatedButton("Задачи", icon=ft.Icons.CHECKLIST,
                                                on_click=lambda e: set_view("tasks")),
                              ft.ElevatedButton("Покупки", icon=ft.Icons.SHOPPING_CART,
                                                on_click=lambda e: set_view("shopping")),
                              ft.Container(width=1, height=24, bgcolor=ft.Colors.GREY_400,
                                           margin=ft.margin.symmetric(horizontal=4)),
                              ft.IconButton(ft.Icons.HOURGLASS_EMPTY,
                                            tooltip=f"Таймер ({tm.settings.regular_timer_minutes} мин)",
                                            icon_color=ft.Colors.GREEN,
                                            on_click=lambda e: start_standalone_timer("regular")),
                              ft.IconButton(ft.Icons.ACCESS_TIME,  # FIX: ACCESS_TIME
                                            tooltip=f"Pomodoro ({tm.settings.pomodoro_work} мин)",
                                            icon_color=ft.Colors.RED,
                                            on_click=lambda e: start_standalone_timer("pomodoro")),
                              ft.Container(width=1, height=24, bgcolor=ft.Colors.GREY_400,
                                           margin=ft.margin.symmetric(horizontal=4)),
                              ft.IconButton(ft.Icons.CALENDAR_MONTH, tooltip="Календарь",
                                            on_click=lambda e: show_calendar()),
                              ft.IconButton(ft.Icons.SHOW_CHART, tooltip="Статистика",
                                            on_click=lambda e: show_dashboard()),
                              ft.IconButton(ft.Icons.NOTE_ALT, tooltip="Шаблоны",  # FIX: NOTE_ALT
                                            on_click=lambda e: show_templates()),
                              ft.IconButton(ft.Icons.SETTINGS, tooltip="Настройки",
                                            on_click=show_settings),
                              ft.ElevatedButton("Добавить задачу", icon=ft.Icons.ADD,
                                                on_click=lambda e: open_editor()),
                          ], spacing=4, wrap=True,
                             alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                             vertical_alignment=ft.CrossAxisAlignment.CENTER),
                          standalone_timers_view,
                          timer_banner,
                          tasks_view,
                      ], spacing=10, expand=True)),
    ], expand=True, spacing=10))

    render_folders()
    render_tasks()
    render_standalone_timers()
    apply_theme_if_needed()
    update_window_title()


if __name__ == "__main__":
    ft.app(target=main)