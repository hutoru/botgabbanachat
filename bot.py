"""
Бот для чата resale gabbana (aiogram 3.x).

Что умеет:
  1. Модерация: приветствие новичков, антиспам (ссылки от новичков, флуд, стоп-слова),
     удаление служебных сообщений «вступил/вышел», команда /rules.
  2. Каталог: админ добавляет вещь через /add в личке с ботом -> бот публикует пост
     с фото и кнопкой в чат. Поиск: /find <слово>, список: /catalog. /sold <id> — «продано».
  3. Заявки: кнопка «Купить / узнать цену» -> заявка улетает админам в личку.
"""
import asyncio
import hashlib
import hmac
import json
import html
import logging
import os
import re
import sqlite3
import time
from collections import defaultdict, deque
from datetime import datetime, timedelta
from urllib.parse import parse_qsl

from aiogram import Bot, Dispatcher, F, Router
from aiohttp import web
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ChatType, ParseMode
from aiogram.filters import Command, CommandObject, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import (
    CallbackQuery,
    ChatPermissions,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MenuButtonWebApp,
    Message,
    WebAppInfo,
)

try:
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass

# ----------------------------- НАСТРОЙКИ -----------------------------------
BOT_TOKEN = os.environ["BOT_TOKEN"]
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x}
CHAT = os.getenv("CHAT", "@gabbanachat")  # @username или числовой id чата
DB_PATH = os.getenv("DB_PATH", "gabbana.db")
PAY_URL = os.getenv("PAY_URL", "https://finance.ozon.ru/apps/sbp/ozonbankpay/019eadee-df6b-71f7-9462-2fca57eaa923")
WEBAPP_URL = os.getenv("WEBAPP_URL", "")  # публичный https-адрес, где запущен бот (для Mini App)
PORT = int(os.getenv("PORT", "8080"))
ADMIN_COMMAND = os.getenv("ADMIN_COMMAND", "AdminExtQwe")  # секретная команда выдачи админки

# тарифы размещения: ключ -> (название, цена ₽, описание). Цены меняются здесь.
PLANS = {
    "free": ("🆓 Обычное", 0, "Публикация после проверки админом"),
    "priority": ("⭐ Приоритет", 10, "Проверка вне очереди, значок ⭐ и первое место в каталоге"),
    "vip": ("👑 VIP", 40, "Всё из «Приоритета» + закреп в чате на 24 часа"),
}

NEWBIE_HOURS = 24          # сколько часов участник считается новичком (ссылки запрещены)
FLOOD_MESSAGES = 6         # больше N сообщений ...
FLOOD_SECONDS = 10         # ... за M секунд = флуд
MUTE_MINUTES = 10          # мут за флуд
WELCOME_DELETE_AFTER = 60  # через сколько секунд удалять приветствие

STOP_WORDS = [             # можно дополнять
    "казино", "ставки на спорт", "быстрый заработок", "пассивный доход",
    "заработок в интернете", "работа на дому", "пиши в лс заработ",
]

RULES_TEXT = (
    "<b>Правила чата</b>\n"
    "1. Без спама и рекламы сторонних каналов/чатов.\n"
    "2. Пишем по теме: вещи, аксессуары, общение.\n"
    "3. Уважаем друг друга, без оскорблений.\n"
    "4. Покупка — через кнопку под постом или в лс админу.\n"
    "\nНарушение = удаление сообщения, мут или бан."
)
# ---------------------------------------------------------------------------

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("gabbana")

router = Router()  # команды, каталог, заявки
mod = Router()     # модерация (подключается последним)
S: dict = {}       # chat_id, username — заполняются при старте

URL_RE = re.compile(r"(https?://|www\.|t\.me/|telegram\.me/|\b[\w-]+\.(?:com|ru|io|me|ly|xyz|top|site)\b)", re.I)

# ------------------------------ БАЗА ---------------------------------------
db = sqlite3.connect(DB_PATH, check_same_thread=False)
db.row_factory = sqlite3.Row
db.executescript(
    """
    CREATE TABLE IF NOT EXISTS items(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        title TEXT, size TEXT, price TEXT, tags TEXT, photo_id TEXT,
        status TEXT DEFAULT 'available', chat_msg_id INTEGER, created REAL
    );
    CREATE TABLE IF NOT EXISTS orders(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        item_id INTEGER, user_id INTEGER, user_name TEXT, created REAL
    );
    CREATE TABLE IF NOT EXISTS members(
        user_id INTEGER PRIMARY KEY, joined REAL
    );
    """
)
for col in ("owner_id INTEGER", "owner_name TEXT", "plan TEXT DEFAULT 'free'", "proof TEXT", "paid INTEGER DEFAULT 0"):
    try:
        db.execute("ALTER TABLE items ADD COLUMN " + col)
    except sqlite3.OperationalError:
        pass
db.execute("CREATE TABLE IF NOT EXISTS admins(user_id INTEGER PRIMARY KEY)")
db.execute("CREATE TABLE IF NOT EXISTS users(user_id INTEGER PRIMARY KEY, name TEXT, username TEXT, registered REAL)")
OWNERS = set(ADMIN_IDS)  # владельцы из .env — только они назначают админов
ADMIN_IDS |= {r[0] for r in db.execute("SELECT user_id FROM admins")}
db.commit()


def esc(s) -> str:
    return html.escape(str(s or ""))


def get_item(item_id: int):
    return db.execute("SELECT * FROM items WHERE id=?", (item_id,)).fetchone()


def item_caption(it) -> str:
    star = "⭐ " if it["plan"] != "free" else ""
    title = f"<s>{esc(it['title'])}</s>" if it["status"] == "sold" else esc(it["title"])
    tags = " ".join("#" + t for t in it["tags"].split() if t)
    text = f"{star}<b>{title}</b>\n\n<b>{esc(it['price'])}</b>\nРазмер: {esc(it['size'])}"
    if tags:
        text += f"\n\n{esc(tags)}"
    text += f"\n<i>№{it['id']}</i>"
    if it["status"] == "sold":
        text = "Продано\n" + text
    return text


def buy_kb(item_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="Купить", callback_data=f"buy:{item_id}")]]
    )


def msg_link(msg_id: int) -> str:
    if S.get("username"):
        return f"https://t.me/{S['username']}/{msg_id}"
    return f"https://t.me/c/{str(S['chat_id'])[4:]}/{msg_id}"


async def is_admin(bot: Bot, chat_id: int, user_id: int) -> bool:
    if user_id in ADMIN_IDS:
        return True
    try:
        member = await bot.get_chat_member(chat_id, user_id)
        return member.status in ("administrator", "creator")
    except Exception:
        return False


async def delete_later(bot: Bot, chat_id: int, msg_id: int, delay: int):
    await asyncio.sleep(delay)
    try:
        await bot.delete_message(chat_id, msg_id)
    except Exception:
        pass


# ------------------------------ /start, /help ------------------------------
STATUS_RU = {
    "available": "в каталоге", "pending": "на проверке", "pending_pay": "ждёт чек об оплате",
    "rejected": "отклонено", "sold": "продано",
}


async def show_me(msg: Message, user):
    register(user.id, user.full_name, user.username)
    rows = db.execute("SELECT * FROM items WHERE owner_id=? ORDER BY id DESC LIMIT 15", (user.id,)).fetchall()
    lines = [f"№{r['id']} {esc(r['title'])}, {esc(r['price'])}: {STATUS_RU.get(r['status'], r['status'])}" for r in rows]
    await msg.answer("<b>Личный кабинет</b>\n\n" + ("\n".join(lines) if lines else "Объявлений пока нет. Выставить: /post"))


@router.message(Command("me"), F.chat.type == ChatType.PRIVATE)
async def cmd_me(m: Message):
    await show_me(m, m.from_user)


@router.callback_query(F.data == "me")
async def cb_me(cb: CallbackQuery):
    await cb.answer()
    await show_me(cb.message, cb.from_user)


@router.message(Command("start", "help"), F.chat.type == ChatType.PRIVATE)
async def cmd_start(m: Message, command: CommandObject, state: FSMContext):
    register(m.from_user.id, m.from_user.full_name, m.from_user.username)  # регистрация через Telegram
    if command.args == "post":
        return await add_start(m, state)
    rows = []
    if WEBAPP_URL:
        rows.append([InlineKeyboardButton(text="🛍 Открыть каталог", web_app=WebAppInfo(url=WEBAPP_URL))])
    rows.append([InlineKeyboardButton(text="👤 Личный кабинет", callback_data="me")])
    rows.append([InlineKeyboardButton(text="➕ Выставить вещь", callback_data="post")])
    rows.append([InlineKeyboardButton(text="⭐ Услуги и цены", callback_data="services")])
    text = "Привет! Я бот <b>resale gabbana</b> 🖤\nСмотри вещи, выставляй свои и продвигай объявления."
    if m.from_user.id in ADMIN_IDS:
        text += "\n\n🔐 Ты админ — панель: /admin"
    await m.answer(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=rows))


@router.callback_query(F.data == "post")
async def cb_post(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    await add_start(cb.message, state)


@router.callback_query(F.data == "services")
async def cb_services(cb: CallbackQuery):
    await cb.answer()
    await cb.message.answer("<b>Услуги продвижения</b>\n\n" + plans_text() + "Оформить можно при размещении: /post")


@router.message(Command("rules"))
async def cmd_rules(m: Message):
    await m.answer(RULES_TEXT)


# ------------------------------ КАТАЛОГ: добавление ------------------------
class Add(StatesGroup):
    photo = State()
    title = State()
    size = State()
    price = State()
    tags = State()


@router.message(Command("cancel"), StateFilter("*"))
async def cmd_cancel(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Отменено.")


@router.message(Command("add", "post"), F.chat.type == ChatType.PRIVATE)
async def add_start(m: Message, state: FSMContext):
    await state.set_state(Add.photo)
    await m.answer("📸 Отправь фото вещи (/cancel — отмена).")


@router.message(Add.photo, F.photo)
async def add_photo(m: Message, state: FSMContext):
    await state.update_data(photo=m.photo[-1].file_id)
    await state.set_state(Add.title)
    await m.answer("Название? Например: Dolce&Gabbana футболка")


@router.message(Add.photo)
async def add_photo_wrong(m: Message):
    await m.answer("Нужно именно фото.")


@router.message(Add.title, F.text)
async def add_title(m: Message, state: FSMContext):
    await state.update_data(title=m.text.strip())
    await state.set_state(Add.size)
    await m.answer("Размер? (например M, 42, one size)")


@router.message(Add.size, F.text)
async def add_size(m: Message, state: FSMContext):
    await state.update_data(size=m.text.strip())
    await state.set_state(Add.price)
    await m.answer("Цена? (например 8500 ₽)")


@router.message(Add.price, F.text)
async def add_price(m: Message, state: FSMContext):
    await state.update_data(price=m.text.strip())
    await state.set_state(Add.tags)
    await m.answer("Теги через пробел или запятую (для поиска). Например: футболка gabbana лето")


class Pay(StatesGroup):
    proof = State()


def plans_text() -> str:
    return "\n".join(
        (f"{n} — <b>{p} ₽</b>\n<i>{d}</i>\n" if p else f"{n}\n<i>{d}</i>\n") for n, p, d in PLANS.values()
    )


def new_item(d, user, plan, status):
    cur = db.execute(
        "INSERT INTO items(title,size,price,tags,photo_id,created,owner_id,owner_name,plan,status) "
        "VALUES(?,?,?,?,?,?,?,?,?,?)",
        (d["title"], d["size"], d["price"], d["tags"], d["photo"], time.time(), user.id, user.full_name, plan, status),
    )
    db.commit()
    return cur.lastrowid


async def unpin_later(bot: Bot, msg_id: int, delay: int):
    await asyncio.sleep(delay)
    try:
        await bot.unpin_chat_message(S["chat_id"], msg_id)
    except Exception:
        pass


async def publish_item(bot: Bot, item_id: int) -> int:
    it = get_item(item_id)
    sent = await bot.send_photo(S["chat_id"], it["photo_id"], caption=item_caption(it), reply_markup=buy_kb(item_id))
    db.execute("UPDATE items SET chat_msg_id=?, status='available' WHERE id=?", (sent.message_id, item_id))
    db.commit()
    if it["plan"] == "vip":
        try:
            await bot.pin_chat_message(S["chat_id"], sent.message_id, disable_notification=True)
            asyncio.create_task(unpin_later(bot, sent.message_id, 86400))
        except Exception as e:
            log.warning("Не удалось закрепить: %s", e)
    return sent.message_id


async def notify_admins(bot: Bot, item_id: int, targets=None):
    it = get_item(item_id)
    name, price, _ = PLANS[it["plan"]]
    head = (
        f"🕓 <b>На модерации</b> · {name}\n"
        f"От: <a href=\"tg://user?id={it['owner_id']}\">{esc(it['owner_name'])}</a>"
    )
    if price:
        head += f"\n💳 Оплата {price} ₽ — сверь чек выше"
    kb = InlineKeyboardMarkup(
        inline_keyboard=[[
            InlineKeyboardButton(text="✅ Опубликовать", callback_data=f"mod:ok:{item_id}"),
            InlineKeyboardButton(text="❌ Отклонить", callback_data=f"mod:no:{item_id}"),
        ]]
    )
    for a in targets or ADMIN_IDS:
        try:
            if it["proof"]:
                await bot.send_photo(a, it["proof"], caption="🧾 Чек об оплате")
            await bot.send_photo(a, it["photo_id"], caption=head + "\n\n" + item_caption(it), reply_markup=kb)
        except Exception as e:
            log.warning("Админу %s не доставлено: %s", a, e)


@router.message(Add.tags, F.text)
async def add_tags(m: Message, state: FSMContext, bot: Bot):
    tags = " ".join(sorted({t.lower().lstrip("#") for t in re.split(r"[,\s]+", m.text) if t}))
    await state.update_data(tags=tags)
    if m.from_user.id in ADMIN_IDS:  # админы публикуют сразу
        data = await state.get_data()
        await state.clear()
        item_id = new_item(data, m.from_user, "free", "available")
        mid = await publish_item(bot, item_id)
        return await m.answer(f"Опубликовано в чате. ID вещи: {item_id}\n{msg_link(mid)}")
    kb = [
        [InlineKeyboardButton(text=f"{n} — {str(p) + ' ₽' if p else 'бесплатно'}", callback_data=f"plan:{k}")]
        for k, (n, p, _) in PLANS.items()
    ]
    await m.answer("Выбери тариф размещения:\n\n" + plans_text(), reply_markup=InlineKeyboardMarkup(inline_keyboard=kb))


@router.callback_query(F.data.startswith("plan:"), Add.tags)
async def on_plan(cb: CallbackQuery, state: FSMContext, bot: Bot):
    plan = cb.data.split(":")[1]
    name, price, _ = PLANS[plan]
    data = await state.get_data()
    item_id = new_item(data, cb.from_user, plan, "pending" if not price else "pending_pay")
    await cb.answer()
    if not price:
        await state.clear()
        await cb.message.answer("✅ Отправлено на модерацию. Напишу, когда объявление выйдет.")
        return await notify_admins(bot, item_id)
    await state.set_state(Pay.proof)
    await state.update_data(item_id=item_id)
    await cb.message.answer(
        f"К оплате: <b>{price} ₽</b> ({name})\n\n"
        f"1️⃣ Оплати по СБП: <a href=\"{PAY_URL}\">Ozon Банк</a>. Если сумма не подставилась — введи {price} ₽ вручную.\n"
        f"2️⃣ Пришли сюда скриншот чека.\n\n"
        f"Объявление №{item_id} уйдёт админам сразу после чека. /cancel — отмена"
    )


@router.message(Pay.proof, F.photo)
async def on_proof(m: Message, state: FSMContext, bot: Bot):
    item_id = (await state.get_data())["item_id"]
    await state.clear()
    db.execute("UPDATE items SET proof=?, status='pending' WHERE id=?", (m.photo[-1].file_id, item_id))
    db.commit()
    await m.answer("🧾 Чек получен. Админ проверит оплату и опубликует объявление.")
    await notify_admins(bot, item_id)


@router.message(Pay.proof)
async def proof_wrong(m: Message):
    await m.answer("Пришли скриншот чека (именно фото).")


@router.callback_query(F.data.startswith("mod:"))
async def on_mod(cb: CallbackQuery, bot: Bot):
    if cb.from_user.id not in ADMIN_IDS:
        return await cb.answer("Нет доступа", show_alert=True)
    _, act, sid = cb.data.split(":")
    it = get_item(int(sid))
    if not it or it["status"] != "pending":
        return await cb.answer("Уже обработано", show_alert=True)
    if act == "ok":
        db.execute("UPDATE items SET paid=? WHERE id=?", (PLANS[it["plan"]][1], it["id"]))
        db.commit()
        mid = await publish_item(bot, it["id"])
        label, note = "✅ Опубликовано", f"✅ Твоё объявление опубликовано!\n{msg_link(mid)}"
    else:
        db.execute("UPDATE items SET status='rejected' WHERE id=?", (it["id"],))
        db.commit()
        label = "❌ Отклонено"
        note = "❌ Объявление не прошло проверку. Если оплачивал(а) — напиши админу, разберёмся."
    await cb.message.edit_caption(
        caption=f"{label} · {esc(cb.from_user.full_name)}\n\n{item_caption(get_item(it['id']))}", reply_markup=None
    )
    try:
        await bot.send_message(it["owner_id"], note)
    except Exception:
        pass
    await cb.answer()


# ------------------------------ АДМИН-ПАНЕЛЬ ------------------------------
def count(q: str) -> int:
    return db.execute(q).fetchone()[0] or 0


@router.message(Command("admin"), F.chat.type == ChatType.PRIVATE)
async def cmd_admin(m: Message):
    if m.from_user.id not in ADMIN_IDS:
        return
    pend = count("SELECT COUNT(*) FROM items WHERE status='pending'")
    avail = count("SELECT COUNT(*) FROM items WHERE status='available'")
    sold = count("SELECT COUNT(*) FROM items WHERE status='sold'")
    kb = InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text=f"🕓 Очередь модерации ({pend})", callback_data="adm:queue")]]
    )
    await m.answer(
        "🔐 <b>Админ-панель</b>\n\n"
        f"📦 В каталоге: {avail}\n"
        f"❌ Продано: {sold}\n"
        f"🛒 Заявок: {count('SELECT COUNT(*) FROM orders')}\n"
        f"👥 Новичков отслежено: {count('SELECT COUNT(*) FROM members')}\n"
        f"💰 Доход с продвижения: {count('SELECT SUM(paid) FROM items')} ₽\n\n"
        f"Админы: {', '.join(map(str, sorted(ADMIN_IDS)))}\n"
        "/addadmin <id> · /deladmin <id> · /sold <id> · /post",
        reply_markup=kb,
    )


@router.callback_query(F.data == "adm:queue")
async def adm_queue(cb: CallbackQuery, bot: Bot):
    if cb.from_user.id not in ADMIN_IDS:
        return await cb.answer("Нет доступа", show_alert=True)
    await cb.answer()
    rows = db.execute("SELECT id FROM items WHERE status='pending' ORDER BY (plan!='free') DESC, id").fetchall()
    if not rows:
        return await cb.message.answer("Очередь пуста ✨")
    for r in rows:
        await notify_admins(bot, r["id"], targets=[cb.from_user.id])


@router.message(Command(ADMIN_COMMAND, ignore_case=True), F.chat.type == ChatType.PRIVATE)
async def cmd_secret_admin(m: Message):
    uid = m.from_user.id
    if uid in ADMIN_IDS:
        return await m.answer("Ты уже админ. Панель: /admin")
    db.execute("INSERT OR IGNORE INTO admins VALUES(?)", (uid,))
    db.commit()
    ADMIN_IDS.add(uid)
    log.info("Выдана админка по секретной команде: %s (@%s)", uid, m.from_user.username)
    for o in OWNERS:
        try:
            await m.bot.send_message(o, f"🔑 Админка выдана: <a href=\"tg://user?id={uid}\">{esc(m.from_user.full_name)}</a> ({uid}). Убрать: /deladmin {uid}")
        except Exception:
            pass
    await m.answer("🔐 Админ-доступ выдан! Панель: /admin")


@router.message(Command("addadmin", "deladmin"))
async def cmd_addadmin(m: Message, command: CommandObject):
    if m.from_user.id not in OWNERS:
        return
    arg = (command.args or "").strip()
    if not arg.isdigit():
        return await m.answer("Использование: /addadmin <id> или /deladmin <id>")
    uid = int(arg)
    if command.command == "addadmin":
        db.execute("INSERT OR IGNORE INTO admins VALUES(?)", (uid,))
        ADMIN_IDS.add(uid)
    elif uid in OWNERS:
        return await m.answer("Владельца удалить нельзя.")
    else:
        db.execute("DELETE FROM admins WHERE user_id=?", (uid,))
        ADMIN_IDS.discard(uid)
    db.commit()
    await m.answer("Готово ✅ (новый админ должен нажать /start у бота)")


@router.message(Command("sold"))
async def cmd_sold(m: Message, command: CommandObject, bot: Bot):
    if m.from_user.id not in ADMIN_IDS:
        return
    if not command.args or not command.args.strip().isdigit():
        return await m.answer("Использование: /sold <id>")
    item = get_item(int(command.args))
    if not item:
        return await m.answer("Вещь не найдена.")
    db.execute("UPDATE items SET status='sold' WHERE id=?", (item["id"],))
    db.commit()
    item = get_item(item["id"])
    try:
        await bot.edit_message_caption(
            chat_id=S["chat_id"], message_id=item["chat_msg_id"], caption=item_caption(item), reply_markup=None
        )
    except Exception as e:
        log.warning("Не удалось обновить пост: %s", e)
    await m.answer(f"Вещь #{item['id']} помечена как проданная.")


# ------------------------------ КАТАЛОГ: поиск ----------------------------
@router.message(Command("find", "catalog"))
async def cmd_find(m: Message, command: CommandObject):
    query = (command.args or "").lower().strip()
    rows = db.execute("SELECT * FROM items WHERE status='available' ORDER BY (plan!='free') DESC, id DESC").fetchall()
    if query:
        words = query.split()
        rows = [r for r in rows if all(w in f"{r['title']} {r['tags']}".lower() for w in words)]
    if not rows:
        return await m.answer("Ничего не найдено.")
    lines = [
        f"• <a href=\"{msg_link(r['chat_msg_id'])}\">{esc(r['title'])}</a> — {esc(r['size'])}, {esc(r['price'])}"
        for r in rows[:10]
    ]
    tail = f"\n…и ещё {len(rows) - 10}. Уточни запрос: /find <слово>" if len(rows) > 10 else ""
    await m.answer("\n".join(lines) + tail, disable_web_page_preview=True)


# ------------------------------ ЗАЯВКИ ------------------------------------
@router.callback_query(F.data.startswith("buy:"))
async def on_buy(cb: CallbackQuery, bot: Bot):
    item = get_item(int(cb.data.split(":")[1]))
    if not item or item["status"] == "sold":
        return await cb.answer("Эта вещь уже продана 😔", show_alert=True)
    user = cb.from_user
    dup = db.execute(
        "SELECT 1 FROM orders WHERE item_id=? AND user_id=?", (item["id"], user.id)
    ).fetchone()
    if dup:
        return await cb.answer("Заявка уже отправлена, админ скоро свяжется.", show_alert=True)
    db.execute(
        "INSERT INTO orders(item_id,user_id,user_name,created) VALUES(?,?,?,?)",
        (item["id"], user.id, user.full_name, time.time()),
    )
    db.commit()
    contact = f"@{user.username}" if user.username else f"<a href=\"tg://user?id={user.id}\">{esc(user.full_name)}</a>"
    text = (
        f"🛒 <b>Новая заявка</b>\n"
        f"Вещь: <a href=\"{msg_link(item['chat_msg_id'])}\">{esc(item['title'])}</a> (ID {item['id']})\n"
        f"Размер: {esc(item['size'])}, цена: {esc(item['price'])}\n"
        f"Покупатель: {contact}"
    )
    owner = {item["owner_id"]} if item["owner_id"] else set()
    for admin_id in ADMIN_IDS | owner:
        try:
            await bot.send_message(admin_id, text, disable_web_page_preview=True)
        except Exception as e:
            log.warning("Не удалось написать админу %s (он нажал /start у бота?): %s", admin_id, e)
    await cb.answer("Заявка отправлена! Админ скоро свяжется с тобой.", show_alert=True)


# ------------------------------ МОДЕРАЦИЯ ---------------------------------
flood: dict = defaultdict(lambda: deque(maxlen=FLOOD_MESSAGES + 1))


@mod.message(F.new_chat_members)
async def on_join(m: Message, bot: Bot):
    if m.chat.id != S["chat_id"]:
        return
    try:
        await m.delete()  # убираем служебное «X вступил»
    except Exception:
        pass
    for u in m.new_chat_members:
        if u.is_bot:
            continue
        db.execute("INSERT OR REPLACE INTO members(user_id, joined) VALUES(?,?)", (u.id, time.time()))
        db.commit()
        welcome = await bot.send_message(
            m.chat.id,
            f"Привет, <a href=\"tg://user?id={u.id}\">{esc(u.full_name)}</a>! 👋\n"
            f"Это resale gabbana. Правила: /rules\nВещи в каталоге: /catalog",
        )
        asyncio.create_task(delete_later(bot, m.chat.id, welcome.message_id, WELCOME_DELETE_AFTER))


@mod.message(F.left_chat_member)
async def on_left(m: Message):
    if m.chat.id == S["chat_id"]:
        try:
            await m.delete()
        except Exception:
            pass


@mod.message(F.chat.type.in_({ChatType.GROUP, ChatType.SUPERGROUP}))
async def antispam(m: Message, bot: Bot):
    if m.chat.id != S["chat_id"] or m.sender_chat or not m.from_user:
        return
    if await is_admin(bot, m.chat.id, m.from_user.id):
        return

    text = (m.text or m.caption or "").lower()

    # 1) стоп-слова
    if any(w in text for w in STOP_WORDS):
        return await m.delete()

    # 2) ссылки от новичков
    row = db.execute("SELECT joined FROM members WHERE user_id=?", (m.from_user.id,)).fetchone()
    is_newbie = bool(row) and (time.time() - row["joined"]) < NEWBIE_HOURS * 3600
    has_link = bool(URL_RE.search(text)) or any(
        e.type in ("url", "text_link") for e in (m.entities or []) + (m.caption_entities or [])
    )
    if is_newbie and has_link:
        await m.delete()
        note = await m.answer(f"{esc(m.from_user.first_name)}, ссылки новичкам временно нельзя 🙏")
        asyncio.create_task(delete_later(bot, m.chat.id, note.message_id, 15))
        return

    # 3) флуд
    now = time.time()
    q = flood[m.from_user.id]
    q.append(now)
    recent = [t for t in q if now - t <= FLOOD_SECONDS]
    if len(recent) > FLOOD_MESSAGES:
        q.clear()
        try:
            await bot.restrict_chat_member(
                m.chat.id,
                m.from_user.id,
                permissions=ChatPermissions(can_send_messages=False),
                until_date=datetime.now() + timedelta(minutes=MUTE_MINUTES),
            )
            note = await m.answer(f"{esc(m.from_user.first_name)} в муте на {MUTE_MINUTES} мин за флуд.")
            asyncio.create_task(delete_later(bot, m.chat.id, note.message_id, 30))
        except Exception as e:
            log.warning("Не удалось выдать мут: %s", e)
        await m.delete()


# ------------------------------ MINI APP (веб-сервер) ----------------------
WEB_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "webapp")


async def web_index(request):
    return web.FileResponse(os.path.join(WEB_DIR, "index.html"))


async def api_items(request):
    rows = db.execute(
        "SELECT * FROM items WHERE status='available' ORDER BY (plan!='free') DESC, id DESC"
    ).fetchall()
    data = {
        "bot": S["bot_username"],
        "services": [{"name": n, "price": p, "desc": d} for n, p, d in PLANS.values() if p],
        "items": [
            {
                "id": r["id"], "title": r["title"], "size": r["size"], "price": r["price"],
                "tags": r["tags"].split(), "vip": r["plan"] != "free", "link": msg_link(r["chat_msg_id"]),
            }
            for r in rows
        ],
    }
    return web.json_response(data)


async def api_photo(request):
    it = get_item(int(request.match_info["id"]))
    if not it or it["status"] != "available":
        raise web.HTTPNotFound()
    bot = request.app["bot"]
    f = await bot.get_file(it["photo_id"])
    buf = await bot.download_file(f.file_path)
    return web.Response(body=buf.read(), content_type="image/jpeg", headers={"Cache-Control": "public, max-age=86400"})


def register(uid: int, name: str, username):
    db.execute("INSERT OR IGNORE INTO users(user_id, registered) VALUES(?,?)", (uid, time.time()))
    db.execute("UPDATE users SET name=?, username=? WHERE user_id=?", (name, username, uid))
    db.commit()


def verify_init(init: str):
    """Проверка подписи Telegram: вход через Mini App нельзя подделать."""
    try:
        data = dict(parse_qsl(init, strict_parsing=True))
        got = data.pop("hash")
        check = "\n".join(f"{k}={v}" for k, v in sorted(data.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        if not hmac.compare_digest(hmac.new(secret, check.encode(), hashlib.sha256).hexdigest(), got):
            return None
        if time.time() - int(data["auth_date"]) > 86400:
            return None
        return json.loads(data["user"])
    except Exception:
        return None


def auth(request):
    u = verify_init(request.headers.get("X-Init-Data", ""))
    if u:
        register(u["id"], " ".join(filter(None, [u.get("first_name"), u.get("last_name")])), u.get("username"))
    return u


async def mark_sold(bot: Bot, item):
    db.execute("UPDATE items SET status='sold' WHERE id=?", (item["id"],))
    db.commit()
    it = get_item(item["id"])
    try:
        await bot.edit_message_caption(
            chat_id=S["chat_id"], message_id=it["chat_msg_id"], caption=item_caption(it), reply_markup=None
        )
    except Exception as e:
        log.warning("Не удалось обновить пост: %s", e)


async def api_me(request):
    u = auth(request)
    if not u:
        raise web.HTTPUnauthorized()
    uid = u["id"]
    me = db.execute("SELECT * FROM users WHERE user_id=?", (uid,)).fetchone()
    items = db.execute("SELECT * FROM items WHERE owner_id=? ORDER BY id DESC", (uid,)).fetchall()
    reqs = db.execute(
        "SELECT i.title, i.status FROM orders o JOIN items i ON i.id=o.item_id WHERE o.user_id=? ORDER BY o.id DESC LIMIT 20",
        (uid,),
    ).fetchall()
    inc = db.execute(
        "SELECT COUNT(*) FROM orders o JOIN items i ON i.id=o.item_id WHERE i.owner_id=?", (uid,)
    ).fetchone()[0]
    return web.json_response({
        "user": {"id": uid, "name": me["name"], "username": me["username"], "since": me["registered"], "admin": uid in ADMIN_IDS},
        "items": [{"id": r["id"], "title": r["title"], "price": r["price"], "status": r["status"], "plan": r["plan"]} for r in items],
        "requests": [{"title": r["title"], "status": r["status"]} for r in reqs],
        "incoming": inc,
    })


async def api_sold(request):
    u = auth(request)
    if not u:
        raise web.HTTPUnauthorized()
    it = get_item(int(request.match_info["id"]))
    if not it or (it["owner_id"] != u["id"] and u["id"] not in ADMIN_IDS):
        raise web.HTTPForbidden()
    if it["status"] != "available":
        raise web.HTTPBadRequest()
    await mark_sold(request.app["bot"], it)
    return web.json_response({"ok": True})


# ------------------------------ ЗАПУСК -------------------------------------
async def main():
    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    chat = await bot.get_chat(CHAT)
    S["chat_id"], S["username"] = chat.id, chat.username
    S["bot_username"] = (await bot.me()).username
    log.info("Работаю с чатом: %s (%s)", chat.title, chat.id)

    dp = Dispatcher()
    dp.include_router(router)
    dp.include_router(mod)  # модерация — последней

    if WEBAPP_URL:
        app = web.Application()
        app["bot"] = bot
        app.add_routes([web.get("/", web_index), web.get("/api/items", api_items), web.get("/api/photo/{id}", api_photo),
                        web.get("/api/me", api_me), web.post("/api/sold/{id}", api_sold)])
        runner = web.AppRunner(app)
        await runner.setup()
        await web.TCPSite(runner, "0.0.0.0", PORT).start()
        await bot.set_chat_menu_button(menu_button=MenuButtonWebApp(text="Каталог", web_app=WebAppInfo(url=WEBAPP_URL)))
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
