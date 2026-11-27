import csv
import html
import io
import json
import os
import random
import re
import signal
import sys
import threading
import time
import uuid
from datetime import date, datetime, timedelta, timezone
from decimal import ROUND_HALF_UP, Decimal, InvalidOperation
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import quote

import requests
import telebot
from telebot import types
from telebot.apihelper import ApiTelegramException

BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()
XROCKET_KEY = os.environ.get("XROCKET_KEY", "").strip()
if not BOT_TOKEN or not XROCKET_KEY:
    print("ERROR: set the BOT_TOKEN and XROCKET_KEY environment variables.")
    raise SystemExit(1)
CHANNEL = "@promocodefailesms"
ADMIN_ID = 7032762364

API = "https://pay.api.xrocket.exchange"
CURRENCY = "USDT"
SLOTS = 6
WINNERS = 3
MEDALS = ["🥇", "🥈", "🥉"]
PLACE_NAMES = ["1st", "2nd", "3rd"]

# Two lotteries run side by side. Each has its own fee, prizes and reminder interval.
TIERS = {
    "A": {
        "emoji": "🎟",
        "name": {"en": "Classic", "bn": "ক্লাসিক", "zh": "经典", "hi": "क्लासिक"},
        "fee": Decimal("0.05"),
        "prizes": [Decimal("0.150"), Decimal("0.080"), Decimal("0.055")],
        "house": Decimal("0.015"),
        "reminder": 10 * 60,
    },
    "B": {
        "emoji": "💎",
        "name": {"en": "Premium", "bn": "প্রিমিয়াম", "zh": "尊享", "hi": "प्रीमियम"},
        "fee": Decimal("0.50"),
        "prizes": [Decimal("1.50"), Decimal("0.80"), Decimal("0.55")],
        "house": Decimal("0.15"),
        "reminder": 20 * 60,
    },
}
TIER_ORDER = ["A", "B"]
for _k, _c in TIERS.items():
    assert len(_c["prizes"]) == WINNERS <= SLOTS
    assert _c["fee"] * SLOTS == sum(_c["prizes"], Decimal("0")) + _c["house"], f"tier {_k}: prizes + platform fee must equal pool"

MIN_WITHDRAW = Decimal("0.01")
MAX_PER_USER = 3
ROUND_SECONDS = 24 * 3600
RESERVE_SECONDS = 300
DISPLAY_CHOICE_SECONDS = 180
DRAW_DELAY = 10
NEXT_DRAW_GAP = 10
REF_DEFAULT_PERCENT = Decimal("2")   # referral commission, % of the ticket price (admin can change it)
REF_MAX_PERCENT = Decimal("5")       # never above the platform's own 5% share
REF_REAL_PAYMENT_ONLY = True         # only tickets paid through xRocket earn commission (anti-abuse)
SOLVENCY_INTERVAL = 600
BACKUP_INTERVAL = 3600
SOLVENCY_BUFFER = Decimal("0.10")
LOOP_INTERVAL = 3
POLL_INTERVAL = 5
PENDING_MAX_AGE = 6 * 3600
PAYOUT_REVIEW_SECONDS = 900
HIST_PAGE = 6
COUNTDOWN_STEP = 1
DICE_ANIM = 4.5
MAX_ROLLS = 60
AUDIT_TOLERANCE = Decimal("0.0005")  # balance above what the history explains -> manual review
STRIKE_LIMIT = 3                     # unpaid reservations in a row ...
JOIN_BLOCK_HOURS = 12                # ... block joining for this long
FLUSH_DELAY = 1.0                    # seconds: changes are written to the database in the background
LEASE_SECONDS = 45                   # only one bot instance may write to the database at a time
KEEP_ROUNDS = 500                    # finished rounds kept in the database

UTC = timezone.utc
BDT = timezone(timedelta(hours=6))
LANGS = [("en", "English 🇬🇧"), ("bn", "বাংলা 🇧🇩"), ("zh", "中文 🇨🇳"), ("hi", "हिन्दी 🇮🇳")]
LANG_TZ = {
    "en": (UTC, "UTC"),
    "bn": (BDT, "BDT"),
    "zh": (timezone(timedelta(hours=8)), "CST"),
    "hi": (timezone(timedelta(hours=5, minutes=30)), "IST"),
}
SEP = "━━━━━━━━━━━━━━━━━━"
NUMBER_EMOJI = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣"]

BOT_TOKEN = BOT_TOKEN.strip()
XROCKET_KEY = XROCKET_KEY.strip()
HEADERS = {
    "Authorization": f"Bearer {XROCKET_KEY}",
    "Accept": "application/json",
    "Content-Type": "application/json",
}

RE_TICKET = re.compile(r"round (\d+) ticket (\d+)")
RE_ROUND = re.compile(r"round (\d+)")

bot = telebot.TeleBot(BOT_TOKEN)


def _guarded(orig, is_call):
    """Every handler is wrapped: banned users get a polite message and nothing else works for them."""

    def factory(*a, **kw):
        deco = orig(*a, **kw)

        def wrap(handler):
            def inner(obj):
                uid = obj.from_user.id
                private = is_call or obj.chat.type == "private"
                if private and uid != ADMIN_ID and is_banned(uid):
                    banned_reply(obj, is_call)
                    return
                return handler(obj)

            inner.__name__ = handler.__name__
            deco(inner)
            return handler

        return wrap

    return factory


bot.message_handler = _guarded(bot.message_handler, False)
bot.callback_query_handler = _guarded(bot.callback_query_handler, True)
lock = threading.RLock()
post_cache = {}
publish_state = {}
solv = {"state": None}
drafts = {}
pending_join = {}
draw_state = {"active": None, "gap_until": 0.0}
BOT_USERNAME = ""

TEXT = {
    "en": {
        "lang_prompt": "🌐 Choose your language / ভাষা বাছাই করুন / 选择语言 / भाषा चुनें",
        "lang_set": "✅ Language set to English.",
        "btn_join": "🎟 Join Lottery",
        "btn_tickets": "📜 Transactions",
        "btn_withdraw": "💸 Withdraw",
        "btn_lang": "🌐 Language",
        "btn_back": "⬅️ Back to menu",
        "btn_back_lot": "⬅️ Back to lotteries",
        "btn_prev": "◀️ Prev",
        "btn_next": "Next ▶️",
        "btn_yes_another": "✅ Yes, add another",
        "btn_no": "❌ No",
        "btn_pay_x": "💸 Pay with xRocket",
        "btn_pay_bal": "💰 Pay with Balance ({bal} USDT)",
        "btn_cancel": "❌ Cancel",
        "btn_pay_on": "💸 Pay on xRocket",
        "btn_check": "🔄 Check payment",
        "btn_show_user": "👤 Show @{u}",
        "btn_show_uid": "🔢 Show UID {uid}",
        "btn_confirm": "✅ Confirm",
        "btn_join_next": "🎟 Join Next Round",
        "menu_body": "🎰 <b>Lucky Dice Lottery</b>\n{sep}\n💰 Your balance: <b>{bal} USDT</b>\n{sep}\n🍀 <b>Feeling lucky?</b>\nPick your number, watch the dice roll live in our channel and win real USDT prizes — <b>3 winners</b> every round!\n\n🎲 Fair  •  🔴 Live  •  💸 Prizes go straight to your balance\n\nTap <b>Join Lottery</b> below to see what is running right now.\n{sep}\n📢 Channel: {channel}",
        "menu_paused": "⏸ New rounds are paused for now.",
        "join_title": "🎰 <b>Choose your lottery</b>\n{sep}\n{rows}\n{sep}\n👇 Tap the lottery you want to join.",
        "join_row": "{tname}\n   💵 Entry: <b>{fee} USDT</b>\n   🏆 Prizes: {prizes}\n   👥 Players: <b>{n}/{slots}</b>  •  ⏳ {left} left",
        "join_row_off": "{tname}\n   ⏳ The next round is opening shortly...",
        "no_round": "⏳ No lottery is open right now. Please try again in a moment.",
        "max_tickets": "⚠️ You already hold the maximum of <b>{max}</b> tickets in this round.",
        "all_taken": "🔒 All numbers are taken or reserved right now. Please try again in a few minutes.",
        "already_hold": "⚠️ You already hold ticket(s): {held}\nTaking another number increases your chance of winning, but each ticket costs <b>{fee} USDT</b>.\n\nDo you want to continue?",
        "pick_number": "<b>{tname} • Round #{id}</b> — pick your lucky number\n💵 Entry fee: <b>{fee} USDT</b>\n🏆 Prizes: {prizes}\n⏳ Ends: {ends}\n\nAvailable numbers:",
        "reserved_msg": "✅ {tname}: number {emoji} <b>{num}</b> is reserved for you for <b>{mins} minutes</b>.\n\n💵 Entry fee: <b>{fee} USDT</b>\nChoose how you want to pay:",
        "alert_closed": "This round is closed.",
        "alert_taken": "Sorry, this number was just taken.",
        "alert_max": "Maximum {max} tickets per round.",
        "alert_reserve_expired": "Your reservation expired. Please pick a number again.",
        "alert_creating": "Creating your invoice...",
        "invoice_fail": "❌ Could not create the invoice. Please try again.",
        "invoice_ready": "💸 <b>Invoice ready</b>\n\n{tname}: ticket {emoji} <b>{num}</b> — <b>{fee} USDT</b>\nPay within <b>{mins} minutes</b>. Your ticket is confirmed automatically after payment.",
        "alert_no_balance": "Not enough balance.",
        "alert_paid_bal": "Paid from balance.",
        "alert_cancelled": "Cancelled.",
        "alert_processed": "This payment has already been processed.",
        "alert_not_received": "⏳ Payment not received yet.",
        "entry_ok_choose": "🎉 <b>Payment received!</b>\nYour ticket: {emoji} <b>{num}</b> ({tname} • Round #{rid})\n👥 Players: {total}/{slots}\n\n👇 <b>One last step</b> — how should your name appear in the channel post?\n⏳ Your join is completed after this step (auto-selected in {wait} minutes if you do not choose).",
        "entry_ok_nouser": "🎉 <b>Payment received!</b>\nYour ticket is confirmed: {emoji} <b>{num}</b> ({tname} • Round #{rid})\n👥 Players: {total}/{slots}\n\nYou have no Telegram username, so your UID will be shown in the post.\n✅ Your join is complete!",
        "name_done": "✅ Done! Ticket {emoji} <b>{num}</b> will appear as <b>{shown}</b>.\n🎟 Your join is complete!",
        "alert_saved": "Saved!",
        "alert_ticket_missing": "Ticket not found.",
        "alert_round_done": "This round is already finished.",
        "alert_no_username": "You have no username.",
        "late_refund": "⚠️ Your payment arrived, but ticket <b>{num}</b> is no longer available (round closed or number taken).\n💰 <b>{fee} USDT</b> has been added to your balance.",
        "round_closed_dm": "⌛ <b>{tname} • Round #{rid} closed</b>\nNot enough players joined within 24 hours.\n💰 <b>{amount} USDT</b> has been refunded to your balance.\nYou can use it to join the next round.",
        "win_dm": "🎉 <b>CONGRATULATIONS!</b>\nYou won in {tname} • Round #{rid}:\n{wins}\n💰 <b>{prize} USDT</b> has been added to your balance.\n💳 New balance: <b>{bal} USDT</b>",
        "lose_dm": "🎲 {tname} • Round #{rid} finished.\nWinners:\n{winners}\nBetter luck next time! 🍀",
        "one_left_dm": "⏳ Only <b>1 spot</b> left in {tname} • Round #{rid}! The live draw starts as soon as it fills.",
        "hist_title": "📜 <b>Your transactions</b>\n{sep}\n{rows}\n{sep}\n📄 Page {page}/{pages}",
        "hist_empty": "📜 You have no transactions yet.",
        "hist_ticket": "🎟 <b>{tname}</b> • Round #{rid} • Ticket {emoji}\n   ➖ {amount} USDT ({method})\n   {status}\n   🕒 {time}",
        "hist_win": "🏆 <b>Prize won</b> — {tname} • Round #{rid} • Ticket {emoji}\n   ➕ {amount} USDT\n   🕒 {time}",
        "hist_refund": "↩️ <b>Refund</b> — {tname} • Round #{rid} closed\n   ➕ {amount} USDT\n   🕒 {time}",
        "hist_late": "↩️ <b>Late payment refund</b>\n   ➕ {amount} USDT\n   🕒 {time}",
        "hist_withdraw": "💸 <b>Withdrawal</b>\n   ➖ {amount} USDT\n   {status}\n   🕒 {time}",
        "hist_other": "🧾 {kind}: {amount} USDT\n   🕒 {time}",
        "method_bal": "Balance",
        "method_x": "xRocket",
        "st_ongoing": "🟢 Ongoing",
        "st_end": "🏁 Ended",
        "st_win": "🏆 WIN",
        "st_closed": "🏁 Ended (refunded)",
        "st_wd_done": "✅ Completed",
        "st_wd_pending": "⏳ Pending",
        "st_wd_failed": "❌ Failed (refunded)",
        "wd_ask": "💸 How much do you want to withdraw?\nSend a number (min {minwd} USDT).\nSend /menu to cancel.",
        "wd_bad_number": "❌ Please send a number only, for example 0.05",
        "wd_bad_dec": "❌ Use at most 3 decimal places, for example 0.055",
        "wd_min": "❌ Minimum withdrawal is {minwd} USDT.",
        "wd_nobal": "❌ Not enough balance. You have {bal} USDT.",
        "wd_confirm": "💸 <b>Withdraw {amount} USDT</b>\nDestination: your xRocket wallet\n\nConfirm?",
        "alert_wd_min": "Minimum withdrawal is {minwd} USDT.",
        "alert_session": "Session expired. Please start again.",
        "wd_processing": "⏳ Processing your withdrawal...",
        "wd_failed_api": "❌ Withdrawal failed: {reason}\n💳 Balance restored: <b>{bal} USDT</b>",
        "wd_pending": "⏳ xRocket is processing it. I will notify you when it is done.",
        "wd_ok": "✅ <b>Withdrawal successful!</b>\n{amount} USDT was sent to your xRocket wallet.\n💳 Balance: <b>{bal} USDT</b>",
        "wd_fail": "❌ <b>Withdrawal failed.</b>\n{amount} USDT was returned to your balance.\n💳 Balance: <b>{bal} USDT</b>",
    },
    "bn": {
        "lang_prompt": "🌐 Choose your language / ভাষা বাছাই করুন / 选择语言 / भाषा चुनें",
        "lang_set": "✅ ভাষা বাংলা সেট করা হয়েছে।",
        "btn_join": "🎟 লটারিতে জয়েন করুন",
        "btn_tickets": "📜 লেনদেন",
        "btn_withdraw": "💸 উইথড্র",
        "btn_lang": "🌐 ভাষা",
        "btn_back": "⬅️ মেনুতে ফিরুন",
        "btn_back_lot": "⬅️ লটারি তালিকায় ফিরুন",
        "btn_prev": "◀️ আগের",
        "btn_next": "পরের ▶️",
        "btn_yes_another": "✅ হ্যাঁ, আরেকটি নিব",
        "btn_no": "❌ না",
        "btn_pay_x": "💸 xRocket দিয়ে পে করুন",
        "btn_pay_bal": "💰 ব্যালেন্স দিয়ে পে ({bal} USDT)",
        "btn_cancel": "❌ বাতিল",
        "btn_pay_on": "💸 xRocket-এ পে করুন",
        "btn_check": "🔄 পেমেন্ট চেক করুন",
        "btn_show_user": "👤 @{u} দেখান",
        "btn_show_uid": "🔢 UID {uid} দেখান",
        "btn_confirm": "✅ নিশ্চিত করুন",
        "btn_join_next": "🎟 পরের রাউন্ডে জয়েন করুন",
        "menu_body": "🎰 <b>লাকি ডাইস লটারি</b>\n{sep}\n💰 আপনার ব্যালেন্স: <b>{bal} USDT</b>\n{sep}\n🍀 <b>ভাগ্য পরীক্ষা করবেন?</b>\nআপনার নম্বর বাছুন, আমাদের চ্যানেলে লাইভ ডাইস রোল দেখুন আর জিতে নিন আসল USDT পুরস্কার — প্রতি রাউন্ডে <b>৩ জন</b> বিজয়ী!\n\n🎲 স্বচ্ছ  •  🔴 লাইভ  •  💸 পুরস্কার সরাসরি আপনার ব্যালেন্সে\n\nএখন কোন লটারি চলছে দেখতে নিচে <b>লটারিতে জয়েন করুন</b> চাপুন।\n{sep}\n📢 চ্যানেল: {channel}",
        "menu_paused": "⏸ নতুন রাউন্ড সাময়িকভাবে বন্ধ আছে।",
        "join_title": "🎰 <b>আপনার লটারি বাছাই করুন</b>\n{sep}\n{rows}\n{sep}\n👇 যে লটারিতে জয়েন করবেন সেটার বাটনে চাপুন।",
        "join_row": "{tname}\n   💵 এন্ট্রি ফি: <b>{fee} USDT</b>\n   🏆 পুরস্কার: {prizes}\n   👥 প্লেয়ার: <b>{n}/{slots}</b>  •  ⏳ বাকি {left}",
        "join_row_off": "{tname}\n   ⏳ পরের রাউন্ড একটু পরেই শুরু হচ্ছে...",
        "no_round": "⏳ এখন কোনো লটারি খোলা নেই। একটু পরে আবার চেষ্টা করুন।",
        "max_tickets": "⚠️ এই রাউন্ডে আপনি সর্বোচ্চ <b>{max}</b>টি টিকিট নিয়ে ফেলেছেন।",
        "all_taken": "🔒 এখন সব নম্বর নেওয়া বা রিজার্ভ আছে। কিছুক্ষণ পর আবার চেষ্টা করুন।",
        "already_hold": "⚠️ আপনার কাছে ইতিমধ্যে টিকিট আছে: {held}\nআরেকটি নম্বর নিলে জেতার সম্ভাবনা বাড়বে, তবে প্রতি টিকিটের মূল্য <b>{fee} USDT</b>।\n\nচালিয়ে যাবেন?",
        "pick_number": "<b>{tname} • রাউন্ড #{id}</b> — আপনার লাকি নম্বর বাছাই করুন\n💵 এন্ট্রি ফি: <b>{fee} USDT</b>\n🏆 পুরস্কার: {prizes}\n⏳ শেষ: {ends}\n\nখালি নম্বর:",
        "reserved_msg": "✅ {tname}: নম্বর {emoji} <b>{num}</b> আপনার জন্য <b>{mins} মিনিট</b> রিজার্ভ করা হয়েছে।\n\n💵 এন্ট্রি ফি: <b>{fee} USDT</b>\nকীভাবে পে করবেন?",
        "alert_closed": "এই রাউন্ড বন্ধ হয়ে গেছে।",
        "alert_taken": "দুঃখিত, নম্বরটি এইমাত্র অন্য কেউ নিয়ে নিয়েছে।",
        "alert_max": "প্রতি রাউন্ডে সর্বোচ্চ {max}টি টিকিট।",
        "alert_reserve_expired": "আপনার রিজার্ভের সময় শেষ। আবার নম্বর বাছাই করুন।",
        "alert_creating": "Invoice তৈরি হচ্ছে...",
        "invoice_fail": "❌ Invoice তৈরি করা যায়নি। আবার চেষ্টা করুন।",
        "invoice_ready": "💸 <b>Invoice তৈরি হয়েছে</b>\n\n{tname}: টিকিট {emoji} <b>{num}</b> — <b>{fee} USDT</b>\n<b>{mins} মিনিটের</b> মধ্যে পে করুন। পেমেন্টের পর টিকিট নিজে থেকেই কনফার্ম হবে।",
        "alert_no_balance": "ব্যালেন্স যথেষ্ট নয়।",
        "alert_paid_bal": "ব্যালেন্স থেকে পেমেন্ট হয়েছে।",
        "alert_cancelled": "বাতিল করা হয়েছে।",
        "alert_processed": "এই পেমেন্ট আগেই প্রসেস হয়ে গেছে।",
        "alert_not_received": "⏳ এখনো পেমেন্ট আসেনি।",
        "entry_ok_choose": "🎉 <b>পেমেন্ট সফল!</b>\nআপনার টিকিট: {emoji} <b>{num}</b> ({tname} • রাউন্ড #{rid})\n👥 প্লেয়ার: {total}/{slots}\n\n👇 <b>শেষ ধাপ</b> — চ্যানেলের পোস্টে আপনার নাম কীভাবে দেখাবে?\n⏳ এই ধাপ শেষ করলেই আপনার জয়েন সম্পূর্ণ হবে (না বাছলে {wait} মিনিট পর নিজে থেকেই বাছাই হবে)।",
        "entry_ok_nouser": "🎉 <b>পেমেন্ট সফল!</b>\nআপনার টিকিট কনফার্ম: {emoji} <b>{num}</b> ({tname} • রাউন্ড #{rid})\n👥 প্লেয়ার: {total}/{slots}\n\nআপনার Telegram username নেই, তাই পোস্টে UID দেখানো হবে।\n✅ আপনার জয়েন সম্পূর্ণ!",
        "name_done": "✅ হয়ে গেছে! টিকিট {emoji} <b>{num}</b> দেখাবে <b>{shown}</b> নামে।\n🎟 আপনার জয়েন সম্পূর্ণ!",
        "alert_saved": "সেভ হয়েছে!",
        "alert_ticket_missing": "টিকিট পাওয়া যায়নি।",
        "alert_round_done": "এই রাউন্ড শেষ হয়ে গেছে।",
        "alert_no_username": "আপনার username নেই।",
        "late_refund": "⚠️ আপনার পেমেন্ট এসেছে, কিন্তু টিকিট <b>{num}</b> আর পাওয়া যায়নি (রাউন্ড বন্ধ বা নম্বর অন্য কেউ নিয়েছে)।\n💰 <b>{fee} USDT</b> আপনার ব্যালেন্সে যোগ করা হয়েছে।",
        "round_closed_dm": "⌛ <b>{tname} • রাউন্ড #{rid} বন্ধ হয়েছে</b>\n২৪ ঘণ্টায় যথেষ্ট প্লেয়ার জয়েন করেনি।\n💰 <b>{amount} USDT</b> আপনার ব্যালেন্সে ফেরত দেওয়া হয়েছে।\nএটা দিয়ে পরের রাউন্ডে জয়েন করতে পারবেন।",
        "win_dm": "🎉 <b>অভিনন্দন!</b>\nআপনি {tname} • রাউন্ড #{rid}-এ জিতেছেন:\n{wins}\n💰 <b>{prize} USDT</b> আপনার ব্যালেন্সে যোগ হয়েছে।\n💳 নতুন ব্যালেন্স: <b>{bal} USDT</b>",
        "lose_dm": "🎲 {tname} • রাউন্ড #{rid} শেষ হয়েছে।\nবিজয়ীরা:\n{winners}\nপরের বার ভাগ্য সহায় হোক! 🍀",
        "one_left_dm": "⏳ {tname} • রাউন্ড #{rid}-এ মাত্র <b>১টি</b> নম্বর বাকি! পূর্ণ হলেই লাইভ ড্র শুরু হবে।",
        "hist_title": "📜 <b>আপনার লেনদেন</b>\n{sep}\n{rows}\n{sep}\n📄 পেজ {page}/{pages}",
        "hist_empty": "📜 এখনো আপনার কোনো লেনদেন নেই।",
        "hist_ticket": "🎟 <b>{tname}</b> • রাউন্ড #{rid} • টিকিট {emoji}\n   ➖ {amount} USDT ({method})\n   {status}\n   🕒 {time}",
        "hist_win": "🏆 <b>পুরস্কার জিতেছেন</b> — {tname} • রাউন্ড #{rid} • টিকিট {emoji}\n   ➕ {amount} USDT\n   🕒 {time}",
        "hist_refund": "↩️ <b>রিফান্ড</b> — {tname} • রাউন্ড #{rid} বন্ধ হয়েছে\n   ➕ {amount} USDT\n   🕒 {time}",
        "hist_late": "↩️ <b>দেরিতে আসা পেমেন্টের রিফান্ড</b>\n   ➕ {amount} USDT\n   🕒 {time}",
        "hist_withdraw": "💸 <b>উইথড্র</b>\n   ➖ {amount} USDT\n   {status}\n   🕒 {time}",
        "hist_other": "🧾 {kind}: {amount} USDT\n   🕒 {time}",
        "method_bal": "ব্যালেন্স",
        "method_x": "xRocket",
        "st_ongoing": "🟢 চলমান",
        "st_end": "🏁 শেষ",
        "st_win": "🏆 WIN",
        "st_closed": "🏁 শেষ (রিফান্ড হয়েছে)",
        "st_wd_done": "✅ সম্পন্ন",
        "st_wd_pending": "⏳ প্রসেসিং",
        "st_wd_failed": "❌ ব্যর্থ (রিফান্ড হয়েছে)",
        "wd_ask": "💸 কত USDT উইথড্র করবেন?\nশুধু সংখ্যা লিখুন (ন্যূনতম {minwd} USDT)।\nবাতিল করতে /menu দিন।",
        "wd_bad_number": "❌ শুধু সংখ্যা লিখুন, যেমন 0.05",
        "wd_bad_dec": "❌ দশমিকের পর সর্বোচ্চ ৩ ঘর দিন, যেমন 0.055",
        "wd_min": "❌ ন্যূনতম উইথড্র {minwd} USDT।",
        "wd_nobal": "❌ ব্যালেন্স যথেষ্ট নয়। আপনার আছে {bal} USDT।",
        "wd_confirm": "💸 <b>{amount} USDT উইথড্র</b>\nগন্তব্য: আপনার xRocket ওয়ালেট\n\nনিশ্চিত করবেন?",
        "alert_wd_min": "ন্যূনতম উইথড্র {minwd} USDT।",
        "alert_session": "সেশন শেষ। আবার শুরু করুন।",
        "wd_processing": "⏳ আপনার উইথড্র প্রসেস হচ্ছে...",
        "wd_failed_api": "❌ উইথড্র হয়নি: {reason}\n💳 ব্যালেন্স ফেরত: <b>{bal} USDT</b>",
        "wd_pending": "⏳ xRocket প্রসেস করছে। শেষ হলে আপনাকে জানাব।",
        "wd_ok": "✅ <b>উইথড্র সফল!</b>\n{amount} USDT আপনার xRocket ওয়ালেটে পাঠানো হয়েছে।\n💳 ব্যালেন্স: <b>{bal} USDT</b>",
        "wd_fail": "❌ <b>উইথড্র ব্যর্থ।</b>\n{amount} USDT আপনার ব্যালেন্সে ফেরত দেওয়া হয়েছে।\n💳 ব্যালেন্স: <b>{bal} USDT</b>",
    },
}

TEXT_EXTRA = {
    "en": {
        "btn_ref": "👥 Refer",
        "btn_guide": "📖 Guide",
        "btn_share": "📤 Share my link",
        "btn_back_guide": "⬅️ Back to guide",
        "gb_join": "🎟 How to join",
        "gb_draw": "🎲 How winners are picked",
        "gb_prizes": "🏆 Lotteries & prizes",
        "gb_money": "💰 Balance & withdraw",
        "gb_refer": "👥 Refer & earn",
        "gb_faq": "❓ FAQ",
        "ref_page": "👥 <b>Refer & Earn</b>\n{sep}\n🔗 <b>Your personal link</b>\n<code>{link}</code>\n{sep}\n💸 You earn <b>{pct}%</b> of every ticket your referrals buy — added to your balance <b>after the round finishes</b>.\n\n🎟 Classic ticket ({fee_a} USDT) → <b>{ca} USDT</b>\n💎 Premium ticket ({fee_b} USDT) → <b>{cb} USDT</b>\n{sep}\n📊 <b>Your stats</b>\n👥 Total referrals: <b>{n}</b>\n💰 Total income: <b>{income} USDT</b>\n🎟 Tickets bought by your referrals: <b>{tickets}</b>\n⏳ In running rounds: <b>{ptk}</b> tickets (≈ <b>{pinc} USDT</b> once the rounds end)\n{sep}\n{refnote}",
        "ref_note": "ℹ️ Commission is counted on tickets paid with xRocket. A round that is closed and refunded pays no commission.",
        "ref_off": "\n⏸ The referral bonus is switched off at the moment.",
        "ref_share_text": "🎰 Lucky Dice Lottery — join with my link, pick your number and win USDT in live dice draws!",
        "ref_new": "🎉 <b>New referral!</b>\n{name} joined with your link.",
        "ref_paid_dm": "💰 <b>Referral bonus!</b>\n{tname} • Round #{rid} finished.\n🎟 Tickets bought by your referrals: {tickets}\n➕ <b>{amount} USDT</b> added to your balance.\n💳 Balance: <b>{bal} USDT</b>",
        "hist_ref": "👥 <b>Referral bonus</b> — {tname} • Round #{rid}\n   ➕ {amount} USDT\n   🕒 {time}",
        "guide_menu": "📖 <b>Guide</b>\n{sep}\nEverything about how our lottery works. Choose a topic:",
        "guide_join": "🎟 <b>How to join</b>\n{sep}\n1️⃣ Tap <b>Join Lottery</b> and choose <b>Classic</b> or <b>Premium</b>.\n2️⃣ Pick a free lucky number (1–{slots}). It is reserved for you for <b>{mins} minutes</b>.\n3️⃣ Pay with <b>xRocket</b> or with your <b>bot balance</b>.\n4️⃣ Choose how your name appears in the channel post (your @username or your ID). <b>Your join is complete after this step.</b>\n\n🎟 You can hold up to <b>{max}</b> tickets per round — more tickets, better chances.\n⏳ Every round stays open for 24 hours.",
        "guide_draw": "🎲 <b>How winners are picked</b>\n{sep}\nWhen all {slots} numbers are taken and every player has finished their name step, a short 1️⃣2️⃣3️⃣ countdown appears in the channel. Then the dice are rolled <b>live</b>:\n\n🥇 Dice 1 → that number is the 1st winner\n🥈 Dice 2 → that number is the 2nd winner\n🥉 Dice 3 → that number is the 3rd winner\n\n♻️ A number cannot win twice. If the same number comes up again, the dice is rolled again.\n✅ The dice are Telegram's own and are rolled in public in {channel}, so everything is transparent.\n⏳ If both lotteries fill up at the same time, they are drawn one after the other.",
        "guide_prizes": "🏆 <b>Lotteries & prizes</b>\n{sep}\n🎟 <b>Classic</b> — entry <b>{fee_a} USDT</b>\n{prizes_a}\n\n💎 <b>Premium</b> — entry <b>{fee_b} USDT</b>\n{prizes_b}\n\n🏆 3 winners in every round. Prizes are added to your bot balance right after the draw.\n⌛ If a round does not fill up within 24 hours, it is closed and every ticket is refunded to your balance.\n🔁 Both lotteries run at the same time and you can join both.",
        "guide_money": "💰 <b>Balance & withdraw</b>\n{sep}\n💳 Your balance holds your prizes, refunds and referral bonuses.\n🎟 You can use it to buy tickets.\n\n💸 <b>Withdraw</b>\nTap Withdraw, send the amount (min <b>{minwd} USDT</b>, up to 3 decimals) and confirm. The money is sent to your xRocket wallet.\n\n📜 <b>Transactions</b>\nEvery ticket, win, refund, referral bonus and withdrawal is listed there with its status:\n🟢 Ongoing  •  🏁 Ended  •  🏆 WIN",
        "guide_refer": "👥 <b>Refer & earn</b>\n{sep}\n1️⃣ Tap <b>Refer</b> and copy your personal link.\n2️⃣ Friends who start the bot with your link become your referrals.\n3️⃣ You earn <b>{pct}%</b> of every ticket they buy — paid <b>after that round finishes</b>.\n\n🎟 Classic ticket → <b>{ca} USDT</b>\n💎 Premium ticket → <b>{cb} USDT</b>\n\n📊 The Refer page shows your total referrals, total income, tickets bought by your referrals and tickets in rounds that are still running.\n{refnote}",
        "guide_faq": "❓ <b>FAQ</b>\n{sep}\n<b>My payment arrived late?</b>\nIf the number was taken or the round closed in the meantime, the fee is added to your balance.\n\n<b>The round did not fill up?</b>\nAfter 24 hours the round is closed and all tickets are refunded to your balance.\n\n<b>I did not choose my name?</b>\nAfter {wait} minutes it is chosen for you (your @username if you have one, otherwise your ID).\n\n<b>Where can I see the results?</b>\nIn {channel} and in your Transactions.\n\n<b>Can I play both lotteries?</b>\nYes, Classic and Premium run at the same time.",
    },
    "bn": {
        "btn_ref": "👥 রেফার",
        "btn_guide": "📖 গাইড",
        "btn_share": "📤 আমার লিংক শেয়ার করুন",
        "btn_back_guide": "⬅️ গাইডে ফিরুন",
        "gb_join": "🎟 কীভাবে জয়েন করবেন",
        "gb_draw": "🎲 বিজয়ী কীভাবে ঠিক হয়",
        "gb_prizes": "🏆 লটারি ও পুরস্কার",
        "gb_money": "💰 ব্যালেন্স ও উইথড্র",
        "gb_refer": "👥 রেফার ও আয়",
        "gb_faq": "❓ সাধারণ প্রশ্ন",
        "ref_page": "👥 <b>রেফার করুন, আয় করুন</b>\n{sep}\n🔗 <b>আপনার নিজস্ব লিংক</b>\n<code>{link}</code>\n{sep}\n💸 আপনার রেফার করা ইউজার প্রতি টিকিট কিনলে আপনি পাবেন <b>{pct}%</b> — রাউন্ড <b>শেষ হওয়ার পর</b> আপনার ব্যালেন্সে যোগ হবে।\n\n🎟 Classic টিকিট ({fee_a} USDT) → <b>{ca} USDT</b>\n💎 Premium টিকিট ({fee_b} USDT) → <b>{cb} USDT</b>\n{sep}\n📊 <b>আপনার হিসাব</b>\n👥 মোট রেফার: <b>{n}</b> জন\n💰 মোট ইনকাম: <b>{income} USDT</b>\n🎟 আপনার রেফার করা ইউজারদের কেনা মোট টিকিট: <b>{tickets}</b>\n⏳ চলমান রাউন্ডে (এখনো শেষ হয়নি): <b>{ptk}</b>টি টিকিট (রাউন্ড শেষ হলে ≈ <b>{pinc} USDT</b>)\n{sep}\n{refnote}",
        "ref_note": "ℹ️ কমিশন গণনা হয় xRocket দিয়ে পেমেন্ট করা টিকিটে। যে রাউন্ড বন্ধ হয়ে রিফান্ড হয়, সেটার কমিশন দেওয়া হয় না।",
        "ref_off": "\n⏸ রেফার বোনাস এখন সাময়িকভাবে বন্ধ আছে।",
        "ref_share_text": "🎰 লাকি ডাইস লটারি — আমার লিংক দিয়ে জয়েন করুন, নম্বর বাছুন আর লাইভ ডাইস ড্রতে জিতুন USDT!",
        "ref_new": "🎉 <b>নতুন রেফার!</b>\n{name} আপনার লিংক দিয়ে জয়েন করেছে।",
        "ref_paid_dm": "💰 <b>রেফার বোনাস!</b>\n{tname} • রাউন্ড #{rid} শেষ হয়েছে।\n🎟 আপনার রেফার করা ইউজারদের কেনা টিকিট: {tickets}\n➕ <b>{amount} USDT</b> আপনার ব্যালেন্সে যোগ হয়েছে।\n💳 ব্যালেন্স: <b>{bal} USDT</b>",
        "hist_ref": "👥 <b>রেফার বোনাস</b> — {tname} • রাউন্ড #{rid}\n   ➕ {amount} USDT\n   🕒 {time}",
        "guide_menu": "📖 <b>গাইড</b>\n{sep}\nআমাদের লটারি সিস্টেম কীভাবে কাজ করে সব এখানে। একটা বিষয় বাছাই করুন:",
        "guide_join": "🎟 <b>কীভাবে জয়েন করবেন</b>\n{sep}\n1️⃣ <b>লটারিতে জয়েন করুন</b> চেপে <b>Classic</b> বা <b>Premium</b> বাছাই করুন।\n2️⃣ একটা খালি লাকি নম্বর (1–{slots}) বাছুন। এটা আপনার জন্য <b>{mins} মিনিট</b> রিজার্ভ থাকবে।\n3️⃣ <b>xRocket</b> দিয়ে অথবা <b>বট ব্যালেন্স</b> দিয়ে পেমেন্ট করুন।\n4️⃣ চ্যানেলের পোস্টে আপনার নাম কীভাবে দেখাবে বাছুন (@username বা ID)। <b>এই ধাপ শেষ হলেই আপনার জয়েন সম্পূর্ণ।</b>\n\n🎟 প্রতি রাউন্ডে সর্বোচ্চ <b>{max}</b>টি টিকিট নিতে পারবেন — যত বেশি টিকিট, জেতার সম্ভাবনা তত বেশি।\n⏳ প্রতিটা রাউন্ড ২৪ ঘণ্টা খোলা থাকে।",
        "guide_draw": "🎲 <b>বিজয়ী কীভাবে ঠিক হয়</b>\n{sep}\n{slots}টা নম্বর পূর্ণ হলে এবং সবাই নাম বাছাইয়ের ধাপ শেষ করলে চ্যানেলে ছোট একটা 1️⃣2️⃣3️⃣ কাউন্টডাউন আসে। তারপর <b>লাইভ</b> ডাইস রোল হয়:\n\n🥇 ১ম ডাইস → যে নম্বর উঠবে সে ১ম বিজয়ী\n🥈 ২য় ডাইস → যে নম্বর উঠবে সে ২য় বিজয়ী\n🥉 ৩য় ডাইস → যে নম্বর উঠবে সে ৩য় বিজয়ী\n\n♻️ একই নম্বর দুইবার জিততে পারে না। আবার একই নম্বর এলে ডাইস আবার রোল হয়।\n✅ ডাইস Telegram-এর নিজস্ব এবং {channel} চ্যানেলে সবার সামনে রোল হয়, তাই সবকিছু স্বচ্ছ।\n⏳ দুই লটারি একসাথে পূর্ণ হলে একটার পর একটার ড্র হয়।",
        "guide_prizes": "🏆 <b>লটারি ও পুরস্কার</b>\n{sep}\n🎟 <b>Classic</b> — এন্ট্রি <b>{fee_a} USDT</b>\n{prizes_a}\n\n💎 <b>Premium</b> — এন্ট্রি <b>{fee_b} USDT</b>\n{prizes_b}\n\n🏆 প্রতি রাউন্ডে ৩ জন বিজয়ী। ড্রয়ের পরই পুরস্কার আপনার বট ব্যালেন্সে যোগ হয়।\n⌛ ২৪ ঘণ্টায় রাউন্ড পূর্ণ না হলে বন্ধ হয়ে যায় এবং সব টিকিটের টাকা আপনার ব্যালেন্সে ফেরত আসে।\n🔁 দুই লটারি একসাথে চলে, আপনি দুটোতেই জয়েন করতে পারবেন।",
        "guide_money": "💰 <b>ব্যালেন্স ও উইথড্র</b>\n{sep}\n💳 আপনার ব্যালেন্সে থাকে পুরস্কার, রিফান্ড ও রেফার বোনাস।\n🎟 এই ব্যালেন্স দিয়ে টিকিট কিনতে পারবেন।\n\n💸 <b>উইথড্র</b>\nউইথড্র চেপে পরিমাণ লিখুন (ন্যূনতম <b>{minwd} USDT</b>, দশমিকের পর ৩ ঘর পর্যন্ত) এবং নিশ্চিত করুন। টাকা আপনার xRocket ওয়ালেটে যাবে।\n\n📜 <b>লেনদেন</b>\nপ্রতিটা টিকিট, জয়, রিফান্ড, রেফার বোনাস ও উইথড্র স্ট্যাটাসসহ সেখানে দেখা যায়:\n🟢 চলমান  •  🏁 শেষ  •  🏆 WIN",
        "guide_refer": "👥 <b>রেফার ও আয়</b>\n{sep}\n1️⃣ <b>রেফার</b> চেপে আপনার নিজস্ব লিংক কপি করুন।\n2️⃣ বন্ধুরা আপনার লিংক দিয়ে বট শুরু করলে তারা আপনার রেফার হবে।\n3️⃣ তারা প্রতি টিকিট কিনলে আপনি পাবেন <b>{pct}%</b> — ওই রাউন্ড <b>শেষ হওয়ার পর</b>।\n\n🎟 Classic টিকিট → <b>{ca} USDT</b>\n💎 Premium টিকিট → <b>{cb} USDT</b>\n\n📊 রেফার পেজে দেখতে পারবেন মোট রেফার, মোট ইনকাম, রেফার করা ইউজারদের কেনা টিকিট এবং যে রাউন্ড এখনো চলছে সেখানের টিকিট।\n{refnote}",
        "guide_faq": "❓ <b>সাধারণ প্রশ্ন</b>\n{sep}\n<b>পেমেন্ট দেরিতে এলে?</b>\nইতিমধ্যে নম্বর অন্য কেউ নিলে বা রাউন্ড বন্ধ হলে টাকা আপনার ব্যালেন্সে যোগ হয়ে যায়।\n\n<b>রাউন্ড পূর্ণ না হলে?</b>\n২৪ ঘণ্টা পর রাউন্ড বন্ধ হয়ে সব টিকিটের টাকা ব্যালেন্সে ফেরত আসে।\n\n<b>নাম বাছাই না করলে?</b>\n{wait} মিনিট পর নিজে থেকেই বাছাই হয়ে যায় (username থাকলে @username, না থাকলে ID)।\n\n<b>ফলাফল কোথায় দেখব?</b>\n{channel} চ্যানেলে এবং আপনার লেনদেন পেজে।\n\n<b>দুই লটারিতেই খেলা যায়?</b>\nহ্যাঁ, Classic ও Premium একসাথে চলে।",
    },
}
TEXT["en"].update(TEXT_EXTRA["en"])
TEXT["bn"].update(TEXT_EXTRA["bn"])

TEXT_EXTRA2 = {
    "en": {
        "wd_off": "⏸ Withdrawals are paused for a short time. Please try again later.",
        "wd_off_alert": "Withdrawals are paused for a short time. Please try again later.",
        "wd_review": "🔍 <b>Withdrawal under review</b>\nFor your safety, this withdrawal needs a quick manual check by the admin. You will be notified as soon as it is decided — there is no need to send it again.",
        "wd_review_exists": "🔍 You already have a withdrawal waiting for review. Please wait for the admin's decision.",
        "wd_approved": "✅ Your withdrawal was approved by the admin.",
        "wd_rejected": "❌ Your withdrawal request was not approved and your balance is unchanged. If you think this is a mistake, please contact the admin.",
        "banned": "🚫 <b>Your account is restricted</b>\nYou cannot use this bot right now. If you think this is a mistake, please contact the admin.",
        "banned_alert": "🚫 Your account is restricted. Please contact the admin.",
        "strike_blocked": "⛔ <b>Joining paused</b>\nYou reserved numbers {n} times in a row without paying. Joining lotteries is paused for <b>{hours} hours</b>. Your balance, withdrawals and menu still work.",
        "join_blocked": "⛔ <b>Joining is paused for you</b>\nYou reserved numbers several times in a row without paying. You can join again in <b>{left}</b>. Your balance, withdrawals and menu still work.",
    },
    "bn": {
        "wd_off": "⏸ উইথড্র কিছুক্ষণের জন্য বন্ধ আছে। একটু পরে আবার চেষ্টা করুন।",
        "wd_off_alert": "উইথড্র কিছুক্ষণের জন্য বন্ধ আছে। একটু পরে আবার চেষ্টা করুন।",
        "wd_review": "🔍 <b>উইথড্র যাচাই চলছে</b>\nআপনার নিরাপত্তার জন্য এই উইথড্র অ্যাডমিন একবার নিজে দেখে নেবেন। সিদ্ধান্ত হলেই আপনাকে জানানো হবে — আবার পাঠানোর দরকার নেই।",
        "wd_review_exists": "🔍 আপনার একটা উইথড্র ইতিমধ্যে যাচাইয়ের অপেক্ষায় আছে। অ্যাডমিনের সিদ্ধান্ত পর্যন্ত অপেক্ষা করুন।",
        "wd_approved": "✅ অ্যাডমিন আপনার উইথড্র অনুমোদন করেছেন।",
        "wd_rejected": "❌ আপনার উইথড্র অনুরোধ অনুমোদন হয়নি, ব্যালেন্স আগের মতোই আছে। কোনো ভুল মনে হলে অ্যাডমিনের সাথে যোগাযোগ করুন।",
        "banned": "🚫 <b>আপনার অ্যাকাউন্ট সীমাবদ্ধ করা হয়েছে</b>\nএই মুহূর্তে আপনি বটটি ব্যবহার করতে পারবেন না। কোনো ভুল মনে হলে অ্যাডমিনের সাথে যোগাযোগ করুন।",
        "banned_alert": "🚫 আপনার অ্যাকাউন্ট সীমাবদ্ধ। অ্যাডমিনের সাথে যোগাযোগ করুন।",
        "strike_blocked": "⛔ <b>জয়েন সাময়িক বন্ধ</b>\nআপনি টানা {n} বার নম্বর রিজার্ভ করে পেমেন্ট করেননি। তাই <b>{hours} ঘণ্টা</b> লটারিতে জয়েন বন্ধ থাকবে। আপনার ব্যালেন্স, উইথড্র ও মেনু আগের মতোই চলবে।",
        "join_blocked": "⛔ <b>আপনার জন্য জয়েন সাময়িক বন্ধ</b>\nআপনি টানা কয়েকবার নম্বর রিজার্ভ করে পেমেন্ট করেননি। <b>{left}</b> পর আবার জয়েন করতে পারবেন। আপনার ব্যালেন্স, উইথড্র ও মেনু আগের মতোই চলবে।",
    },
}
TEXT["en"].update(TEXT_EXTRA2["en"])
TEXT["bn"].update(TEXT_EXTRA2["bn"])

TEXT_EXTRA3 = {
    "en": {
        "ban_dm": "🚫 <b>Your account has been restricted</b>\nYou can no longer use this bot. If you think this is a mistake, please contact the admin.",
        "unban_dm": "✅ <b>Your account is active again</b>\nThe restriction has been lifted and you can use the bot as usual. Tap /menu to continue.",
        "strike_warn": "⚠️ <b>Warning</b>\nYou have reserved numbers <b>{n}</b> times in a row without paying.\nIf this happens <b>once more</b>, joining lotteries will be paused for <b>{hours} hours</b>.\n\nOnly reserve a number if you are ready to pay now. Continue?",
        "btn_continue": "✅ Continue",
    },
    "bn": {
        "ban_dm": "🚫 <b>আপনার অ্যাকাউন্ট সীমাবদ্ধ করা হয়েছে</b>\nআপনি আর এই বট ব্যবহার করতে পারবেন না। কোনো ভুল মনে হলে অ্যাডমিনের সাথে যোগাযোগ করুন।",
        "unban_dm": "✅ <b>আপনার অ্যাকাউন্ট আবার চালু হয়েছে</b>\nসীমাবদ্ধতা তুলে নেওয়া হয়েছে, আপনি আগের মতো বট ব্যবহার করতে পারবেন। চালিয়ে যেতে /menu চাপুন।",
        "strike_warn": "⚠️ <b>সতর্কতা</b>\nআপনি টানা <b>{n}</b> বার নম্বর রিজার্ভ করে পেমেন্ট করেননি।\nআরও <b>একবার</b> এমন হলে <b>{hours} ঘণ্টা</b> লটারিতে জয়েন বন্ধ থাকবে।\n\nপেমেন্ট করতে প্রস্তুত থাকলেই নম্বর রিজার্ভ করুন। চালিয়ে যাবেন?",
        "btn_continue": "✅ চালিয়ে যান",
    },
}
TEXT["en"].update(TEXT_EXTRA3["en"])
TEXT["bn"].update(TEXT_EXTRA3["bn"])


TEXT_ZH = {
    "lang_prompt": "🌐 Choose your language / ভাষা বাছাই করুন / 选择语言 / भाषा चुनें",
    "lang_set": "✅ 语言已设置为简体中文。",
    "btn_join": "🎟 参加抽奖",
    "btn_tickets": "📜 交易记录",
    "btn_withdraw": "💸 提现",
    "btn_lang": "🌐 语言",
    "btn_back": "⬅️ 返回菜单",
    "btn_back_lot": "⬅️ 返回抽奖列表",
    "btn_prev": "◀️ 上一页",
    "btn_next": "下一页 ▶️",
    "btn_yes_another": "✅ 是的，再买一张",
    "btn_no": "❌ 否",
    "btn_pay_x": "💸 使用 xRocket 支付",
    "btn_pay_bal": "💰 使用余额支付（{bal} USDT）",
    "btn_cancel": "❌ 取消",
    "btn_pay_on": "💸 前往 xRocket 支付",
    "btn_check": "🔄 检查付款",
    "btn_show_user": "👤 显示 @{u}",
    "btn_show_uid": "🔢 显示 UID {uid}",
    "btn_confirm": "✅ 确认",
    "btn_join_next": "🎟 参加下一轮",
    "btn_continue": "✅ 继续",
    "menu_body": "🎰 <b>幸运骰子抽奖</b>\n{sep}\n💰 您的余额：<b>{bal} USDT</b>\n{sep}\n🍀 <b>想试试手气吗？</b>\n选一个号码，在频道里观看骰子实时滚动，赢取真正的 USDT 奖金——每轮 <b>3 位</b>获奖者！\n\n🎲 公平  •  🔴 直播  •  💸 奖金直接进入您的余额\n\n点击下方的<b>参加抽奖</b>，查看当前正在进行的抽奖。\n{sep}\n📢 频道：{channel}",
    "menu_paused": "⏸ 新一轮抽奖暂时暂停。",
    "join_title": "🎰 <b>请选择抽奖</b>\n{sep}\n{rows}\n{sep}\n👇 点击您想参加的抽奖。",
    "join_row": "{tname}\n   💵 参与费用：<b>{fee} USDT</b>\n   🏆 奖金：{prizes}\n   👥 玩家：<b>{n}/{slots}</b>  •  ⏳ 剩余 {left}",
    "join_row_off": "{tname}\n   ⏳ 下一轮即将开始……",
    "no_round": "⏳ 目前没有开放的抽奖，请稍后再试。",
    "max_tickets": "⚠️ 您在本轮已持有最多 <b>{max}</b> 张票。",
    "all_taken": "🔒 所有号码目前都已被占用或预留，请几分钟后再试。",
    "already_hold": "⚠️ 您已持有号码：{held}\n多买一个号码可以增加中奖机会，但每张票需 <b>{fee} USDT</b>。\n\n是否继续？",
    "pick_number": "<b>{tname} • 第 #{id} 轮</b> — 选择您的幸运号码\n💵 参与费用：<b>{fee} USDT</b>\n🏆 奖金：{prizes}\n⏳ 截止：{ends}\n\n可选号码：",
    "reserved_msg": "✅ {tname}：号码 {emoji} <b>{num}</b> 已为您预留 <b>{mins} 分钟</b>。\n\n💵 参与费用：<b>{fee} USDT</b>\n请选择支付方式：",
    "alert_closed": "本轮已结束。",
    "alert_taken": "抱歉，这个号码刚刚被别人选走了。",
    "alert_max": "每轮最多 {max} 张票。",
    "alert_reserve_expired": "您的预留已过期，请重新选择号码。",
    "alert_creating": "正在创建账单……",
    "invoice_fail": "❌ 无法创建账单，请重试。",
    "invoice_ready": "💸 <b>账单已生成</b>\n\n{tname}：号码 {emoji} <b>{num}</b> — <b>{fee} USDT</b>\n请在 <b>{mins} 分钟</b>内付款。付款后您的号码将自动确认。",
    "alert_no_balance": "余额不足。",
    "alert_paid_bal": "已用余额支付。",
    "alert_cancelled": "已取消。",
    "alert_processed": "该付款已处理。",
    "alert_not_received": "⏳ 尚未收到付款。",
    "entry_ok_choose": "🎉 <b>付款成功！</b>\n您的号码：{emoji} <b>{num}</b>（{tname} • 第 #{rid} 轮）\n👥 玩家：{total}/{slots}\n\n👇 <b>最后一步</b> — 您的名字在频道帖子中如何显示？\n⏳ 完成此步骤后才算成功参加（若不选择，将在 {wait} 分钟后自动选择）。",
    "entry_ok_nouser": "🎉 <b>付款成功！</b>\n您的号码已确认：{emoji} <b>{num}</b>（{tname} • 第 #{rid} 轮）\n👥 玩家：{total}/{slots}\n\n您没有 Telegram 用户名，因此帖子中将显示您的 UID。\n✅ 您已成功参加！",
    "name_done": "✅ 完成！号码 {emoji} <b>{num}</b> 将显示为 <b>{shown}</b>。\n🎟 您已成功参加！",
    "alert_saved": "已保存！",
    "alert_ticket_missing": "未找到该号码。",
    "alert_round_done": "本轮已结束。",
    "alert_no_username": "您没有用户名。",
    "late_refund": "⚠️ 您的付款已到账，但号码 <b>{num}</b> 已不可用（本轮已结束或号码被占用）。\n💰 <b>{fee} USDT</b> 已添加到您的余额。",
    "round_closed_dm": "⌛ <b>{tname} • 第 #{rid} 轮已关闭</b>\n24 小时内参与人数不足。\n💰 <b>{amount} USDT</b> 已退还到您的余额。\n您可以用它参加下一轮。",
    "win_dm": "🎉 <b>恭喜！</b>\n您在 {tname} • 第 #{rid} 轮中获奖：\n{wins}\n💰 <b>{prize} USDT</b> 已添加到您的余额。\n💳 新余额：<b>{bal} USDT</b>",
    "lose_dm": "🎲 {tname} • 第 #{rid} 轮已结束。\n获奖者：\n{winners}\n祝您下次好运！🍀",
    "one_left_dm": "⏳ {tname} • 第 #{rid} 轮仅剩 <b>1 个名额</b>！满员后将立即开始直播抽奖。",
    "hist_title": "📜 <b>您的交易记录</b>\n{sep}\n{rows}\n{sep}\n📄 第 {page}/{pages} 页",
    "hist_empty": "📜 您还没有任何交易记录。",
    "hist_ticket": "🎟 <b>{tname}</b> • 第 #{rid} 轮 • 号码 {emoji}\n   ➖ {amount} USDT（{method}）\n   {status}\n   🕒 {time}",
    "hist_win": "🏆 <b>中奖</b> — {tname} • 第 #{rid} 轮 • 号码 {emoji}\n   ➕ {amount} USDT\n   🕒 {time}",
    "hist_refund": "↩️ <b>退款</b> — {tname} • 第 #{rid} 轮已关闭\n   ➕ {amount} USDT\n   🕒 {time}",
    "hist_late": "↩️ <b>迟到付款退款</b>\n   ➕ {amount} USDT\n   🕒 {time}",
    "hist_withdraw": "💸 <b>提现</b>\n   ➖ {amount} USDT\n   {status}\n   🕒 {time}",
    "hist_other": "🧾 {kind}: {amount} USDT\n   🕒 {time}",
    "method_bal": "余额",
    "method_x": "xRocket",
    "st_ongoing": "🟢 进行中",
    "st_end": "🏁 已结束",
    "st_win": "🏆 中奖",
    "st_closed": "🏁 已结束（已退款）",
    "st_wd_done": "✅ 已完成",
    "st_wd_pending": "⏳ 处理中",
    "st_wd_failed": "❌ 失败（已退款）",
    "wd_ask": "💸 您想提现多少 USDT？\n请发送一个数字（最低 {minwd} USDT）。\n发送 /menu 取消。",
    "wd_bad_number": "❌ 请只发送数字，例如 0.05",
    "wd_bad_dec": "❌ 小数最多 3 位，例如 0.055",
    "wd_min": "❌ 最低提现金额为 {minwd} USDT。",
    "wd_nobal": "❌ 余额不足。您的余额为 {bal} USDT。",
    "wd_confirm": "💸 <b>提现 {amount} USDT</b>\n收款账户：您的 xRocket 钱包\n\n确认吗？",
    "alert_wd_min": "最低提现金额为 {minwd} USDT。",
    "alert_session": "会话已过期，请重新开始。",
    "wd_processing": "⏳ 正在处理您的提现……",
    "wd_failed_api": "❌ 提现失败：{reason}\n💳 余额已恢复：<b>{bal} USDT</b>",
    "wd_pending": "⏳ xRocket 正在处理，完成后我会通知您。",
    "wd_ok": "✅ <b>提现成功！</b>\n{amount} USDT 已发送到您的 xRocket 钱包。\n💳 余额：<b>{bal} USDT</b>",
    "wd_fail": "❌ <b>提现失败。</b>\n{amount} USDT 已退回您的余额。\n💳 余额：<b>{bal} USDT</b>",
    "btn_ref": "👥 推荐",
    "btn_guide": "📖 指南",
    "btn_share": "📤 分享我的链接",
    "btn_back_guide": "⬅️ 返回指南",
    "gb_join": "🎟 如何参加",
    "gb_draw": "🎲 如何选出获奖者",
    "gb_prizes": "🏆 抽奖与奖金",
    "gb_money": "💰 余额与提现",
    "gb_refer": "👥 推荐赚钱",
    "gb_faq": "❓ 常见问题",
    "ref_page": "👥 <b>推荐赚钱</b>\n{sep}\n🔗 <b>您的专属链接</b>\n<code>{link}</code>\n{sep}\n💸 您推荐的用户每买一张票，您就能获得票价的 <b>{pct}%</b>——在该轮<b>结束后</b>加入您的余额。\n\n🎟 经典票（{fee_a} USDT）→ <b>{ca} USDT</b>\n💎 尊享票（{fee_b} USDT）→ <b>{cb} USDT</b>\n{sep}\n📊 <b>您的数据</b>\n👥 推荐总人数：<b>{n}</b>\n💰 总收入：<b>{income} USDT</b>\n🎟 被推荐用户购买的票数：<b>{tickets}</b>\n⏳ 进行中的轮次：<b>{ptk}</b> 张票（轮次结束后约 <b>{pinc} USDT</b>）\n{sep}\n{refnote}",
    "ref_note": "ℹ️ 佣金按通过 xRocket 支付的票计算。已关闭并退款的轮次不发放佣金。",
    "ref_off": "\n⏸ 推荐奖励目前已关闭。",
    "ref_share_text": "🎰 幸运骰子抽奖——通过我的链接加入，选号码，在直播骰子抽奖中赢取 USDT！",
    "ref_new": "🎉 <b>新的推荐！</b>\n{name} 通过您的链接加入了。",
    "ref_paid_dm": "💰 <b>推荐奖励！</b>\n{tname} • 第 #{rid} 轮已结束。\n🎟 被推荐用户购买的票数：{tickets}\n➕ <b>{amount} USDT</b> 已添加到您的余额。\n💳 余额：<b>{bal} USDT</b>",
    "hist_ref": "👥 <b>推荐奖励</b> — {tname} • 第 #{rid} 轮\n   ➕ {amount} USDT\n   🕒 {time}",
    "guide_menu": "📖 <b>指南</b>\n{sep}\n了解我们抽奖的全部玩法。请选择一个主题：",
    "guide_join": "🎟 <b>如何参加</b>\n{sep}\n1️⃣ 点击<b>参加抽奖</b>，选择<b>经典</b>或<b>尊享</b>。\n2️⃣ 选择一个空闲的幸运号码（1–{slots}），将为您预留 <b>{mins} 分钟</b>。\n3️⃣ 使用 <b>xRocket</b> 或您的<b>机器人余额</b>支付。\n4️⃣ 选择名字在频道帖子中的显示方式（@用户名或 ID）。<b>完成此步骤后才算成功参加。</b>\n\n🎟 每轮最多可持有 <b>{max}</b> 张票——票越多，机会越大。\n⏳ 每一轮开放 24 小时。",
    "guide_draw": "🎲 <b>如何选出获奖者</b>\n{sep}\n当 {slots} 个号码全部被占用，且每位玩家都完成了名字选择后，频道里会出现简短的 1️⃣2️⃣3️⃣ 倒计时。随后骰子会<b>实时</b>滚动：\n\n🥇 第 1 个骰子 → 该号码为第 1 名\n🥈 第 2 个骰子 → 该号码为第 2 名\n🥉 第 3 个骰子 → 该号码为第 3 名\n\n♻️ 同一号码不能中奖两次。如果再次出现相同号码，将重新掷骰子。\n✅ 骰子为 Telegram 官方骰子，并在 {channel} 公开掷出，全程透明。\n⏳ 如果两个抽奖同时满员，将依次开奖。",
    "guide_prizes": "🏆 <b>抽奖与奖金</b>\n{sep}\n🎟 <b>经典</b> — 参与费用 <b>{fee_a} USDT</b>\n{prizes_a}\n\n💎 <b>尊享</b> — 参与费用 <b>{fee_b} USDT</b>\n{prizes_b}\n\n🏆 每轮 3 位获奖者。开奖后奖金立即加入您的机器人余额。\n⌛ 如果一轮在 24 小时内未满员，将被关闭，所有票款退还到您的余额。\n🔁 两个抽奖同时进行，您可以两个都参加。",
    "guide_money": "💰 <b>余额与提现</b>\n{sep}\n💳 您的余额包含奖金、退款和推荐奖励。\n🎟 您可以用余额购买票。\n\n💸 <b>提现</b>\n点击提现，发送金额（最低 <b>{minwd} USDT</b>，最多 3 位小数）并确认。款项将发送到您的 xRocket 钱包。\n\n📜 <b>交易记录</b>\n每一张票、中奖、退款、推荐奖励和提现都会连同状态列在那里：\n🟢 进行中  •  🏁 已结束  •  🏆 中奖",
    "guide_refer": "👥 <b>推荐赚钱</b>\n{sep}\n1️⃣ 点击<b>推荐</b>，复制您的专属链接。\n2️⃣ 朋友通过您的链接启动机器人，就成为您的推荐用户。\n3️⃣ 他们每买一张票，您就能获得 <b>{pct}%</b>——在<b>该轮结束后</b>发放。\n\n🎟 经典票 → <b>{ca} USDT</b>\n💎 尊享票 → <b>{cb} USDT</b>\n\n📊 推荐页面会显示推荐总人数、总收入、被推荐用户购买的票数，以及仍在进行中的轮次里的票数。\n{refnote}",
    "guide_faq": "❓ <b>常见问题</b>\n{sep}\n<b>我的付款到账晚了？</b>\n如果这期间号码已被占用或本轮已关闭，票款会加入您的余额。\n\n<b>这一轮没有满员？</b>\n24 小时后该轮关闭，所有票款退还到您的余额。\n\n<b>我没有选择名字显示方式？</b>\n{wait} 分钟后会自动为您选择（有用户名则用 @用户名，否则用 ID）。\n\n<b>在哪里查看结果？</b>\n在 {channel} 频道和您的交易记录中。\n\n<b>可以两个抽奖都参加吗？</b>\n可以，经典和尊享同时进行。",
    "wd_off": "⏸ 提现暂时暂停，请稍后再试。",
    "wd_off_alert": "提现暂时暂停，请稍后再试。",
    "wd_review": "🔍 <b>提现审核中</b>\n为了您的资金安全，这笔提现需要管理员进行一次人工检查。一有结果会立即通知您——无需重复提交。",
    "wd_review_exists": "🔍 您已有一笔提现正在等待审核，请等待管理员的决定。",
    "wd_approved": "✅ 管理员已批准您的提现。",
    "wd_rejected": "❌ 您的提现申请未获批准，余额保持不变。如果您认为有误，请联系管理员。",
    "banned": "🚫 <b>您的账户已被限制</b>\n您目前无法使用此机器人。如果您认为有误，请联系管理员。",
    "banned_alert": "🚫 您的账户已被限制，请联系管理员。",
    "strike_blocked": "⛔ <b>暂停参加</b>\n您已连续 {n} 次预留号码但未付款。参加抽奖将暂停 <b>{hours} 小时</b>。您的余额、提现和菜单仍可正常使用。",
    "join_blocked": "⛔ <b>您暂时无法参加</b>\n您已连续多次预留号码但未付款。<b>{left}</b> 后可再次参加。您的余额、提现和菜单仍可正常使用。",
    "ban_dm": "🚫 <b>您的账户已被限制</b>\n您无法再使用此机器人。如果您认为有误，请联系管理员。",
    "unban_dm": "✅ <b>您的账户已恢复</b>\n限制已解除，您可以像往常一样使用机器人。点击 /menu 继续。",
    "strike_warn": "⚠️ <b>警告</b>\n您已连续 <b>{n}</b> 次预留号码但未付款。\n如果<b>再发生一次</b>，参加抽奖将暂停 <b>{hours} 小时</b>。\n\n只有在准备好立即付款时才预留号码。是否继续？",
}


TEXT_HI = {
    "lang_prompt": "🌐 Choose your language / ভাষা বাছাই করুন / 选择语言 / भाषा चुनें",
    "lang_set": "✅ भाषा हिन्दी सेट कर दी गई है।",
    "btn_join": "🎟 लॉटरी में शामिल हों",
    "btn_tickets": "📜 लेन-देन",
    "btn_withdraw": "💸 निकासी",
    "btn_lang": "🌐 भाषा",
    "btn_back": "⬅️ मेनू पर वापस",
    "btn_back_lot": "⬅️ लॉटरी सूची पर वापस",
    "btn_prev": "◀️ पिछला",
    "btn_next": "अगला ▶️",
    "btn_yes_another": "✅ हाँ, एक और लूँगा",
    "btn_no": "❌ नहीं",
    "btn_pay_x": "💸 xRocket से भुगतान करें",
    "btn_pay_bal": "💰 बैलेंस से भुगतान ({bal} USDT)",
    "btn_cancel": "❌ रद्द करें",
    "btn_pay_on": "💸 xRocket पर भुगतान करें",
    "btn_check": "🔄 भुगतान जाँचें",
    "btn_show_user": "👤 @{u} दिखाएँ",
    "btn_show_uid": "🔢 UID {uid} दिखाएँ",
    "btn_confirm": "✅ पुष्टि करें",
    "btn_join_next": "🎟 अगले राउंड में शामिल हों",
    "btn_continue": "✅ जारी रखें",
    "menu_body": "🎰 <b>लकी डाइस लॉटरी</b>\n{sep}\n💰 आपका बैलेंस: <b>{bal} USDT</b>\n{sep}\n🍀 <b>क्या किस्मत आज़माना चाहते हैं?</b>\nअपना नंबर चुनें, हमारे चैनल में लाइव डाइस रोल देखें और असली USDT इनाम जीतें — हर राउंड में <b>3 विजेता</b>!\n\n🎲 निष्पक्ष  •  🔴 लाइव  •  💸 इनाम सीधे आपके बैलेंस में\n\nअभी कौन-सी लॉटरी चल रही है यह देखने के लिए नीचे <b>लॉटरी में शामिल हों</b> दबाएँ।\n{sep}\n📢 चैनल: {channel}",
    "menu_paused": "⏸ नए राउंड अभी के लिए रोके गए हैं।",
    "join_title": "🎰 <b>अपनी लॉटरी चुनें</b>\n{sep}\n{rows}\n{sep}\n👇 जिस लॉटरी में शामिल होना है उसे दबाएँ।",
    "join_row": "{tname}\n   💵 प्रवेश शुल्क: <b>{fee} USDT</b>\n   🏆 इनाम: {prizes}\n   👥 खिलाड़ी: <b>{n}/{slots}</b>  •  ⏳ {left} बाकी",
    "join_row_off": "{tname}\n   ⏳ अगला राउंड जल्द शुरू हो रहा है...",
    "no_round": "⏳ अभी कोई लॉटरी खुली नहीं है। कृपया थोड़ी देर बाद फिर कोशिश करें।",
    "max_tickets": "⚠️ इस राउंड में आपके पास पहले से अधिकतम <b>{max}</b> टिकट हैं।",
    "all_taken": "🔒 अभी सभी नंबर लिए जा चुके हैं या रिज़र्व हैं। कुछ मिनट बाद फिर कोशिश करें।",
    "already_hold": "⚠️ आपके पास पहले से टिकट हैं: {held}\nएक और नंबर लेने से जीतने की संभावना बढ़ती है, लेकिन हर टिकट की कीमत <b>{fee} USDT</b> है।\n\nक्या आप जारी रखना चाहते हैं?",
    "pick_number": "<b>{tname} • राउंड #{id}</b> — अपना लकी नंबर चुनें\n💵 प्रवेश शुल्क: <b>{fee} USDT</b>\n🏆 इनाम: {prizes}\n⏳ समाप्ति: {ends}\n\nखाली नंबर:",
    "reserved_msg": "✅ {tname}: नंबर {emoji} <b>{num}</b> आपके लिए <b>{mins} मिनट</b> के लिए रिज़र्व है।\n\n💵 प्रवेश शुल्क: <b>{fee} USDT</b>\nभुगतान का तरीका चुनें:",
    "alert_closed": "यह राउंड बंद हो चुका है।",
    "alert_taken": "माफ़ करें, यह नंबर अभी-अभी किसी और ने ले लिया।",
    "alert_max": "प्रति राउंड अधिकतम {max} टिकट।",
    "alert_reserve_expired": "आपका रिज़र्वेशन समाप्त हो गया। कृपया फिर से नंबर चुनें।",
    "alert_creating": "इनवॉइस बनाया जा रहा है...",
    "invoice_fail": "❌ इनवॉइस नहीं बन सका। कृपया फिर कोशिश करें।",
    "invoice_ready": "💸 <b>इनवॉइस तैयार है</b>\n\n{tname}: टिकट {emoji} <b>{num}</b> — <b>{fee} USDT</b>\n<b>{mins} मिनट</b> के भीतर भुगतान करें। भुगतान के बाद आपका टिकट अपने आप कन्फ़र्म हो जाएगा।",
    "alert_no_balance": "बैलेंस पर्याप्त नहीं है।",
    "alert_paid_bal": "बैलेंस से भुगतान हो गया।",
    "alert_cancelled": "रद्द कर दिया गया।",
    "alert_processed": "यह भुगतान पहले ही प्रोसेस हो चुका है।",
    "alert_not_received": "⏳ भुगतान अभी नहीं मिला।",
    "entry_ok_choose": "🎉 <b>भुगतान मिल गया!</b>\nआपका टिकट: {emoji} <b>{num}</b> ({tname} • राउंड #{rid})\n👥 खिलाड़ी: {total}/{slots}\n\n👇 <b>आख़िरी चरण</b> — चैनल पोस्ट में आपका नाम कैसे दिखे?\n⏳ इस चरण के बाद ही आपकी एंट्री पूरी होगी (न चुनने पर {wait} मिनट बाद अपने आप चुन लिया जाएगा)।",
    "entry_ok_nouser": "🎉 <b>भुगतान मिल गया!</b>\nआपका टिकट कन्फ़र्म हो गया: {emoji} <b>{num}</b> ({tname} • राउंड #{rid})\n👥 खिलाड़ी: {total}/{slots}\n\nआपका Telegram username नहीं है, इसलिए पोस्ट में आपकी UID दिखाई जाएगी।\n✅ आपकी एंट्री पूरी हो गई!",
    "name_done": "✅ हो गया! टिकट {emoji} <b>{num}</b> <b>{shown}</b> नाम से दिखेगा।\n🎟 आपकी एंट्री पूरी हो गई!",
    "alert_saved": "सेव हो गया!",
    "alert_ticket_missing": "टिकट नहीं मिला।",
    "alert_round_done": "यह राउंड पहले ही समाप्त हो चुका है।",
    "alert_no_username": "आपका username नहीं है।",
    "late_refund": "⚠️ आपका भुगतान आ गया, लेकिन टिकट <b>{num}</b> अब उपलब्ध नहीं है (राउंड बंद हो गया या नंबर किसी और ने ले लिया)।\n💰 <b>{fee} USDT</b> आपके बैलेंस में जोड़ दिए गए हैं।",
    "round_closed_dm": "⌛ <b>{tname} • राउंड #{rid} बंद हो गया</b>\n24 घंटे में पर्याप्त खिलाड़ी शामिल नहीं हुए।\n💰 <b>{amount} USDT</b> आपके बैलेंस में वापस कर दिए गए हैं।\nआप इन्हें अगले राउंड में इस्तेमाल कर सकते हैं।",
    "win_dm": "🎉 <b>बधाई हो!</b>\nआपने {tname} • राउंड #{rid} में जीत हासिल की:\n{wins}\n💰 <b>{prize} USDT</b> आपके बैलेंस में जोड़ दिए गए हैं।\n💳 नया बैलेंस: <b>{bal} USDT</b>",
    "lose_dm": "🎲 {tname} • राउंड #{rid} समाप्त हो गया।\nविजेता:\n{winners}\nअगली बार किस्मत साथ दे! 🍀",
    "one_left_dm": "⏳ {tname} • राउंड #{rid} में सिर्फ़ <b>1 जगह</b> बाकी है! भरते ही लाइव ड्रॉ शुरू हो जाएगा।",
    "hist_title": "📜 <b>आपके लेन-देन</b>\n{sep}\n{rows}\n{sep}\n📄 पेज {page}/{pages}",
    "hist_empty": "📜 अभी तक आपका कोई लेन-देन नहीं है।",
    "hist_ticket": "🎟 <b>{tname}</b> • राउंड #{rid} • टिकट {emoji}\n   ➖ {amount} USDT ({method})\n   {status}\n   🕒 {time}",
    "hist_win": "🏆 <b>इनाम जीता</b> — {tname} • राउंड #{rid} • टिकट {emoji}\n   ➕ {amount} USDT\n   🕒 {time}",
    "hist_refund": "↩️ <b>रिफ़ंड</b> — {tname} • राउंड #{rid} बंद हुआ\n   ➕ {amount} USDT\n   🕒 {time}",
    "hist_late": "↩️ <b>देर से आए भुगतान का रिफ़ंड</b>\n   ➕ {amount} USDT\n   🕒 {time}",
    "hist_withdraw": "💸 <b>निकासी</b>\n   ➖ {amount} USDT\n   {status}\n   🕒 {time}",
    "hist_other": "🧾 {kind}: {amount} USDT\n   🕒 {time}",
    "method_bal": "बैलेंस",
    "method_x": "xRocket",
    "st_ongoing": "🟢 जारी",
    "st_end": "🏁 समाप्त",
    "st_win": "🏆 जीत",
    "st_closed": "🏁 समाप्त (रिफ़ंड हुआ)",
    "st_wd_done": "✅ पूरा हुआ",
    "st_wd_pending": "⏳ प्रोसेस हो रहा है",
    "st_wd_failed": "❌ विफल (रिफ़ंड हुआ)",
    "wd_ask": "💸 आप कितने USDT निकालना चाहते हैं?\nसिर्फ़ संख्या भेजें (न्यूनतम {minwd} USDT)।\nरद्द करने के लिए /menu भेजें।",
    "wd_bad_number": "❌ कृपया सिर्फ़ संख्या भेजें, जैसे 0.05",
    "wd_bad_dec": "❌ दशमलव के बाद अधिकतम 3 अंक रखें, जैसे 0.055",
    "wd_min": "❌ न्यूनतम निकासी {minwd} USDT है।",
    "wd_nobal": "❌ बैलेंस पर्याप्त नहीं है। आपके पास {bal} USDT हैं।",
    "wd_confirm": "💸 <b>{amount} USDT की निकासी</b>\nगंतव्य: आपका xRocket वॉलेट\n\nपुष्टि करें?",
    "alert_wd_min": "न्यूनतम निकासी {minwd} USDT है।",
    "alert_session": "सेशन समाप्त हो गया। कृपया फिर से शुरू करें।",
    "wd_processing": "⏳ आपकी निकासी प्रोसेस हो रही है...",
    "wd_failed_api": "❌ निकासी विफल: {reason}\n💳 बैलेंस वापस मिल गया: <b>{bal} USDT</b>",
    "wd_pending": "⏳ xRocket इसे प्रोसेस कर रहा है। पूरा होते ही मैं आपको बताऊँगा।",
    "wd_ok": "✅ <b>निकासी सफल!</b>\n{amount} USDT आपके xRocket वॉलेट में भेज दिए गए हैं।\n💳 बैलेंस: <b>{bal} USDT</b>",
    "wd_fail": "❌ <b>निकासी विफल।</b>\n{amount} USDT आपके बैलेंस में वापस कर दिए गए हैं।\n💳 बैलेंस: <b>{bal} USDT</b>",
    "btn_ref": "👥 रेफ़र",
    "btn_guide": "📖 गाइड",
    "btn_share": "📤 मेरा लिंक शेयर करें",
    "btn_back_guide": "⬅️ गाइड पर वापस",
    "gb_join": "🎟 शामिल कैसे हों",
    "gb_draw": "🎲 विजेता कैसे चुने जाते हैं",
    "gb_prizes": "🏆 लॉटरी और इनाम",
    "gb_money": "💰 बैलेंस और निकासी",
    "gb_refer": "👥 रेफ़र करें और कमाएँ",
    "gb_faq": "❓ अक्सर पूछे जाने वाले प्रश्न",
    "ref_page": "👥 <b>रेफ़र करें, कमाएँ</b>\n{sep}\n🔗 <b>आपका निजी लिंक</b>\n<code>{link}</code>\n{sep}\n💸 आपके रेफ़र किए गए यूज़र हर टिकट खरीदें तो आपको मिलेगा टिकट की कीमत का <b>{pct}%</b> — राउंड <b>समाप्त होने के बाद</b> आपके बैलेंस में जुड़ जाएगा।\n\n🎟 क्लासिक टिकट ({fee_a} USDT) → <b>{ca} USDT</b>\n💎 प्रीमियम टिकट ({fee_b} USDT) → <b>{cb} USDT</b>\n{sep}\n📊 <b>आपके आँकड़े</b>\n👥 कुल रेफ़रल: <b>{n}</b>\n💰 कुल कमाई: <b>{income} USDT</b>\n🎟 आपके रेफ़रल द्वारा खरीदे गए टिकट: <b>{tickets}</b>\n⏳ चल रहे राउंड में: <b>{ptk}</b> टिकट (राउंड खत्म होने पर ≈ <b>{pinc} USDT</b>)\n{sep}\n{refnote}",
    "ref_note": "ℹ️ कमीशन xRocket से भुगतान किए गए टिकटों पर गिना जाता है। जो राउंड बंद होकर रिफ़ंड हो जाता है, उस पर कमीशन नहीं मिलता।",
    "ref_off": "\n⏸ रेफ़रल बोनस अभी बंद है।",
    "ref_share_text": "🎰 लकी डाइस लॉटरी — मेरे लिंक से जुड़ें, अपना नंबर चुनें और लाइव डाइस ड्रॉ में USDT जीतें!",
    "ref_new": "🎉 <b>नया रेफ़रल!</b>\n{name} आपके लिंक से जुड़ा है।",
    "ref_paid_dm": "💰 <b>रेफ़रल बोनस!</b>\n{tname} • राउंड #{rid} समाप्त हुआ।\n🎟 आपके रेफ़रल द्वारा खरीदे गए टिकट: {tickets}\n➕ <b>{amount} USDT</b> आपके बैलेंस में जोड़ दिए गए हैं।\n💳 बैलेंस: <b>{bal} USDT</b>",
    "hist_ref": "👥 <b>रेफ़रल बोनस</b> — {tname} • राउंड #{rid}\n   ➕ {amount} USDT\n   🕒 {time}",
    "guide_menu": "📖 <b>गाइड</b>\n{sep}\nहमारी लॉटरी कैसे काम करती है, सब कुछ यहाँ है। एक विषय चुनें:",
    "guide_join": "🎟 <b>शामिल कैसे हों</b>\n{sep}\n1️⃣ <b>लॉटरी में शामिल हों</b> दबाएँ और <b>क्लासिक</b> या <b>प्रीमियम</b> चुनें।\n2️⃣ एक खाली लकी नंबर (1–{slots}) चुनें। वह आपके लिए <b>{mins} मिनट</b> रिज़र्व रहेगा।\n3️⃣ <b>xRocket</b> से या अपने <b>बॉट बैलेंस</b> से भुगतान करें।\n4️⃣ चैनल पोस्ट में अपना नाम कैसे दिखे यह चुनें (@username या ID)। <b>इस चरण के बाद ही आपकी एंट्री पूरी होती है।</b>\n\n🎟 आप हर राउंड में अधिकतम <b>{max}</b> टिकट ले सकते हैं — जितने ज़्यादा टिकट, उतना बेहतर मौका।\n⏳ हर राउंड 24 घंटे खुला रहता है।",
    "guide_draw": "🎲 <b>विजेता कैसे चुने जाते हैं</b>\n{sep}\nजब सभी {slots} नंबर भर जाते हैं और हर खिलाड़ी अपना नाम चुन लेता है, तो चैनल में एक छोटी 1️⃣2️⃣3️⃣ उलटी गिनती आती है। फिर डाइस <b>लाइव</b> रोल होते हैं:\n\n🥇 पहला डाइस → जो नंबर आए वह पहला विजेता\n🥈 दूसरा डाइस → जो नंबर आए वह दूसरा विजेता\n🥉 तीसरा डाइस → जो नंबर आए वह तीसरा विजेता\n\n♻️ एक नंबर दो बार नहीं जीत सकता। वही नंबर दोबारा आए तो डाइस फिर से रोल होता है।\n✅ डाइस Telegram के अपने हैं और {channel} में सबके सामने रोल होते हैं, इसलिए सब कुछ पारदर्शी है।\n⏳ अगर दोनों लॉटरी एक साथ भर जाएँ तो एक के बाद एक ड्रॉ होता है।",
    "guide_prizes": "🏆 <b>लॉटरी और इनाम</b>\n{sep}\n🎟 <b>क्लासिक</b> — प्रवेश शुल्क <b>{fee_a} USDT</b>\n{prizes_a}\n\n💎 <b>प्रीमियम</b> — प्रवेश शुल्क <b>{fee_b} USDT</b>\n{prizes_b}\n\n🏆 हर राउंड में 3 विजेता। ड्रॉ के तुरंत बाद इनाम आपके बॉट बैलेंस में जुड़ जाता है।\n⌛ अगर राउंड 24 घंटे में नहीं भरता तो बंद हो जाता है और हर टिकट का पैसा आपके बैलेंस में वापस आ जाता है।\n🔁 दोनों लॉटरी साथ-साथ चलती हैं और आप दोनों में शामिल हो सकते हैं।",
    "guide_money": "💰 <b>बैलेंस और निकासी</b>\n{sep}\n💳 आपके बैलेंस में इनाम, रिफ़ंड और रेफ़रल बोनस रहते हैं।\n🎟 आप इससे टिकट खरीद सकते हैं।\n\n💸 <b>निकासी</b>\nनिकासी दबाएँ, राशि भेजें (न्यूनतम <b>{minwd} USDT</b>, दशमलव के बाद 3 अंक तक) और पुष्टि करें। पैसा आपके xRocket वॉलेट में जाएगा।\n\n📜 <b>लेन-देन</b>\nहर टिकट, जीत, रिफ़ंड, रेफ़रल बोनस और निकासी स्थिति के साथ वहाँ दिखती है:\n🟢 जारी  •  🏁 समाप्त  •  🏆 जीत",
    "guide_refer": "👥 <b>रेफ़र करें और कमाएँ</b>\n{sep}\n1️⃣ <b>रेफ़र</b> दबाएँ और अपना निजी लिंक कॉपी करें।\n2️⃣ जो दोस्त आपके लिंक से बॉट शुरू करेंगे वे आपके रेफ़रल बनेंगे।\n3️⃣ वे हर टिकट खरीदेंगे तो आपको मिलेगा <b>{pct}%</b> — उस <b>राउंड के समाप्त होने के बाद</b>।\n\n🎟 क्लासिक टिकट → <b>{ca} USDT</b>\n💎 प्रीमियम टिकट → <b>{cb} USDT</b>\n\n📊 रेफ़र पेज पर कुल रेफ़रल, कुल कमाई, रेफ़रल द्वारा खरीदे गए टिकट और अभी चल रहे राउंड के टिकट दिखते हैं।\n{refnote}",
    "guide_faq": "❓ <b>अक्सर पूछे जाने वाले प्रश्न</b>\n{sep}\n<b>मेरा भुगतान देर से आया?</b>\nअगर इस बीच नंबर किसी और ने ले लिया या राउंड बंद हो गया, तो राशि आपके बैलेंस में जुड़ जाती है।\n\n<b>राउंड नहीं भरा?</b>\n24 घंटे बाद राउंड बंद हो जाता है और हर टिकट का पैसा आपके बैलेंस में लौट आता है।\n\n<b>मैंने नाम नहीं चुना?</b>\n{wait} मिनट बाद अपने आप चुन लिया जाता है (username हो तो @username, नहीं तो ID)।\n\n<b>नतीजे कहाँ देखूँ?</b>\n{channel} चैनल में और आपके लेन-देन पेज पर।\n\n<b>क्या दोनों लॉटरी में खेल सकता हूँ?</b>\nहाँ, क्लासिक और प्रीमियम एक साथ चलती हैं।",
    "wd_off": "⏸ निकासी थोड़ी देर के लिए रोकी गई है। कृपया बाद में फिर कोशिश करें।",
    "wd_off_alert": "निकासी थोड़ी देर के लिए रोकी गई है। कृपया बाद में फिर कोशिश करें।",
    "wd_review": "🔍 <b>निकासी की जाँच चल रही है</b>\nआपकी सुरक्षा के लिए इस निकासी को एडमिन एक बार खुद जाँचेंगे। फ़ैसला होते ही आपको बता दिया जाएगा — दोबारा भेजने की ज़रूरत नहीं है।",
    "wd_review_exists": "🔍 आपकी एक निकासी पहले से जाँच के इंतज़ार में है। कृपया एडमिन के फ़ैसले का इंतज़ार करें।",
    "wd_approved": "✅ एडमिन ने आपकी निकासी मंज़ूर कर दी है।",
    "wd_rejected": "❌ आपका निकासी अनुरोध मंज़ूर नहीं हुआ और आपका बैलेंस पहले जैसा ही है। अगर आपको कोई गलती लगती है तो एडमिन से संपर्क करें।",
    "banned": "🚫 <b>आपका अकाउंट प्रतिबंधित कर दिया गया है</b>\nआप अभी यह बॉट इस्तेमाल नहीं कर सकते। अगर आपको कोई गलती लगती है तो एडमिन से संपर्क करें।",
    "banned_alert": "🚫 आपका अकाउंट प्रतिबंधित है। एडमिन से संपर्क करें।",
    "strike_blocked": "⛔ <b>शामिल होना अस्थायी रूप से बंद</b>\nआपने लगातार {n} बार नंबर रिज़र्व करके भुगतान नहीं किया। इसलिए <b>{hours} घंटे</b> के लिए लॉटरी में शामिल होना बंद रहेगा। आपका बैलेंस, निकासी और मेनू पहले की तरह काम करेंगे।",
    "join_blocked": "⛔ <b>आपके लिए शामिल होना अस्थायी रूप से बंद है</b>\nआपने लगातार कई बार नंबर रिज़र्व करके भुगतान नहीं किया। <b>{left}</b> बाद आप फिर शामिल हो सकेंगे। आपका बैलेंस, निकासी और मेनू पहले की तरह काम करेंगे।",
    "ban_dm": "🚫 <b>आपका अकाउंट प्रतिबंधित कर दिया गया है</b>\nअब आप यह बॉट इस्तेमाल नहीं कर सकते। अगर आपको कोई गलती लगती है तो एडमिन से संपर्क करें।",
    "unban_dm": "✅ <b>आपका अकाउंट फिर से चालू हो गया है</b>\nप्रतिबंध हटा दिया गया है। आप पहले की तरह बॉट इस्तेमाल कर सकते हैं। जारी रखने के लिए /menu दबाएँ।",
    "strike_warn": "⚠️ <b>चेतावनी</b>\nआपने लगातार <b>{n}</b> बार नंबर रिज़र्व करके भुगतान नहीं किया है।\nअगर ऐसा <b>एक बार और</b> हुआ तो <b>{hours} घंटे</b> के लिए लॉटरी में शामिल होना बंद हो जाएगा।\n\nनंबर तभी रिज़र्व करें जब आप अभी भुगतान करने के लिए तैयार हों। जारी रखें?",
}

TEXT["zh"] = TEXT_ZH
TEXT["hi"] = TEXT_HI


state = {}  # filled by init_state() once the database is connected
state_dirty = threading.Event()
io_lock = threading.Lock()  # never call flush_state / ledger_rows while holding `lock`
pending_ledger = []
ledger_cache = {}
ledger_seq = [0]
notices = []
INSTANCE_ID = uuid.uuid4().hex
store = None


def fill_defaults(data):
    data.setdefault("users", {})
    data.setdefault("rounds", {})
    data.setdefault("current", None)
    data.setdefault("current_by_tier", {})
    # Older single-lottery data: the running round belongs to the first (Classic) lottery.
    if data["current"] is not None and "A" not in data["current_by_tier"]:
        data["current_by_tier"]["A"] = data["current"]
    data.setdefault("counter", 0)
    data.setdefault("invoices", {})
    data.setdefault("payouts", {})
    data.setdefault("stats", {})
    data.setdefault("paused", False)
    data.setdefault("ref_percent", str(REF_DEFAULT_PERCENT))
    data.setdefault("approvals", {})
    data.setdefault("approval_counter", 0)
    data.setdefault("wd_enabled", True)
    data.setdefault("daily", {})      # per-day counters for the daily report (Bangladesh dates)
    data.setdefault("images", {})     # lottery pictures: {"A": file_id, "B": file_id}
    data.setdefault("last_report", None)
    return data


class FileDB:
    """Local development storage (a single JSON file). NOT for Render: its disk is wiped on every restart."""

    supports_lock = False

    def __init__(self, path):
        self.path = path
        self.data = {}
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as f:
                self.data = json.load(f)

    def get(self, path):
        node = self.data
        for part in path.split("/"):
            if not isinstance(node, dict) or part not in node:
                return None
            node = node[part]
        return node

    def update(self, updates):
        for path, value in updates.items():
            parts = path.split("/")
            node = self.data
            for part in parts[:-1]:
                node = node.setdefault(part, {})
            node[parts[-1]] = value
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.data, f, ensure_ascii=False)
        os.replace(tmp, self.path)

    def try_lock(self, me, lease):
        return True

    def refresh_lock(self, me, lease):
        return True

    def release_lock(self, me):
        return True


class FirebaseDB:
    """Firebase Realtime Database. All writes of one flush are a single atomic multi-path update."""

    supports_lock = True

    def __init__(self, cred_json, url):
        import firebase_admin
        from firebase_admin import credentials
        from firebase_admin import db as fdb

        info = json.loads(cred_json)
        if isinstance(info.get("private_key"), str):
            info["private_key"] = info["private_key"].replace("\\n", "\n")
        firebase_admin.initialize_app(credentials.Certificate(info), {"databaseURL": url})
        self.fdb = fdb

    def get(self, path):
        return self.fdb.reference(path).get()

    def update(self, updates):
        self.fdb.reference("/").update(updates)

    def _lock_txn(self, me, lease, mode):
        def fn(cur):
            now = time.time()
            mine = bool(cur) and cur.get("id") == me
            if mode == "release":
                return None if mine else cur
            if mode == "refresh":
                return {"id": me, "t": now} if mine else cur
            # mode == "take"
            if cur and not mine and now - float(cur.get("t", 0)) < lease:
                return cur
            return {"id": me, "t": now}

        try:
            res = self.fdb.reference("lottery/lock").transaction(fn)
        except Exception as e:
            print("lock transaction error:", e)
            return False
        if mode == "release":
            return True
        return bool(res) and res.get("id") == me

    def try_lock(self, me, lease):
        return self._lock_txn(me, lease, "take")

    def refresh_lock(self, me, lease):
        return self._lock_txn(me, lease, "refresh")

    def release_lock(self, me):
        return self._lock_txn(me, 0, "release")


def make_store():
    url = os.environ.get("FIREBASE_DB_URL", "").strip()
    cred = os.environ.get("FIREBASE_CREDENTIALS", "").strip()
    if url and cred:
        print("Storage: Firebase Realtime Database")
        return FirebaseDB(cred, url)
    if os.environ.get("RENDER"):
        print("ERROR: FIREBASE_DB_URL / FIREBASE_CREDENTIALS are missing. Refusing to start on Render with a local")
        print("disk, because all data would be lost on every restart.")
        raise SystemExit(1)
    print("WARNING: LOCAL MODE - data is stored in a local file. Set FIREBASE_DB_URL and FIREBASE_CREDENTIALS.")
    return FileDB(os.environ.get("LOCAL_DB_FILE", "local_db.json"))


def init_state():
    raw = store.get("lottery/state")
    data = json.loads(raw) if raw else {}
    fill_defaults(data)
    state.clear()
    state.update(data)
    ensure_snapshots()


def ensure_snapshots():
    """Every round remembers its own fee and prizes, so editing TIERS never changes a running round."""
    for r in state["rounds"].values():
        if r.get("fee"):
            continue
        c = cfg(tier_of(r))
        r["fee"] = str(c["fee"])
        r["prizes"] = [str(p) for p in c["prizes"]]
        r["house"] = str(c["house"])


def save_state():
    """Marks the data as changed. A background thread writes it to the database a moment later."""
    state_dirty.set()


def flush_state(raise_on_error=False):
    """Writes state + new ledger rows to the database in ONE atomic update. Do not call while holding `lock`."""
    with io_lock:
        with lock:
            blob = json.dumps(state, ensure_ascii=False)
            rows = list(pending_ledger)
            del pending_ledger[:]
        updates = {"lottery/state": blob}
        for uid, key, rowd in rows:
            updates[f"lottery/ledger/{uid}/{key}"] = rowd
        try:
            store.update(updates)
        except Exception as e:
            print("database write failed:", e)
            with lock:
                pending_ledger[:0] = rows
            state_dirty.set()
            if raise_on_error:
                raise
            return False
    return True


def state_writer():
    while True:
        state_dirty.wait()
        time.sleep(FLUSH_DELAY)
        state_dirty.clear()
        try:
            flush_state()
        except Exception as e:
            print("state writer error:", e)


def money(value):
    return f"{value:.3f}"


def tier_of(r):
    return (r or {}).get("tier") or "A"


def cfg(tier):
    return TIERS.get(tier, TIERS["A"])


def fee_of(r):
    if r and r.get("fee"):
        return Decimal(r["fee"])
    return cfg(tier_of(r))["fee"]


def prizes_of(r):
    if r and r.get("prizes"):
        return [Decimal(p) for p in r["prizes"]]
    return cfg(tier_of(r))["prizes"]


def house_of(r):
    if r and r.get("house"):
        return Decimal(r["house"])
    return cfg(tier_of(r))["house"]


def prizes_line_r(r):
    return " • ".join(f"{MEDALS[i]} {money(p)}" for i, p in enumerate(prizes_of(r)))


def tier_name(tier, lang="en"):
    names = cfg(tier)["name"]
    return names.get(lang) or names["en"]


def tier_label(tier, lang="en"):
    return f"{cfg(tier)['emoji']} {tier_name(tier, lang)}"


def tier_image(tier):
    return (state.get("images") or {}).get(tier)


def prizes_line(tier):
    return " • ".join(f"{MEDALS[i]} {money(p)}" for i, p in enumerate(cfg(tier)["prizes"]))


def new_user():
    return {"balance": "0.00", "name": "", "username": "", "lang": None}


def user_rec(uid):
    rec = state["users"].setdefault(str(uid), new_user())
    rec.setdefault("lang", None)
    return rec


def lang_of(uid):
    code = state["users"].get(str(uid), {}).get("lang") or "en"
    return code if code in TEXT else "en"


def ref_percent():
    try:
        return Decimal(str(state.get("ref_percent", REF_DEFAULT_PERCENT)))
    except InvalidOperation:
        return REF_DEFAULT_PERCENT


def set_ref_percent(value):
    value = max(Decimal("0"), min(REF_MAX_PERCENT, Decimal(value))).quantize(Decimal("0.01"))
    with lock:
        state["ref_percent"] = str(value)
        save_state()
    return value


def fmt_pct(value):
    return format(Decimal(value).normalize(), "f")


def ref_commission(fee, pct):
    return (Decimal(fee) * Decimal(pct) / 100).quantize(Decimal("0.001"), rounding=ROUND_HALF_UP)


def t(user_id, key, **kw):
    tier = kw.pop("tier", None)
    lang = lang_of(user_id)
    if isinstance(tier, dict):  # a round: use the fee and prizes it was created with
        kw.setdefault("fee", money(fee_of(tier)))
        kw.setdefault("prizes", prizes_line_r(tier))
        kw.setdefault("tname", tier_label(tier_of(tier), lang))
    elif tier is not None:
        c = cfg(tier)
        kw.setdefault("fee", money(c["fee"]))
        kw.setdefault("prizes", prizes_line(tier))
        kw.setdefault("tname", tier_label(tier, lang))
    kw.setdefault("sep", SEP)
    kw.setdefault("fee", money(TIERS["A"]["fee"]))
    kw.setdefault("slots", SLOTS)
    kw.setdefault("max", MAX_PER_USER)
    kw.setdefault("mins", RESERVE_SECONDS // 60)
    kw.setdefault("wait", DISPLAY_CHOICE_SECONDS // 60)
    kw.setdefault("minwd", money(MIN_WITHDRAW))
    kw.setdefault("channel", CHANNEL)
    template = TEXT[lang].get(key) or TEXT["en"][key]
    try:
        return template.format(**kw)
    except (KeyError, IndexError):
        return template


def balance(uid):
    return Decimal(state["users"].get(str(uid), {}).get("balance", "0.00"))


def row_from(uid, d):
    return [d.get("t", ""), str(uid), d.get("k", ""), d.get("a", "0.000"), str(d.get("b", "")), d.get("r", "")]


def log_ledger(uid, kind, amount, after, ref=""):
    uid = str(uid)
    with lock:
        ledger_seq[0] += 1
        key = f"{int(time.time() * 1000):013d}{ledger_seq[0] % 100000:05d}"
        rowd = {
            "t": datetime.now(UTC).strftime("%Y-%m-%d %H:%M:%S"),
            "k": kind,
            "a": money(amount),
            "b": str(after),
            "r": ref,
        }
        pending_ledger.append((uid, key, rowd))
        if uid in ledger_cache:
            ledger_cache[uid].append(row_from(uid, rowd))
    state_dirty.set()


def ledger_rows(uid):
    """All ledger rows of one user (loaded once, then served from memory). Do not call while holding `lock`."""
    uid = str(uid)
    with lock:
        cached = ledger_cache.get(uid)
        if cached is not None:
            return list(cached)
    with io_lock:  # no flush can run while we read, so no row can be missed or doubled
        remote = store.get(f"lottery/ledger/{uid}") or {}
        if isinstance(remote, list):
            remote = {str(i): v for i, v in enumerate(remote) if v}
        with lock:
            merged = dict(remote)
            for p_uid, key, rowd in pending_ledger:
                if p_uid == uid:
                    merged[key] = rowd
            rows = [row_from(uid, merged[k]) for k in sorted(merged)]
            ledger_cache[uid] = rows
            return list(rows)


def add_balance(uid, delta, kind, ref=""):
    rec = user_rec(uid)
    rec["balance"] = money(Decimal(rec["balance"]) + delta)
    log_ledger(uid, kind, delta, rec["balance"], ref)


def stat_add(key, value):
    stats = state["stats"]
    if isinstance(value, Decimal):
        stats[key] = money(Decimal(stats.get(key, "0.00")) + value)
    else:
        stats[key] = int(stats.get(key, 0)) + value


def bdt_day(ts=None):
    return datetime.fromtimestamp(time.time() if ts is None else ts, BDT).strftime("%Y-%m-%d")


def day_add(key, value=1):
    """Adds to today's (Bangladesh date) counter used by the daily report."""
    with lock:
        d = state.setdefault("daily", {}).setdefault(bdt_day(), {})
        if isinstance(value, Decimal):
            d[key] = money(Decimal(str(d.get(key, "0"))) + value)
        else:
            d[key] = int(d.get(key, 0)) + value
        save_state()


def day_user(key, uid, value=1):
    """Same, but kept per user (for example withdrawals per user)."""
    with lock:
        m = state.setdefault("daily", {}).setdefault(bdt_day(), {}).setdefault(key, {})
        k = str(uid)
        if isinstance(value, Decimal):
            m[k] = money(Decimal(str(m.get(k, "0"))) + value)
        else:
            m[k] = int(m.get(k, 0)) + value
        save_state()


def ensure_user(tg_user):
    with lock:
        is_new = str(tg_user.id) not in state["users"]
        rec = user_rec(tg_user.id)
        name = tg_user.first_name or ""
        username = tg_user.username or ""
        if is_new:
            day_add("new_users")
        if is_new or rec.get("name") != name or rec.get("username") != username:
            rec["name"] = name
            rec["username"] = username
            save_state()


def is_banned(uid):
    return bool(state["users"].get(str(uid), {}).get("banned"))


def banned_reply(obj, is_call):
    uid = obj.from_user.id
    if is_call:
        ack(obj, t(uid, "banned_alert"), True)
    else:
        safe_send(obj.chat.id, t(uid, "banned"))


def join_block_left(uid):
    return max(0, int(state["users"].get(str(uid), {}).get("join_block_until", 0) - time.time()))


def fmt_left(secs):
    h, rem = divmod(secs, 3600)
    return f"{h}h {rem // 60:02d}m"


def show_join_block(chat_id, uid, message_id=None):
    left = join_block_left(uid)
    if left <= 0:
        return False
    edit_or_send(chat_id, message_id, t(uid, "join_blocked", left=fmt_left(left)), back_markup(uid))
    return True


def add_strike(uid):
    """One more unpaid reservation in a row. Called with `lock` held."""
    rec = user_rec(uid)
    rec["strikes"] = int(rec.get("strikes", 0)) + 1
    if rec["strikes"] >= STRIKE_LIMIT:
        count = rec["strikes"]
        rec["strikes"] = 0
        rec["join_block_until"] = time.time() + JOIN_BLOCK_HOURS * 3600
        day_add("strike_blocks")
        notices.append((uid, t(uid, "strike_blocked", n=count, hours=JOIN_BLOCK_HOURS)))
        notices.append(
            (
                ADMIN_ID,
                f"⛔ User <code>{uid}</code> cannot join for {JOIN_BLOCK_HOURS}h: "
                f"{count} reservations in a row were not paid.",
            )
        )
    save_state()


def send_notices():
    with lock:
        items = list(notices)
        del notices[:]
    for chat_id, text in items:
        safe_send(chat_id, text)


def fmt_time(ts, lang="en"):
    tz, label = LANG_TZ.get(lang, LANG_TZ["en"])
    return datetime.fromtimestamp(ts, tz).strftime("%d %b %Y, %I:%M %p") + f" ({label})"


def short_time(text, lang="en"):
    try:
        dt = datetime.strptime(text, "%Y-%m-%d %H:%M:%S").replace(tzinfo=UTC)
    except ValueError:
        return text
    tz, label = LANG_TZ.get(lang, LANG_TZ["en"])
    return dt.astimezone(tz).strftime("%d %b, %I:%M %p") + f" ({label})"


def find_usdt(obj):
    if isinstance(obj, dict):
        if CURRENCY in obj and not isinstance(obj[CURRENCY], (dict, list)):
            try:
                return Decimal(str(obj[CURRENCY]))
            except InvalidOperation:
                pass
        name = str(obj.get("currency") or obj.get("asset") or obj.get("symbol") or obj.get("ticker") or "").upper()
        if name == CURRENCY:
            for key in ("balance", "available", "amount", "total"):
                if obj.get(key) is not None:
                    try:
                        return Decimal(str(obj[key]))
                    except InvalidOperation:
                        pass
        for value in obj.values():
            found = find_usdt(value)
            if found is not None:
                return found
    elif isinstance(obj, list):
        for value in obj:
            found = find_usdt(value)
            if found is not None:
                return found
    return None


def app_balance():
    try:
        r = requests.get(f"{API}/api/v1/balances", headers=HEADERS, timeout=20)
        if r.status_code != 200:
            print("balances error:", r.status_code, r.text[:200])
            return None
        found = find_usdt(r.json())
        if found is None:
            print("balances: USDT not found in:", r.text[:300])
        return found
    except (requests.RequestException, ValueError) as e:
        print("balances error:", e)
        return None


def check_key():
    try:
        r = requests.get(f"{API}/api/v1/app-info", headers=HEADERS, timeout=20)
        if r.status_code == 200:
            print("xRocket key OK")
            print("App USDT balance:", app_balance())
        else:
            print("xRocket key FAILED:", r.status_code, r.text)
    except requests.RequestException as e:
        print("xRocket check network error:", e)


def create_invoice(uid, round_id, number, fee):
    base = {
        "priceAmount": money(fee),
        "priceCurrency": CURRENCY,
        "clientInvoiceId": f"r{round_id}-n{number}-u{uid}-{int(time.time())}",
        "description": f"Lottery round #{round_id} - ticket {number}",
    }
    for body in (dict(base, expiresIn=RESERVE_SECONDS * 1000), base):
        try:
            r = requests.post(f"{API}/api/v1/invoices", headers=HEADERS, json=body, timeout=20)
        except requests.RequestException as e:
            print("create_invoice network error:", e)
            return None
        if r.status_code < 400:
            return r.json()
        print("create_invoice error:", r.status_code, r.text)
    return None


def get_invoice(invoice_id):
    try:
        r = requests.get(
            f"{API}/api/v1/invoice",
            headers=HEADERS,
            params={"invoiceId": invoice_id},
            timeout=20,
        )
        if r.status_code >= 400:
            print("get_invoice error:", r.status_code, r.text)
            return None
        return r.json()
    except requests.RequestException as e:
        print("get_invoice network error:", e)
        return None


def invoice_link(invoice):
    links = invoice.get("links") or {}
    return links.get("telegramBotLink") or links.get("webLink") or links.get("telegramMiniAppLink")


def api_get_payout(payout_id=None, client_id=None):
    params = {"payoutId": payout_id} if payout_id else {"clientPayoutId": client_id}
    try:
        r = requests.get(f"{API}/api/v1/payout", headers=HEADERS, params=params, timeout=20)
        if r.status_code >= 400:
            print("get_payout error:", r.status_code, r.text)
            return r.status_code, None
        return r.status_code, r.json()
    except requests.RequestException as e:
        print("get_payout network error:", e)
        return 0, None


def api_create_payout(uid, amount, client_id):
    body = {
        "clientPayoutId": client_id,
        "target": str(uid),
        "targetType": "telegram_user_id",
        "asset": CURRENCY,
        "amount": money(amount),
        "description": "Lottery withdrawal",
    }
    try:
        r = requests.post(f"{API}/api/v1/payouts", headers=HEADERS, json=body, timeout=30)
    except requests.RequestException as e:
        print("create_payout network error:", e)
        return "unknown", None
    if r.status_code >= 400:
        print("create_payout error:", r.status_code, r.text)
        try:
            err = r.json()
            reason = err.get("detail") or err.get("title") or r.text
        except ValueError:
            reason = r.text
        return "error", reason
    try:
        return "ok", r.json()
    except ValueError:
        return "unknown", None


def current_round(tier):
    cur = state["current_by_tier"].get(tier)
    if cur is None:
        return None
    return state["rounds"].get(str(cur))


def open_round(tier):
    r = current_round(tier)
    if r and r["status"] == "open" and r.get("message_id") and time.time() < r["ends"]:
        return r
    return None


def release_expired(r):
    now = time.time()
    changed = False
    for key, val in list(r["reserved"].items()):
        if val["expires"] <= now:
            del r["reserved"][key]
            changed = True
            has_invoice = any(
                inv["round_id"] == r["id"] and inv["number"] == int(key) and inv["user_id"] == val["user_id"]
                for inv in state["invoices"].values()
            )
            if not has_invoice:  # with an invoice the strike is counted when that invoice expires unpaid
                add_strike(val["user_id"])
    return changed


def user_entries(r, uid):
    return sorted(int(k) for k, e in r["entries"].items() if e["user_id"] == uid)


def free_numbers(r):
    return [i for i in range(1, SLOTS + 1) if str(i) not in r["entries"] and str(i) not in r["reserved"]]


def display(entry):
    mode = entry.get("mode")
    if mode is None:
        return "⏳ Choosing name..."
    if mode == "username" and entry.get("username"):
        return "@" + html.escape(entry["username"])
    return f"ID {entry['user_id']}"


def time_left(r):
    secs = max(0, int(r["ends"] - time.time()))
    h, rem = divmod(secs, 3600)
    return f"{h}h {rem // 60:02d}m"


def join_url(tier):
    return f"https://t.me/{BOT_USERNAME}?start=join_{tier}"


def render(r):
    tier = tier_of(r)
    c = cfg(tier)
    rows = []
    for i in range(1, SLOTS + 1):
        entry = r["entries"].get(str(i))
        if entry:
            tag = display(entry)
        elif str(i) in r["reserved"]:
            tag = "⏳ Reserved"
        else:
            tag = "🔓 Open"
        rows.append(f"{NUMBER_EMOJI[i - 1]}  {tag}")
    head = (
        f"🎰 <b>LUCKY DICE LOTTERY</b> • {c['emoji']} <b>{c['name']['en'].upper()}</b>\n"
        f"{SEP}\n"
        f"🏷 Round: <b>#{r['id']}</b>\n"
        f"🎟 Entry: <b>{money(fee_of(r))} USDT</b>\n"
        f"🏆 Prizes (USDT)\n"
        f"{prizes_line_r(r)}\n"
        f"👥 Players: <b>{len(r['entries'])}/{SLOTS}</b>\n"
        f"{SEP}\n"
        + "\n".join(rows)
        + f"\n{SEP}\n"
    )
    markup = types.InlineKeyboardMarkup()
    status = r["status"]
    if status == "open":
        foot = (
            f"⏳ Time left: <b>{time_left(r)}</b>\n"
            f"🕒 Ends: {fmt_time(r['ends'], 'en')}\n\n"
            "🎲 When all 6 numbers are taken, live dice rolls pick 3 winners.\n"
            "👇 Tap the button below to choose your lucky number."
        )
        markup.add(types.InlineKeyboardButton("🎟 Join Now", url=join_url(tier)))
    elif status == "drawing":
        if not r.get("ready_at"):
            foot = "🔒 <b>Round full!</b>\n⏳ Waiting for the last players to choose how their name appears..."
        elif draw_state["active"] == r["id"]:
            foot = "🎲 <b>Live draw in progress...</b>"
        elif draw_state["active"] is not None:
            foot = (
                "🔒 <b>Round full!</b>\n"
                "⏳ Another lottery is being drawn right now. The live draw for this one starts right after it."
            )
        else:
            foot = "🔒 <b>Round full!</b>\n🎲 The live draw is about to begin..."
    elif status == "finished":
        foot = "✅ <b>ROUND FINISHED</b>\n" + winners_block(r)
    else:
        foot = (
            "⌛ <b>ROUND CLOSED</b>\n"
            "Not enough players joined in time.\n"
            f"💸 Every ticket was refunded ({money(fee_of(r))} USDT each) to the players' bot balance."
        )
    return head + foot, markup


def refresh_post(r):
    if not r.get("message_id"):
        return
    with lock:
        text, markup = render(r)
    if post_cache.get(r["id"]) == text:
        return
    try:
        if r.get("photo"):
            cap, mode = fit_caption(text)
            bot.edit_message_caption(caption=cap, chat_id=CHANNEL, message_id=r["message_id"], parse_mode=mode, reply_markup=markup)
        else:
            bot.edit_message_text(text, CHANNEL, r["message_id"], parse_mode="HTML", reply_markup=markup)
        post_cache[r["id"]] = text
    except ApiTelegramException as e:
        if "message is not modified" in str(e):
            post_cache[r["id"]] = text
        else:
            print("edit error:", e)
    except Exception as e:
        print("edit error:", e)


def publish_round(r, force=False):
    now = time.time()
    key = tier_of(r)
    if not force and now - publish_state.get(key, 0.0) < 30:
        return
    publish_state[key] = now
    with lock:
        text, markup = render(r)
    msg = None
    is_photo = False
    file_id = tier_image(key)
    if file_id:
        try:
            msg = chan_photo(file_id, text, markup)
            is_photo = True
        except Exception as e:
            print("Could not post the lottery picture, posting text instead:", e)
            safe_send(ADMIN_ID, "⚠️ The lottery picture could not be posted, so a text post was used. Check it with /images and set it again with /setimage.")
    if msg is None:
        try:
            msg = bot.send_message(CHANNEL, text, parse_mode="HTML", reply_markup=markup)
        except Exception as e:
            print("Could not post to the channel (is the bot an admin?):", e)
            return
    with lock:
        r["message_id"] = msg.message_id
        r["photo"] = is_photo
        save_state()
    post_cache[r["id"]] = text
    pin_round(r)


def pin_round(r):
    """Pin the lottery post (bot needs the 'Pin messages' admin right). Retried at most once a minute."""
    now = time.time()
    with lock:
        mid = r.get("message_id")
        if not mid or r.get("pinned") or now - r.get("pin_try", 0) < 60:
            return
        r["pin_try"] = now
    try:
        bot.pin_chat_message(CHANNEL, mid, disable_notification=True)
    except Exception as e:
        print("pin error (give the bot the 'Pin messages' right):", e)
        return
    with lock:
        r["pinned"] = True
        save_state()


def unpin_round(r):
    with lock:
        mid = r.get("message_id")
        was_pinned = r.get("pinned")
        r["pinned"] = False
        save_state()
    if not mid or not was_pinned:
        return
    try:
        bot.unpin_chat_message(CHANNEL, mid)
    except Exception as e:
        print("unpin error:", e)


def create_round(tier):
    """Create and post a new round for one lottery. Safe to call from several threads."""
    with lock:
        cur = current_round(tier)
        if cur is not None and cur["status"] in ("open", "drawing"):
            return
        if state.get("paused"):
            return
        state["counter"] += 1
        rid = state["counter"]
        now = time.time()
        r = {
            "id": rid,
            "tier": tier,
            "fee": str(cfg(tier)["fee"]),
            "prizes": [str(p) for p in cfg(tier)["prizes"]],
            "house": str(cfg(tier)["house"]),
            "status": "open",
            "created": now,
            "ends": now + ROUND_SECONDS,
            "message_id": None,
            "entries": {},
            "reserved": {},
            "full_at": None,
            "ready_at": None,
            "started": False,
            "announced": False,
            "winners": [],
            "reminder_id": None,
            "reminder_at": None,
            "one_left_sent": False,
        }
        state["rounds"][str(rid)] = r
        state["current_by_tier"][tier] = rid
        save_state()
    publish_round(r, force=True)


def delete_channel_message(message_id):
    try:
        bot.delete_message(CHANNEL, message_id)
    except Exception as e:
        print("delete error:", e)


def cleanup_reminder(r):
    with lock:
        mid = r.get("reminder_id")
        if not mid:
            return
        r["reminder_id"] = None
        save_state()
    delete_channel_message(mid)


def reminder_text(r):
    tier = tier_of(r)
    c = cfg(tier)
    left = SLOTS - len(r["entries"])
    nums = " ".join(NUMBER_EMOJI[i - 1] for i in free_numbers(r))
    if left > 3:
        title = f"🎰 <b>{left} SPOTS LEFT!</b>"
        body = "Pick your lucky number and join the live dice draw!"
    else:
        noun = "SPOT" if left == 1 else "SPOTS"
        title = f"🔥 <b>HURRY UP — ONLY {left} {noun} LEFT!</b>"
        body = "The live draw starts the moment the round is full. Don't miss your chance — join now!"
    lines = [
        title,
        SEP,
        f"{tier_label(tier)} • Round: <b>#{r['id']}</b>",
        f"🎟 Entry: <b>{money(fee_of(r))} USDT</b>",
        f"🏆 Prizes: {prizes_line_r(r)} USDT",
    ]
    if nums:
        lines.append(f"🔓 Open numbers: {nums}")
    lines += [f"⏳ Time left: <b>{time_left(r)}</b>", SEP, body]
    return "\n".join(lines)


def maybe_remind(r):
    now = time.time()
    tier = tier_of(r)
    interval = cfg(tier)["reminder"]
    with lock:
        if r["status"] != "open" or now >= r["ends"]:
            return
        last = r.get("reminder_at") or r["created"]
        if now - last < interval:
            return
        text = reminder_text(r)
        old = r.get("reminder_id")
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("🎟 Join Now", url=join_url(tier)))
    try:
        msg = None
        file_id = tier_image(tier)
        if file_id:
            try:
                msg = chan_photo(file_id, text, kb, reply_to=r.get("message_id"))
            except Exception as e:
                print("reminder picture error (text used instead):", e)
        if msg is None:
            msg = chan_send(text, kb, reply_to=r.get("message_id"))
    except Exception as e:
        print("reminder error:", e)
        with lock:
            r["reminder_at"] = now - interval + 60
        return
    with lock:
        r["reminder_id"] = msg.message_id
        r["reminder_at"] = time.time()
        save_state()
    if old:
        delete_channel_message(old)


def notify_one_left(r):
    with lock:
        if r["status"] != "open" or r.get("one_left_sent") or SLOTS - len(r["entries"]) != 1:
            return
        r["one_left_sent"] = True
        save_state()
        users = sorted({e["user_id"] for e in r["entries"].values()})
        tier = tier_of(r)
    for uid in users:
        kb = types.InlineKeyboardMarkup()
        kb.add(types.InlineKeyboardButton(t(uid, "btn_join"), callback_data=f"jt:{tier}"))
        safe_send(uid, t(uid, "one_left_dm", rid=r["id"], tier=r), kb)


def safe_send(chat_id, text, markup=None):
    try:
        bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=markup)
    except Exception as e:
        print("send error:", chat_id, e)


def try_send(chat_id, text, markup=None):
    """Like safe_send, but tells whether the message was delivered."""
    try:
        bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=markup)
        return True
    except Exception as e:
        print("send error:", chat_id, e)
        return False


def edit_or_send(chat_id, message_id, text, markup=None):
    if message_id:
        try:
            bot.edit_message_text(text, chat_id, message_id, parse_mode="HTML", reply_markup=markup)
            return
        except Exception as e:
            if "message is not modified" in str(e):
                return
    safe_send(chat_id, text, markup)


def ack(call, text=None, alert=False):
    try:
        bot.answer_callback_query(call.id, text, show_alert=alert)
    except Exception:
        pass


def clear_markup(call):
    try:
        bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=None)
    except Exception:
        pass


def confirm_entry_locked(r, num, uid, persist=True, via="balance"):
    rec = state["users"].get(str(uid), {})
    if rec:
        rec["strikes"] = 0  # a real purchase clears the unpaid-reservation count
    now = time.time()
    r["reserved"].pop(str(num), None)
    r["entries"][str(num)] = {
        "user_id": uid,
        "name": rec.get("name", ""),
        "username": rec.get("username", ""),
        "mode": None,
        "choice_by": now + DISPLAY_CHOICE_SECONDS,
        "via": via,
        "ref_by": rec.get("ref_by"),
        "ref_pct": state.get("ref_percent", "0"),
    }
    stat_add("tickets", 1)
    day_add(f"tickets_{tier_of(r)}_{'x' if via == 'xrocket' else 'bal'}")
    day_user("players", uid, 1)
    if len(r["entries"]) >= SLOTS and r["status"] == "open":
        r["status"] = "drawing"
        r["full_at"] = now
        r["ready_at"] = None
        r["reserved"] = {}
    if persist:
        save_state()


def after_entry(rid, num, uid):
    with lock:
        r = state["rounds"][str(rid)]
        tier = tier_of(r)
        entry = r["entries"][str(num)]
        username = state["users"].get(str(uid), {}).get("username", "")
        if not username:
            entry["mode"] = "uid"
            save_state()
        total = len(r["entries"])
    emoji = NUMBER_EMOJI[int(num) - 1]
    if username:
        kb = types.InlineKeyboardMarkup()
        kb.add(types.InlineKeyboardButton(t(uid, "btn_show_user", u=username), callback_data=f"nm:{rid}:{num}:u"))
        kb.add(types.InlineKeyboardButton(t(uid, "btn_show_uid", uid=uid), callback_data=f"nm:{rid}:{num}:i"))
        safe_send(uid, t(uid, "entry_ok_choose", emoji=emoji, num=num, rid=rid, total=total, tier=r), kb)
    else:
        safe_send(
            uid,
            t(uid, "entry_ok_nouser", emoji=emoji, num=num, rid=rid, total=total, tier=r),
            menu_markup(uid),
        )
    refresh_post(r)


def handle_paid(invoice_id):
    ok = False
    with lock:
        inv = state["invoices"].get(invoice_id)
        if not inv:
            return
        uid = inv["user_id"]
        num = inv["number"]
        r = state["rounds"].get(str(inv["round_id"]))
        fee = Decimal(inv["fee"]) if inv.get("fee") else fee_of(r)
        day_add("money_in", fee)
        if r and r["status"] == "open" and time.time() < r["ends"]:
            release_expired(r)
            res = r["reserved"].get(str(num))
            free = str(num) not in r["entries"] and (res is None or res["user_id"] == uid)
            if free and len(user_entries(r, uid)) < MAX_PER_USER:
                ok = True
        if ok:
            confirm_entry_locked(r, num, uid, persist=False, via="xrocket")
            log_ledger(
                uid,
                "ticket_xrocket",
                Decimal("0"),
                money(balance(uid)),
                f"round {r['id']} ticket {num} invoice {invoice_id}",
            )
        else:
            add_balance(uid, fee, "late_refund", f"invoice {invoice_id}")
            day_add("late_refunds")
        # The invoice is removed only after everything above succeeded,
        # and entry + removal are written to disk together.
        state["invoices"].pop(invoice_id, None)
        save_state()
    if ok:
        try:
            after_entry(r["id"], num, uid)
        except Exception as e:
            print("after_entry error:", e)
    else:
        safe_send(uid, t(uid, "late_refund", num=num, fee=money(fee)), menu_markup(uid))


def apply_default_modes(r, force):
    now = time.time()
    changed = False
    for entry in r["entries"].values():
        if entry["mode"] is None and (force or now >= entry["choice_by"]):
            entry["mode"] = "username" if entry.get("username") else "uid"
            changed = True
    if changed:
        save_state()
    return changed


def close_round(r):
    with lock:
        if r["status"] != "open":
            return
        tier = tier_of(r)
        fee = fee_of(r)
        refunds = {}
        for entry in r["entries"].values():
            refunds[entry["user_id"]] = refunds.get(entry["user_id"], 0) + 1
        for uid, count in refunds.items():
            add_balance(uid, fee * count, "refund", f"round {r['id']} closed")
        r["status"] = "closed"
        r["reserved"] = {}
        stat_add("closed", 1)
        day_add(f"closed_{tier}")
        day_add("refunds", fee * len(r["entries"]))
        save_state()
    refresh_post(r)
    unpin_round(r)
    for uid, count in refunds.items():
        safe_send(
            uid,
            t(uid, "round_closed_dm", rid=r["id"], amount=money(fee * count), tier=r),
            menu_markup(uid),
        )


def chan_reply_kwargs(reply_to):
    if not reply_to:
        return {}
    if hasattr(types, "ReplyParameters"):
        return {"reply_parameters": types.ReplyParameters(message_id=reply_to, allow_sending_without_reply=True)}
    return {"reply_to_message_id": reply_to, "allow_sending_without_reply": True}


def chan_send(text, markup=None, reply_to=None):
    """Post to the channel; if reply_to is given the post is a reply to that round's main post."""
    try:
        return bot.send_message(CHANNEL, text, parse_mode="HTML", reply_markup=markup, **chan_reply_kwargs(reply_to))
    except TypeError:
        return bot.send_message(CHANNEL, text, parse_mode="HTML", reply_markup=markup)


def fit_caption(text):
    """A photo caption may hold 1024 characters. Longer text is sent as plain text, shortened."""
    if len(text) <= 1024:
        return text, "HTML"
    plain = html.unescape(re.sub(r"<[^>]+>", "", text))
    return plain[:1020] + "...", None


def chan_photo(file_id, caption, markup=None, reply_to=None):
    """Post a picture with a caption to the channel (optionally as a reply to the main post)."""
    caption, mode = fit_caption(caption)
    try:
        return bot.send_photo(
            CHANNEL, file_id, caption=caption, parse_mode=mode, reply_markup=markup, **chan_reply_kwargs(reply_to)
        )
    except TypeError:
        return bot.send_photo(CHANNEL, file_id, caption=caption, parse_mode=mode, reply_markup=markup)


def chan_dice(reply_to=None):
    try:
        return bot.send_dice(CHANNEL, emoji="🎲", **chan_reply_kwargs(reply_to))
    except TypeError:
        return bot.send_dice(CHANNEL, emoji="🎲")


def winners_block(r):
    lines = []
    for i, w in enumerate(r.get("winners") or []):
        lines.append(
            f"{MEDALS[i]} <b>{PLACE_NAMES[i]}</b>: <b>{w['display']}</b> • "
            f"{NUMBER_EMOJI[w['number'] - 1]} • <b>{w['prize']} USDT</b>"
        )
    old = r.get("winner")
    if not lines and old:
        lines.append(f"🏆 <b>{old['display']}</b> • {NUMBER_EMOJI[old['number'] - 1]} • <b>{old['prize']} USDT</b>")
    return "\n".join(lines)


def result_text(r):
    blocks = []
    for i, w in enumerate(r["winners"]):
        blocks.append(
            f"{MEDALS[i]} <b>{PLACE_NAMES[i]} Winner</b> — <b>{w['prize']} USDT</b>\n"
            f"      👤 {w['display']}  •  🎟 {NUMBER_EMOJI[w['number'] - 1]}"
        )
    lines = [f"{NUMBER_EMOJI[i - 1]}  {display(r['entries'][str(i)])}" for i in range(1, SLOTS + 1)]
    return (
        "🏆 <b>LOTTERY RESULT</b>\n"
        f"{SEP}\n"
        f"{tier_label(tier_of(r))} • Round: <b>#{r['id']}</b>\n"
        f"{SEP}\n"
        + "\n\n".join(blocks)
        + f"\n{SEP}\n"
        "🎟 <b>Participants</b>\n"
        + "\n".join(lines)
        + f"\n{SEP}\n"
        "✅ Prizes have been added to the winners' bot balances.\n"
        "🔁 A new round is starting now!"
    )


def finish_round(r):
    with lock:
        if r["status"] != "drawing" or len(r.get("winners") or []) < WINNERS:
            return
        tier = tier_of(r)
        per_user = {}
        for i, w in enumerate(r["winners"]):
            add_balance(w["user_id"], Decimal(w["prize"]), "win", f"round {r['id']} ticket {w['number']}")
            per_user.setdefault(w["user_id"], []).append(i)
        r["status"] = "finished"
        stat_add("finished", 1)
        stat_add("fees", house_of(r))
        prize_total = sum((Decimal(w["prize"]) for w in r["winners"]), Decimal("0"))
        stat_add("prizes", prize_total)
        day_add(f"games_{tier}")
        day_add("fees", house_of(r))
        day_add("prizes", prize_total)
        for w in r["winners"]:
            day_user("winners", w["user_id"], Decimal(w["prize"]))
        ref_dms = settle_referrals(r)
        save_state()
        text = result_text(r)
        winners_text = winners_block(r)
        participants = sorted({e["user_id"] for e in r["entries"].values()})
        balances = {uid: balance(uid) for uid in participants}
        wins = {}
        for uid, places in per_user.items():
            wins[uid] = (
                "\n".join(
                    f"{MEDALS[i]} {PLACE_NAMES[i]} • {NUMBER_EMOJI[r['winners'][i]['number'] - 1]} — "
                    f"{r['winners'][i]['prize']} USDT"
                    for i in places
                ),
                sum((Decimal(r["winners"][i]["prize"]) for i in places), Decimal("0")),
            )
        main_id = r.get("message_id")
    refresh_post(r)
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("🎟 Play Next Round", url=join_url(tier)))
    try:
        chan_send(text, kb, reply_to=main_id)
    except Exception as e:
        print("result post error:", e)
        safe_send(CHANNEL, text, kb)
    unpin_round(r)
    for ref_uid, (count, amount, new_bal) in ref_dms.items():
        safe_send(
            ref_uid,
            t(ref_uid, "ref_paid_dm", rid=r["id"], tickets=count, amount=money(amount), bal=money(new_bal), tier=r),
        )
    for uid in participants:
        if uid in wins:
            wk = types.InlineKeyboardMarkup()
            wk.add(types.InlineKeyboardButton(t(uid, "btn_withdraw"), callback_data="wd"))
            lines, total = wins[uid]
            safe_send(
                uid,
                t(uid, "win_dm", rid=r["id"], wins=lines, prize=money(total), bal=money(balances[uid]), tier=r),
                wk,
            )
        else:
            jk = types.InlineKeyboardMarkup()
            jk.add(types.InlineKeyboardButton(t(uid, "btn_join_next"), callback_data=f"jt:{tier}"))
            safe_send(uid, t(uid, "lose_dm", rid=r["id"], winners=winners_text, tier=r), jk)


def run_draw(r):
    """Countdown 1-2-3 (deleted), then one dice per winner. Every step is saved so a restart resumes safely."""
    main_id = r.get("message_id")
    tier = tier_of(r)
    label = tier_label(tier)
    prizes = prizes_of(r)
    with lock:
        apply_default_modes(r, True)
        r.setdefault("winners", [])
        r.setdefault("rolls", 0)
        r["started"] = True
        countdown_done = r.get("countdown_done", False)
        save_state()
    refresh_post(r)

    if not countdown_done:
        sent = []
        for n in range(1, WINNERS + 1):
            try:
                msg = chan_send(NUMBER_EMOJI[n - 1], reply_to=main_id)
                sent.append(msg.message_id)
            except Exception as e:
                print("countdown error:", e)
            time.sleep(COUNTDOWN_STEP)
        for mid in sent:
            delete_channel_message(mid)
        with lock:
            r["countdown_done"] = True
            save_state()

    while True:
        with lock:
            winners = r["winners"]
            if len(winners) >= WINNERS:
                break
            taken = {w["number"] for w in winners}
            rolls = r["rolls"]
        if rolls >= MAX_ROLLS:
            # Safety net, practically unreachable: pick among the numbers that have not won yet.
            value = random.choice([i for i in range(1, SLOTS + 1) if i not in taken])
        else:
            try:
                msg = chan_dice(main_id)
                value = ((int(msg.dice.value) - 1) % SLOTS) + 1
            except Exception as e:
                print("dice error:", e)
                return
            time.sleep(DICE_ANIM)
        with lock:
            r["rolls"] += 1
            save_state()
        if value in taken:
            try:
                chan_send(f"♻️ Duplicate {NUMBER_EMOJI[value - 1]} — rolling again...", reply_to=main_id)
            except Exception as e:
                print("duplicate post error:", e)
            continue
        with lock:
            place = len(r["winners"])
            entry = r["entries"][str(value)]
            winner = {
                "place": place + 1,
                "number": value,
                "user_id": entry["user_id"],
                "display": display(entry),
                "prize": money(prizes[place]),
            }
            r["winners"].append(winner)
            save_state()
        try:
            chan_send(
                f"{MEDALS[place]} <b>{PLACE_NAMES[place]} Winner</b> • {label} • Round #{r['id']}\n"
                f"👤 {winner['display']}  •  🎟 {NUMBER_EMOJI[value - 1]}\n"
                f"💰 <b>{winner['prize']} USDT</b>",
                reply_to=main_id,
            )
        except Exception as e:
            print("winner post error:", e)
        time.sleep(1)
    finish_round(r)


def next_draw_candidate():
    """The full round that is ready (everyone finished their name step) and became full first."""
    now = time.time()
    best = None
    with lock:
        for tier in TIER_ORDER:
            r = current_round(tier)
            if not r or r["status"] != "drawing" or not r.get("ready_at"):
                continue
            if now < r["ready_at"] + DRAW_DELAY:
                continue
            order = r.get("full_at") or r["ready_at"]
            if best is None or order < (best.get("full_at") or best["ready_at"]):
                best = r
    return best


def draw_step():
    """Run at most one draw. Only one lottery is ever drawn at a time."""
    if time.time() < draw_state["gap_until"]:
        return False
    r = next_draw_candidate()
    if r is None:
        return False
    tier = tier_of(r)
    draw_state["active"] = r["id"]
    try:
        refresh_post(r)
        run_draw(r)
        if r["status"] == "finished":
            create_round(tier)  # the new lottery is posted first ...
            draw_state["gap_until"] = time.time() + NEXT_DRAW_GAP  # ... the next draw starts 10 seconds later
        else:
            draw_state["gap_until"] = time.time() + 5
    except Exception:
        draw_state["gap_until"] = time.time() + 5
        raise
    finally:
        draw_state["active"] = None
    return True


def draw_worker():
    while True:
        try:
            draw_step()
        except Exception as e:
            print("draw worker error:", e)
        time.sleep(1)


def tick(tier):
    with lock:
        r = current_round(tier)
    if r is None or r["status"] in ("finished", "closed"):
        if r is not None:
            if draw_state["active"] == r["id"]:
                return  # the draw worker posts the next round right after the result
            cleanup_reminder(r)
        if state.get("paused"):
            return
        create_round(tier)
        return
    if not r.get("message_id"):
        publish_round(r)
        return
    now = time.time()
    with lock:
        if release_expired(r):
            save_state()
        apply_default_modes(r, False)
        status = r["status"]
        ends = r["ends"]
        if status == "drawing" and not r.get("ready_at") and all(e["mode"] is not None for e in r["entries"].values()):
            r["ready_at"] = now
            save_state()
    if status != "open":
        cleanup_reminder(r)
    if status in ("open", "drawing") and not r.get("pinned"):
        pin_round(r)
    if status == "open" and now >= ends:
        close_round(r)
    else:
        refresh_post(r)
        if status == "open":
            maybe_remind(r)
            notify_one_left(r)


def prune_rounds():
    with lock:
        keep = {str(x) for x in state["current_by_tier"].values()}
        ids = sorted((int(k) for k in state["rounds"]), reverse=True)
        for k in ids[KEEP_ROUNDS:]:
            if str(k) not in keep and state["rounds"][str(k)]["status"] in ("finished", "closed"):
                del state["rounds"][str(k)]
        cutoff = (datetime.now(BDT) - timedelta(days=90)).strftime("%Y-%m-%d")
        for k in [k for k in state.get("daily", {}) if k < cutoff]:
            del state["daily"][k]
        save_state()


def maintenance():
    last_prune = time.time()
    while True:
        for tier in TIER_ORDER:
            try:
                tick(tier)
            except Exception as e:
                print("maintenance error:", tier, e)
        try:
            send_notices()
            if time.time() - last_prune > 3600:
                last_prune = time.time()
                prune_rounds()
        except Exception as e:
            print("maintenance error:", e)
        time.sleep(LOOP_INTERVAL)


def notify_admin_withdraw(title, uid, amount, client_id, extra=""):
    with lock:
        rec = state["users"].get(str(uid), {})
        name = html.escape(rec.get("name", "") or "-")
        username = rec.get("username", "")
        left = balance(uid)
    now = time.time()
    safe_send(
        ADMIN_ID,
        f"{title}\n{SEP}\n"
        f"👤 Name: {name}\n"
        f"🔗 Username: {('@' + html.escape(username)) if username else 'none'}\n"
        f"🆔 User ID: <code>{uid}</code>\n"
        f"💰 Amount: <b>{money(Decimal(amount))} USDT</b>\n"
        f"💳 Bot balance now: {money(left)} USDT\n"
        f"🧾 Client ID: <code>{html.escape(client_id)}</code>\n"
        f"🕒 {fmt_time(now, 'en')}\n"
        f"🕒 {fmt_time(now, 'bn')}"
        + (f"\n{SEP}\n{extra}" if extra else ""),
    )


def resolve_payout(client_id, status):
    with lock:
        info = state["payouts"].get(client_id)
        if not info or status not in ("finished", "failed"):
            return
        state["payouts"].pop(client_id)
        uid = info["user_id"]
        amount = Decimal(info["amount"])
        if status == "failed":
            add_balance(uid, amount, "withdraw_refund", client_id)
            day_add("wd_failed")
        else:
            stat_add("withdrawn", amount)
            day_user("wd_done", uid, amount)
        save_state()
        left = balance(uid)
    if status == "finished":
        safe_send(uid, t(uid, "wd_ok", amount=money(amount), bal=money(left)), menu_markup(uid))
    else:
        safe_send(uid, t(uid, "wd_fail", amount=money(amount), bal=money(left)), menu_markup(uid))
    if status == "finished":
        notify_admin_withdraw("✅ <b>Withdrawal COMPLETED</b>", uid, amount, client_id)
    else:
        notify_admin_withdraw(
            "❌ <b>Withdrawal FAILED</b>", uid, amount, client_id, "Amount returned to the user's bot balance."
        )


def flag_payout_for_review(client_id):
    with lock:
        info = state["payouts"].get(client_id)
        if not info or info.get("flagged"):
            return
        info["flagged"] = True
        save_state()
        uid = info["user_id"]
        amount = info["amount"]
    safe_send(
        ADMIN_ID,
        "⚠️ <b>Withdrawal needs manual review</b>\n"
        f"User: <code>{uid}</code>\n"
        f"Amount: <b>{amount} USDT</b>\n"
        f"Client ID: <code>{html.escape(client_id)}</code>\n\n"
        "xRocket does not know this payout. First check your xRocket app history.\n"
        f"• Money was NOT sent → /payout_fail {html.escape(client_id)}\n"
        f"• Money WAS sent → /payout_ok {html.escape(client_id)}",
    )


def poller():
    while True:
        with lock:
            invoices = list(state["invoices"].items())
            payouts = list(state["payouts"].items())
        for invoice_id, inv in invoices:
            try:
                data = get_invoice(invoice_id)
                status = data.get("status") if data else None
                if status == "paid":
                    handle_paid(invoice_id)
                elif status in ("expired", "cancelled") or time.time() - inv["created"] > PENDING_MAX_AGE:
                    with lock:
                        gone = state["invoices"].pop(invoice_id, None)
                        if gone and status == "expired" and not gone.get("cancelled"):
                            add_strike(gone["user_id"])
                        save_state()
            except Exception as e:
                print("poller invoice error:", invoice_id, e)
        for client_id, info in payouts:
            try:
                code, data = api_get_payout(info.get("payout_id"), client_id)
                if data:
                    resolve_payout(client_id, data.get("status"))
                elif code == 404 and time.time() - info["created"] > PAYOUT_REVIEW_SECONDS:
                    flag_payout_for_review(client_id)
            except Exception as e:
                print("poller payout error:", client_id, e)
        time.sleep(POLL_INTERVAL)


def total_liability():
    return sum((Decimal(u.get("balance", "0.00")) for u in state["users"].values()), Decimal("0"))


def send_backup(caption):
    flush_state()
    with lock:
        data = json.dumps(state, ensure_ascii=False, indent=1).encode("utf-8")
    buf = io.BytesIO(data)
    buf.name = "lottery_backup.json"
    bot.send_document(ADMIN_ID, buf, caption=caption)


def send_ledger():
    flush_state()
    with io_lock:
        data = store.get("lottery/ledger") or {}
    rows = []
    for uid, items in data.items():
        if isinstance(items, list):
            items = {str(i): v for i, v in enumerate(items) if v}
        for d in items.values():
            rows.append(row_from(uid, d))
    if not rows:
        safe_send(ADMIN_ID, "📒 The ledger is empty.")
        return
    rows.sort(key=lambda row: row[0])
    out = io.StringIO()
    writer = csv.writer(out)
    writer.writerow(["time_utc", "user_id", "type", "amount", "balance_after", "ref"])
    writer.writerows(rows)
    buf = io.BytesIO(out.getvalue().encode("utf-8"))
    buf.name = "ledger.csv"
    bot.send_document(ADMIN_ID, buf, caption="📒 Full ledger")


def user_ledger(uid, limit=20):
    rows = ledger_rows(uid)
    if limit is None:
        return rows
    return rows[-limit:]


def check_solvency():
    with lock:
        liability = total_liability()
    bal = app_balance()
    if bal is None:
        if solv["state"] != "unknown":
            solv["state"] = "unknown"
            safe_send(ADMIN_ID, "⚠️ Could not read the xRocket app balance. Check the console output.")
        return
    required = liability * (1 + SOLVENCY_BUFFER)
    new_state = "low" if bal < required else "ok"
    previous = solv["state"]
    if new_state == previous:
        return
    solv["state"] = new_state
    if new_state == "low":
        safe_send(
            ADMIN_ID,
            "⚠️ <b>LOW APP BALANCE</b>\n"
            f"User balances owed: <b>{money(liability)} USDT</b>\n"
            f"xRocket app balance: <b>{money(bal)} USDT</b>\n"
            f"Needed (+{int(SOLVENCY_BUFFER * 100)}% buffer): <b>{money(required)} USDT</b>\n"
            "Please top up your xRocket app balance.",
        )
    elif previous == "low":
        safe_send(ADMIN_ID, f"✅ App balance is healthy again: <b>{money(bal)} USDT</b>")


def admin_loop():
    last_backup = time.time()
    last_check = 0.0
    while True:
        try:
            now = time.time()
            try:
                maybe_send_daily_report()
            except Exception as e:
                print("daily report error:", e)
            if now - last_check >= SOLVENCY_INTERVAL:
                last_check = now
                check_solvency()
            if now - last_backup >= BACKUP_INTERVAL:
                last_backup = now
                send_backup("⏰ Hourly backup")
        except Exception as e:
            print("admin loop error:", e)
        time.sleep(30)


def admin_text():
    with lock:
        liability = total_liability()
        stats = dict(state["stats"])
        users = len(state["users"])
        round_lines = []
        for tier in TIER_ORDER:
            r = current_round(tier)
            if r:
                round_lines.append(f"{tier_label(tier)}: #{r['id']} ({len(r['entries'])}/{SLOTS}, {r['status']})")
            else:
                round_lines.append(f"{tier_label(tier)}: none")
        paused = state.get("paused", False)
    bal = app_balance()
    required = liability * (1 + SOLVENCY_BUFFER)
    if bal is None:
        bal_text = "unknown"
        health = "❓ Could not read app balance"
    else:
        bal_text = f"{money(bal)} USDT"
        health = "✅ Safe" if bal >= required else "⚠️ LOW — top up"
    return (
        "🛠 <b>Admin Dashboard</b>\n"
        f"{SEP}\n"
        "🎰 Current rounds:\n" + "\n".join(round_lines) + "\n"
        f"✅ Finished rounds: {stats.get('finished', 0)}  •  ⌛ Closed: {stats.get('closed', 0)}\n"
        f"👥 Users: {users}  •  🎟 Tickets sold: {stats.get('tickets', 0)}\n"
        f"💵 Fees earned: {stats.get('fees', '0.00')} USDT\n"
        f"🏆 Prizes credited: {stats.get('prizes', '0.00')} USDT\n"
        f"💸 Withdrawn: {stats.get('withdrawn', '0.00')} USDT\n"
        f"👥 Referral: {fmt_pct(ref_percent())}%  •  paid {stats.get('ref_paid', '0.00')} USDT\n"
        f"💳 Withdrawals: {'ON' if state.get('wd_enabled', True) else 'OFF'}  •  ⏳ Reviews waiting: {len(state.get('approvals', {}))}\n"
        f"🖼 Pictures: " + "  •  ".join(f"{tier_label(t_)} {'✅' if tier_image(t_) else '—'}" for t_ in TIER_ORDER) + "\n"
        f"{SEP}\n"
        f"🧾 User balances owed: <b>{money(liability)} USDT</b>\n"
        f"🏦 xRocket app balance: <b>{bal_text}</b>\n"
        f"🛡 Needed with {int(SOLVENCY_BUFFER * 100)}% buffer: {money(required)} USDT\n"
        f"Status: {health}\n"
        f"⏸ Paused: {'yes' if paused else 'no'}\n"
        f"🕒 {fmt_time(time.time(), 'en')}"
    )


def admin_markup():
    paused = state.get("paused", False)
    kb = types.InlineKeyboardMarkup()
    kb.row(
        types.InlineKeyboardButton("🔄 Refresh", callback_data="ad:refresh"),
        types.InlineKeyboardButton("💾 Backup", callback_data="ad:backup"),
    )
    kb.row(
        types.InlineKeyboardButton("📒 Ledger CSV", callback_data="ad:ledger"),
        types.InlineKeyboardButton("▶️ Resume" if paused else "⏸ Pause", callback_data="ad:pause"),
    )
    kb.row(
        types.InlineKeyboardButton("➖ Ref 0.5%", callback_data="ad:refdown"),
        types.InlineKeyboardButton("➕ Ref 0.5%", callback_data="ad:refup"),
    )
    kb.row(
        types.InlineKeyboardButton("📣 Broadcast", callback_data="ad:bc"),
        types.InlineKeyboardButton("🖼 Images", callback_data="ad:images"),
    )
    kb.row(
        types.InlineKeyboardButton("📊 Today's report", callback_data="ad:report"),
        types.InlineKeyboardButton("📖 How to use bot", callback_data="ad:howto"),
    )
    return kb


def is_admin(uid):
    return uid == ADMIN_ID


@bot.message_handler(commands=["admin", "stats"])
def on_admin(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    safe_send(message.chat.id, admin_text(), admin_markup())


@bot.message_handler(commands=["backup"])
def on_backup(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    try:
        send_backup("💾 Manual backup")
    except Exception as e:
        safe_send(message.chat.id, f"❌ Backup failed: {html.escape(str(e))}")


@bot.message_handler(commands=["ledger"])
def on_ledger(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    try:
        send_ledger()
    except Exception as e:
        safe_send(message.chat.id, f"❌ Failed: {html.escape(str(e))}")


@bot.message_handler(commands=["pause", "resume"])
def on_pause(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    pause = (message.text or "").startswith("/pause")
    with lock:
        state["paused"] = pause
        save_state()
    safe_send(
        message.chat.id,
        "⏸ New rounds are paused. The current rounds will finish normally." if pause else "▶️ New rounds are enabled again.",
    )


@bot.message_handler(commands=["payout_ok", "payout_fail"])
def on_payout_manual(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split()
    if len(parts) < 2:
        safe_send(message.chat.id, "Usage: /payout_ok CLIENT_ID  or  /payout_fail CLIENT_ID")
        return
    client_id = parts[1]
    with lock:
        exists = client_id in state["payouts"]
    if not exists:
        safe_send(message.chat.id, "Pending payout not found (already resolved?).")
        return
    ok = parts[0].startswith("/payout_ok")
    resolve_payout(client_id, "finished" if ok else "failed")
    safe_send(message.chat.id, "✅ Marked as sent." if ok else "↩️ Refunded to the user's bot balance.")


def user_details(uid):
    rows = user_ledger(uid, 10)  # read outside the lock
    with lock:
        rec = state["users"].get(str(uid))
        if not rec:
            return None
        bal = money(balance(uid))
        name = html.escape(rec.get("name", ""))
        username = html.escape(rec.get("username", ""))
        lang = rec.get("lang") or "not set"
        refs = sum(1 for u in state["users"].values() if u.get("ref_by") == uid)
        income = rec.get("ref_income", "0.000")
        ref_tickets = int(rec.get("ref_tickets", 0))
        banned = bool(rec.get("banned"))
        blocked = int(rec.get("join_block_until", 0) - time.time())
    lines = [f"{r[0]} | {r[2]} | {r[3]} | bal {r[4]}" for r in rows]
    body = html.escape("\n".join(lines)) if lines else "No transactions yet."
    status = "🚫 BANNED" if banned else "✅ active"
    if blocked > 0:
        status += f"  •  ⛔ join paused {fmt_left(blocked)}"
    text = (
        f"👤 <b>User {uid}</b>\nName: {name} @{username}\nLanguage: {lang}\nStatus: {status}\n"
        f"💰 Balance: <b>{bal} USDT</b>\n"
        f"👥 Total referrals: <b>{refs}</b>\n"
        f"💸 Total referral income: <b>{income} USDT</b>\n"
        f"🎟 Tickets bought by referrals: <b>{ref_tickets}</b>\n\n"
        f"🧾 Last transactions:\n<pre>{body}</pre>"
    )
    kb = types.InlineKeyboardMarkup()
    kb.row(
        types.InlineKeyboardButton("🚫 Ban", callback_data=f"bn:ban:{uid}"),
        types.InlineKeyboardButton("✅ Unban", callback_data=f"bn:unban:{uid}"),
    )
    return text, kb


def set_ban(uid, flag):
    """Returns None (unknown user), "same" (nothing changed), "done" or "undelivered".
    The user is told about every real change (banned users still receive notifications)."""
    with lock:
        rec = state["users"].get(str(uid))
        if not rec:
            return None
        if bool(rec.get("banned")) == bool(flag):
            return "same"
        rec["banned"] = bool(flag)
        day_add("bans" if flag else "unbans")
        save_state()
    delivered = try_send(uid, t(uid, "ban_dm" if flag else "unban_dm"), None if flag else menu_markup(uid))
    return "done" if delivered else "undelivered"


def ban_result_text(res, flag):
    if res is None:
        return "User not found."
    word = "banned" if flag else "unbanned"
    icon = "🚫" if flag else "✅"
    if res == "same":
        return f"Already {word}. Nothing changed."
    if res == "undelivered":
        return f"{icon} User {word}. ⚠️ The notification could NOT be delivered (the user may have blocked the bot)."
    return f"{icon} User {word}. The user was notified."


@bot.message_handler(commands=["user"])
def on_user(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split()
    if len(parts) < 2 or not parts[1].isdigit():
        safe_send(message.chat.id, "Usage: /user 123456789")
        return
    details = user_details(int(parts[1]))
    if details is None:
        safe_send(message.chat.id, "User not found.")
        return
    safe_send(message.chat.id, details[0], details[1])


@bot.callback_query_handler(func=lambda c: c.data.startswith("bn:"))
def on_ban_button(call):
    if not is_admin(call.from_user.id):
        ack(call)
        return
    _, action, raw = call.data.split(":")
    uid = int(raw)
    res = set_ban(uid, action == "ban")
    if res is None:
        ack(call, "User not found.", True)
        return
    ack(call, ban_result_text(res, action == "ban"), True)
    details = user_details(uid)
    if details:
        edit_or_send(call.message.chat.id, call.message.message_id, details[0], details[1])


@bot.message_handler(commands=["block", "unblock", "ban", "unban"])
def on_block_command(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split()
    if len(parts) < 2 or not parts[1].isdigit():
        safe_send(message.chat.id, "Usage: /ban 123456789  or  /unban 123456789")
        return
    block = parts[0].startswith(("/block", "/ban"))
    safe_send(message.chat.id, ban_result_text(set_ban(int(parts[1]), block), block))


@bot.message_handler(commands=["wd_off", "wd_on"])
def on_withdraw_switch(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    on = (message.text or "").startswith("/wd_on")
    with lock:
        state["wd_enabled"] = on
        save_state()
    safe_send(message.chat.id, "▶️ Withdrawals are ON." if on else "⏸ Withdrawals are OFF for everyone.")


@bot.callback_query_handler(func=lambda c: c.data.startswith("ad:"))
def on_admin_cb(call):
    if not is_admin(call.from_user.id):
        ack(call)
        return
    action = call.data.split(":", 1)[1]
    ack(call)
    if action == "bc":
        start_broadcast_flow(call.message.chat.id)
        return
    if action == "images":
        show_images(call.message.chat.id)
        return
    if action == "report":
        if not send_report(bdt_day(), partial=True):
            safe_send(call.message.chat.id, "❌ Could not send the report.")
        return
    if action == "howto":
        show_howto(call.message.chat.id, call.message.message_id)
        return
    if action == "pause":
        with lock:
            state["paused"] = not state.get("paused", False)
            save_state()
    elif action in ("refup", "refdown"):
        step = Decimal("0.5") if action == "refup" else Decimal("-0.5")
        set_ref_percent(ref_percent() + step)
    elif action == "backup":
        try:
            send_backup("💾 Manual backup")
        except Exception as e:
            safe_send(call.message.chat.id, f"❌ Backup failed: {html.escape(str(e))}")
    elif action == "ledger":
        try:
            send_ledger()
        except Exception as e:
            safe_send(call.message.chat.id, f"❌ Failed: {html.escape(str(e))}")
    edit_or_send(call.message.chat.id, call.message.message_id, admin_text(), admin_markup())


# =====================================================================
# Admin tools: lottery pictures, broadcast, daily report, "How to use bot"
# =====================================================================
IMG_KEYS = {"classic": "A", "a": "A", "premium": "B", "b": "B"}
BROADCAST_DELAY = 0.05  # seconds between messages (about 20 per second, below Telegram's limit)
bc = {"running": False, "draft": None}
report_retry = {"at": 0.0}


def parse_tier_arg(text):
    parts = (text or "").split()
    if len(parts) < 2:
        return None
    return IMG_KEYS.get(parts[1].strip().lower())


def do_setimage(message, arg_text, photo_msg):
    chat = message.chat.id
    tier = parse_tier_arg(arg_text)
    if tier is None:
        safe_send(chat, "Usage: send a photo with the caption <code>/setimage classic</code> or <code>/setimage premium</code>.")
        return
    photos = getattr(photo_msg, "photo", None) if photo_msg is not None else None
    if not photos:
        if photo_msg is not None and getattr(photo_msg, "document", None):
            safe_send(chat, "❌ Please send it as a normal <b>photo</b> (not 'as file') and write the command in the caption.")
        else:
            safe_send(chat, "❌ No photo found. Send a photo with the caption /setimage classic (or premium), or reply to a photo with the command.")
        return
    file_id = photos[-1].file_id
    with lock:
        state.setdefault("images", {})[tier] = file_id
        save_state()
    try:
        bot.send_photo(
            chat,
            file_id,
            caption=f"✅ {tier_label(tier)} picture saved.\nIt is used from the next round: main post + reminders.",
        )
    except Exception as e:
        safe_send(chat, f"✅ Saved, but I could not show it: {html.escape(str(e))}")


def photo_cmd_filter(m):
    return (getattr(m, "caption", None) or "").strip().lower().startswith("/setimage")


@bot.message_handler(content_types=["photo", "document"], func=photo_cmd_filter)
def on_setimage_photo(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    do_setimage(message, message.caption, message)


@bot.message_handler(commands=["setimage"])
def on_setimage_text(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    do_setimage(message, message.text, getattr(message, "reply_to_message", None))


@bot.message_handler(commands=["delimage"])
def on_delimage(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    tier = parse_tier_arg(message.text)
    if tier is None:
        safe_send(message.chat.id, "Usage: /delimage classic  or  /delimage premium")
        return
    with lock:
        had = bool((state.get("images") or {}).pop(tier, None))
        save_state()
    safe_send(
        message.chat.id,
        f"🗑 {tier_label(tier)} picture removed. New rounds will be text posts." if had else f"{tier_label(tier)} had no picture.",
    )


def show_images(chat_id):
    for tier in TIER_ORDER:
        file_id = tier_image(tier)
        if file_id:
            try:
                bot.send_photo(chat_id, file_id, caption=f"{tier_label(tier)} — current picture")
                continue
            except Exception as e:
                safe_send(chat_id, f"{tier_label(tier)} — picture is set but cannot be shown: {html.escape(str(e))}")
                continue
        safe_send(chat_id, f"{tier_label(tier)} — no picture set (text post).")
    safe_send(
        chat_id,
        "🖼 <b>How to set or change a picture</b>\n"
        "Send the picture to this bot as a normal photo and write <code>/setimage classic</code> or "
        "<code>/setimage premium</code> in the caption.\n"
        "Remove with /delimage classic or /delimage premium.\n"
        "It is used from the next round (main post + reminders).",
    )


@bot.message_handler(commands=["images"])
def on_images(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    show_images(message.chat.id)


# ---------------------------------------------------------------- broadcast
def start_broadcast_flow(chat_id):
    if bc["running"]:
        safe_send(chat_id, "⏳ A broadcast is still being sent. Please wait until it finishes.")
        return
    msg = bot.send_message(
        chat_id,
        "📣 <b>New broadcast</b>\n"
        f"{SEP}\n"
        "Send the message now:\n"
        "• plain text (bold, italic and links work), or\n"
        "• a photo with a caption (caption max 1024 characters).\n\n"
        "It will go to <b>ALL users, banned ones too</b>. You will see a preview first.\n"
        "Send /cancel to stop.",
        parse_mode="HTML",
    )
    bot.register_next_step_handler(msg, receive_broadcast)


def send_broadcast_item(chat_id, item):
    if item["kind"] == "photo":
        bot.send_photo(chat_id, item["file_id"], caption=item["caption"] or None, parse_mode="HTML")
    else:
        bot.send_message(chat_id, item["text"], parse_mode="HTML")


def receive_broadcast(message):
    if message.from_user.id != ADMIN_ID:
        return
    chat_id = message.chat.id
    ctype = getattr(message, "content_type", "text")
    text = (getattr(message, "text", None) or "").strip()
    if ctype == "text" and text.startswith("/"):
        safe_send(chat_id, "❎ Broadcast cancelled.")
        return
    if ctype == "text" and text:
        item = {"kind": "text", "text": getattr(message, "html_text", None) or text}
        if len(item["text"]) > 4000:
            safe_send(chat_id, "❌ Too long (max 4000 characters). Send a shorter text, or /cancel.")
            bot.register_next_step_handler(message, receive_broadcast)
            return
    elif ctype == "photo" and getattr(message, "photo", None):
        caption = getattr(message, "html_caption", None) or getattr(message, "caption", None) or ""
        if len(caption) > 1000:
            safe_send(chat_id, "❌ The caption is too long (max 1024 characters). Send it again, or /cancel.")
            bot.register_next_step_handler(message, receive_broadcast)
            return
        item = {"kind": "photo", "file_id": message.photo[-1].file_id, "caption": caption}
    else:
        safe_send(chat_id, "❌ Only text or a photo (with caption) can be broadcast. Send it again, or /cancel.")
        bot.register_next_step_handler(message, receive_broadcast)
        return
    try:
        send_broadcast_item(chat_id, item)  # the preview: exactly what everyone will get
    except Exception as e:
        safe_send(chat_id, f"❌ This message cannot be sent: {html.escape(str(e))}\nFix it and send again with the 📣 button.")
        return
    with lock:
        count = len(state["users"])
        draft_id = int(time.time() * 1000)
        bc["draft"] = dict(item, id=draft_id)
    kb = types.InlineKeyboardMarkup()
    kb.row(
        types.InlineKeyboardButton(f"✅ Send to {count} users", callback_data=f"bc:go:{draft_id}"),
        types.InlineKeyboardButton("❌ Cancel", callback_data=f"bc:no:{draft_id}"),
    )
    safe_send(
        chat_id,
        f"👆 <b>Preview</b>\nReceivers: <b>{count}</b> users (everyone who ever started the bot, banned users included).\nSend it?",
        kb,
    )


def retry_after(exc):
    try:
        return int((getattr(exc, "result_json", None) or {}).get("parameters", {}).get("retry_after") or 0)
    except (TypeError, ValueError, AttributeError):
        return 0


def broadcast_worker(item, admin_chat):
    try:
        with lock:
            ids = sorted(int(k) for k in state["users"])
        sent = blocked = failed = 0
        started = time.time()
        safe_send(admin_chat, f"📤 Sending to <b>{len(ids)}</b> users... I will send you a report when it is done.")
        for uid in ids:
            for _attempt in range(3):
                try:
                    send_broadcast_item(uid, item)
                    sent += 1
                    break
                except ApiTelegramException as e:
                    wait = retry_after(e)
                    if getattr(e, "error_code", None) == 429 or wait:
                        time.sleep(min(wait or 5, 60))
                        continue
                    if getattr(e, "error_code", None) in (400, 403):
                        blocked += 1  # the user blocked the bot or deleted the account
                    else:
                        failed += 1
                    break
                except Exception as e:
                    print("broadcast error:", uid, e)
                    failed += 1
                    break
            else:
                failed += 1
            time.sleep(BROADCAST_DELAY)
        day_add("broadcasts")
        secs = int(time.time() - started)
        safe_send(
            admin_chat,
            "✅ <b>Broadcast finished</b>\n"
            f"{SEP}\n"
            f"👥 Users: {len(ids)}\n"
            f"✅ Delivered: <b>{sent}</b>\n"
            f"🚫 Not delivered (blocked the bot / account gone): {blocked}\n"
            f"⚠️ Failed for other reasons: {failed}\n"
            f"⏱ Time: {secs}s",
        )
    except Exception as e:
        print("broadcast worker error:", e)
        safe_send(admin_chat, f"❌ Broadcast stopped by an error: {html.escape(str(e))}")
    finally:
        bc["running"] = False


@bot.message_handler(commands=["broadcast"])
def on_broadcast_cmd(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    start_broadcast_flow(message.chat.id)


@bot.callback_query_handler(func=lambda c: c.data.startswith("bc:"))
def on_broadcast_cb(call):
    if not is_admin(call.from_user.id):
        ack(call)
        return
    _, action, raw = call.data.split(":")
    chat_id = call.message.chat.id
    if action == "no":
        with lock:
            if bc["draft"] and str(bc["draft"]["id"]) == raw:
                bc["draft"] = None
        clear_markup(call)
        ack(call, "Cancelled")
        safe_send(chat_id, "❎ Broadcast cancelled.")
        return
    with lock:
        draft = bc["draft"]
        if not draft or str(draft["id"]) != raw:
            problem = "This draft is no longer valid. Create a new broadcast."
        elif bc["running"]:
            problem = "A broadcast is already being sent."
        else:
            problem = None
            bc["running"] = True  # set under the lock: a double tap cannot start two sends
            bc["draft"] = None
    clear_markup(call)
    if problem:
        ack(call, problem, True)
        return
    ack(call, "Sending started")
    threading.Thread(target=broadcast_worker, args=(draft, chat_id), daemon=True).start()


# ---------------------------------------------------------------- daily report
def user_tag(uid):
    rec = state["users"].get(str(uid), {})
    uname = rec.get("username")
    return f"<code>{uid}</code>" + (f" @{html.escape(uname)}" if uname else "")


def top_lines(mapping, limit=15, suffix=" USDT"):
    items = sorted(mapping.items(), key=lambda kv: Decimal(str(kv[1])), reverse=True)
    lines = [f"   • {user_tag(k)} — <b>{v}{suffix}</b>" for k, v in items[:limit]]
    if len(items) > limit:
        lines.append(f"   … and {len(items) - limit} more")
    return lines


def build_daily_report(day, partial=False):
    app_bal = app_balance()  # network call: outside the lock
    with lock:
        d = json.loads(json.dumps(state.get("daily", {}).get(day, {})))
        users_total = len(state["users"])
        banned_total = sum(1 for u in state["users"].values() if u.get("banned"))
        owed = total_liability()
        pending_wd = len(state["payouts"])
        reviews = len(state.get("approvals", {}))

        def gi(key):
            return int(d.get(key, 0))

        def gd(key):
            return Decimal(str(d.get(key, "0")))

        def gm(key):
            return d.get(key) or {}

        try:
            label = datetime.strptime(day, "%Y-%m-%d").strftime("%d %b %Y")
        except ValueError:
            label = day
        games = {t_: gi(f"games_{t_}") for t_ in TIER_ORDER}
        closed = {t_: gi(f"closed_{t_}") for t_ in TIER_ORDER}
        tickets_x = {t_: gi(f"tickets_{t_}_x") for t_ in TIER_ORDER}
        tickets_b = {t_: gi(f"tickets_{t_}_bal") for t_ in TIER_ORDER}
        ticket_total = sum(tickets_x.values()) + sum(tickets_b.values())
        fees, prizes, refunds = gd("fees"), gd("prizes"), gd("refunds")
        ref_paid, money_in = gd("ref_paid"), gd("money_in")
        net = fees - ref_paid
        wd_req, wd_done = gm("wd_req"), gm("wd_done")
        wd_users = sorted(set(wd_req) | set(wd_done), key=lambda k: Decimal(str(wd_req.get(k, wd_done.get(k, "0")))), reverse=True)
        wd_lines = []
        for k in wd_users[:15]:
            wd_lines.append(
                f"   • {user_tag(k)} — requested <b>{wd_req.get(k, '0.000')}</b> • completed <b>{wd_done.get(k, '0.000')}</b> USDT"
            )
        if len(wd_users) > 15:
            wd_lines.append(f"   … and {len(wd_users) - 15} more")
        wd_req_total = sum((Decimal(str(v)) for v in wd_req.values()), Decimal("0"))
        wd_done_total = sum((Decimal(str(v)) for v in wd_done.values()), Decimal("0"))
        earners = top_lines(gm("ref_earners"))
        winners = top_lines(gm("winners"))
        n_earners, n_winners, n_players = len(gm("ref_earners")), len(gm("winners")), len(gm("players"))

    def per_tier(values):
        return " • ".join(f"{tier_label(t_)}: <b>{values[t_]}</b>" for t_ in TIER_ORDER)

    head = "📊 <b>Daily report</b> — " + label
    if partial:
        head += " (so far)"
    lines = [
        head,
        "🕛 Bangladesh time, 12:00 AM – 12:00 AM",
        SEP,
        f"🎲 <b>Dice games played:</b> {sum(games.values())}",
        f"   {per_tier(games)}",
        f"⌛ Rounds closed (refunded): {sum(closed.values())}  ({per_tier(closed)})",
        SEP,
        f"🎟 <b>Tickets sold:</b> {ticket_total}",
    ]
    for t_ in TIER_ORDER:
        lines.append(f"   {tier_label(t_)}: {tickets_x[t_]} paid with xRocket + {tickets_b[t_]} paid with balance")
    lines += [
        f"👤 Active players: <b>{n_players}</b>",
        f"🆕 New users: <b>{gi('new_users')}</b>  •  👥 Total users: {users_total}  •  🚫 Banned: {banned_total}",
        f"🔗 New referrals: <b>{gi('new_refs')}</b>",
        SEP,
        f"💵 <b>Money in via xRocket:</b> {money(money_in)} USDT",
        f"🏆 Prizes credited: {money(prizes)} USDT",
        f"↩️ Refunded to balances (closed rounds): {money(refunds)} USDT",
        f"🏦 Platform fees earned: {money(fees)} USDT",
        f"🤝 Referral commission paid: {money(ref_paid)} USDT ({n_earners} earners)",
    ]
    lines += earners
    lines += [
        f"💰 <b>Net income</b> (fees − referral): <b>{money(net)} USDT</b>",
        SEP,
        f"🥇 <b>Winners:</b> {n_winners} users",
    ]
    lines += winners
    lines += [
        SEP,
        "💸 <b>Withdrawals</b>",
        f"   Requested: {money(wd_req_total)} USDT • Completed: <b>{money(wd_done_total)} USDT</b> "
        f"• Failed: {gi('wd_failed')} • Sent to review: {gi('wd_review')}",
    ]
    lines += wd_lines or ["   none"]
    lines += [
        SEP,
        f"🛡 Bans: {gi('bans')} • Unbans: {gi('unbans')} • 12h join blocks: {gi('strike_blocks')} • Late-payment refunds: {gi('late_refunds')}",
        f"📣 Broadcasts sent: {gi('broadcasts')}",
        SEP,
        "🧾 <b>Right now</b>",
        f"   User balances owed: {money(owed)} USDT",
        f"   xRocket app balance: {money(app_bal) + ' USDT' if app_bal is not None else 'unknown'}",
        f"   Withdrawals in progress: {pending_wd} • Reviews waiting: {reviews}",
    ]
    return "\n".join(lines)


def send_long(chat_id, text):
    """Telegram allows 4096 characters per message: split on line breaks. Returns False if sending failed."""
    chunks, cur = [], ""
    for line in text.split("\n"):
        if len(cur) + len(line) + 1 > 3800 and cur:
            chunks.append(cur)
            cur = ""
        cur += line + "\n"
    if cur:
        chunks.append(cur)
    for chunk in chunks:
        try:
            bot.send_message(chat_id, chunk.rstrip("\n"), parse_mode="HTML")
        except Exception as e:
            print("report send error:", e)
            return False
    return True


def send_report(day, partial=False):
    return send_long(ADMIN_ID, build_daily_report(day, partial))


def maybe_send_daily_report():
    """At 12:00 AM Bangladesh time the previous day's report goes to the admin. Missed days are sent after a restart."""
    now = time.time()
    if now < report_retry["at"]:
        return
    today = datetime.fromtimestamp(now, BDT).date()
    with lock:
        last = state.get("last_report")
        if not last:
            state["last_report"] = (today - timedelta(days=1)).isoformat()
            save_state()
            return
        try:
            last_d = date.fromisoformat(last)
        except ValueError:
            last_d = today - timedelta(days=1)
        start = max(last_d + timedelta(days=1), today - timedelta(days=7))
        days = []
        cur = start
        while cur < today:
            days.append(cur)
            cur += timedelta(days=1)
    for d in days:
        key = d.isoformat()
        with lock:
            has_data = key in state.get("daily", {})
        if has_data or d == today - timedelta(days=1):
            if not send_report(key):
                report_retry["at"] = time.time() + 300
                return
        with lock:
            state["last_report"] = key
            save_state()


@bot.message_handler(commands=["report"])
def on_report(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split()
    today = bdt_day()
    day = today
    if len(parts) > 1:
        try:
            day = date.fromisoformat(parts[1]).isoformat()
        except ValueError:
            safe_send(message.chat.id, "Usage: /report  (today so far)  or  /report 2026-11-26")
            return
    if not send_report(day, partial=(day == today)):
        safe_send(message.chat.id, "❌ Could not send the report.")


# ---------------------------------------------------------------- how to use the bot
HOWTO = {
    "en": {
        "titles": {
            "panel": "🛠 Panel buttons",
            "cmds": "⌨️ Commands",
            "users": "🚫 Users, bans, strikes",
            "money": "💸 Withdrawals & safety",
            "media": "🖼 Pictures & broadcast",
            "auto": "⏰ Automatic things",
            "menu": "👤 What users see",
        },
        "menu": "📖 <b>How to use this bot</b>\n" + SEP + "\nEvery button and command of the admin side, and what it does. Choose a topic:",
        "panel": "🛠 <b>Admin panel buttons</b>\nOpen the panel with /admin.\n\n🔄 <b>Refresh</b> — reloads the numbers.\n💾 <b>Backup</b> — sends a full JSON backup of all data now (one also arrives every hour).\n📒 <b>Ledger CSV</b> — every balance change of every user as a CSV file.\n⏸ <b>Pause</b> / ▶️ <b>Resume</b> — Pause stops NEW rounds from starting, running rounds finish normally. Resume starts rounds again.\n➖ <b>Ref 0.5%</b> / ➕ <b>Ref 0.5%</b> — lowers / raises the referral commission by 0.5% (range 0–5%). Only tickets bought after the change use the new rate.\n📣 <b>Broadcast</b> — sends one message (text or photo + caption) to ALL users, banned ones too. You see a preview and confirm first.\n🖼 <b>Images</b> — shows the picture of each lottery and how to change it.\n📊 <b>Today's report</b> — today's statistics so far. The full report comes by itself at 12:00 AM Bangladesh time.\n📖 <b>How to use bot</b> — this guide.\n\n<b>Dashboard lines:</b> current rounds, finished / closed rounds, users, tickets, fees, prizes, withdrawn, referral %, withdrawals ON/OFF, reviews waiting, balances owed vs xRocket app balance, Safe / LOW status, pictures.",
        "cmds": "⌨️ <b>Admin commands</b>\n/admin or /stats — opens the panel.\n/backup — sends a backup file.\n/ledger — sends the ledger CSV.\n/pause · /resume — stop / allow new rounds.\n/refpct 2.5 — sets the referral commission (0–5%). /refpct alone shows it.\n/user 123456789 — user's balance, referral numbers, last transactions, Ban / Unban buttons.\n/ban 123456789 · /unban 123456789 — ban / unban (/block and /unblock do the same). The user gets a message.\n/wd_off · /wd_on — switch ALL withdrawals off / on (emergency stop).\n/payout_ok CLIENT_ID — xRocket does not know a payout and the money WAS sent: mark it done.\n/payout_fail CLIENT_ID — the money was NOT sent: refund the user's balance.\n/setimage classic (or premium) — used in a photo caption, sets the lottery picture.\n/delimage classic (or premium) — removes a picture.\n/images — shows both pictures.\n/broadcast — starts a broadcast.\n/report — today so far; /report 2026-11-26 shows a past day.\n/howto — this guide.",
        "users": "🚫 <b>Users, bans and strikes</b>\n• <b>Ban</b>: the person can no longer use any button or command; clicking shows 'your account is restricted'. They STILL receive notifications (wins, refunds, withdrawal results, admin messages, broadcasts).\n• When you ban or unban, the user gets a message and you are told whether it was delivered.\n• <b>3-strike rule</b>: reserving a number and not paying is a strike. With 2 strikes, the next time the user picks a number a <b>warning</b> appears (Continue / Cancel). The 3rd unpaid reservation blocks joining for <b>12 hours</b>; balance, withdraw and menu still work. One paid ticket resets the count. You get a message when someone is blocked.\n• /user shows total referrals, referral income, tickets bought by referrals and the last 10 transactions.",
        "money": "💸 <b>Withdrawals and safety</b>\n• Every withdrawal is checked against the user's history. If the balance is higher than the history explains, nothing is sent: you get a message with <b>Approve / Reject</b>, and the user is told it needs a manual review.\n• ✅ Approve: the withdrawal is sent and the difference is accepted from then on. ❌ Reject: nothing is sent, balance unchanged.\n• Every withdrawal sends you a notice (new / completed / failed) with name, username, ID and time.\n• ⚠️ 'LOW APP BALANCE': user balances + 10% are above your xRocket app balance. Top up xRocket.\n• /wd_off stops all withdrawals at once; /pause only stops new rounds.\n• Payment cancelled or expired: no ticket, no loss. A payment that arrives late is refunded to the user's balance.",
        "media": "🖼 <b>Pictures and broadcast</b>\n<b>Lottery pictures</b> (one per lottery)\n1. Send the picture to this bot as a normal photo (not 'as file').\n2. Write /setimage classic or /setimage premium as the CAPTION. (Or send the photo first, then reply to it with the command.)\n3. The bot confirms and shows it. It is used from the NEXT round: the main post and the 10 / 20 minute reminders. Running rounds stay as they are.\n• /delimage classic removes it. /images shows what is set.\n• Countdown, duplicate and winner mini-posts and the result post stay text.\n\n<b>Broadcast</b>\n1. Tap 📣 Broadcast (or /broadcast).\n2. Send the text, or a photo with a caption (max 1024 characters). Bold, italic and links work.\n3. The bot shows a preview and the number of receivers. Tap ✅ Send or ❌ Cancel.\n4. It is sent slowly in the background to ALL users, banned ones too. You get a report: delivered / blocked / failed.\n• One broadcast at a time. Do not restart the bot while one is running.",
        "auto": "⏰ <b>What the bot does by itself</b>\n• <b>Daily report</b> at 12:00 AM Bangladesh time: games, tickets, new users, referrals, withdrawals per user, income and more. If the bot was off at midnight it is sent when the bot is back.\n• <b>Hourly backup</b> file.\n• <b>Balance check</b> every 10 minutes (LOW APP BALANCE alert).\n• <b>Reminder posts</b>: Classic every 10 min, Premium every 20 min; the old one is deleted. With the lottery picture if set.\n• <b>Pin / unpin</b>: the lottery post is pinned while the round runs and unpinned after the result (the bot needs the 'Pin messages' right).\n• <b>Draw</b>: when a round is full and everyone has chosen a name: 1️⃣2️⃣3️⃣ countdown, then 3 live dice. Two full lotteries are drawn one after the other (10 s gap); a new round is posted right after each result.\n• <b>Round closes</b> after 24 h without 6 players: every ticket is refunded to balances.\n• <b>Referral commission</b> is paid after the round finishes, only on tickets paid through xRocket.\n• Data lives in Firebase; only one bot instance is active at a time.",
        "menu_users": "👤 <b>What users see</b>\n🎟 <b>Join Lottery</b> — open lotteries (Classic / Premium) → pick a number → pay with xRocket or balance → choose how the name appears.\n📜 <b>Transactions</b> — tickets, wins, refunds, referral bonuses, withdrawals with status.\n💸 <b>Withdraw</b> — amount → confirm → sent to the user's xRocket wallet (may need your review).\n🌐 <b>Language</b> — English, বাংলা, 中文, हिन्दी.\n👥 <b>Refer</b> — personal link, commission, statistics.\n📖 <b>Guide</b> — explains everything in the user's language.\n• /start and /menu open the menu.",
        "back": "⬅️ Back to guide",
        "panel_btn": "🛠 Admin panel",
    },
    "bn": {
        "titles": {
            "panel": "🛠 প্যানেলের বাটন",
            "cmds": "⌨️ কমান্ড",
            "users": "🚫 ইউজার, ব্যান, স্ট্রাইক",
            "money": "💸 উইথড্র ও নিরাপত্তা",
            "media": "🖼 ছবি ও Broadcast",
            "auto": "⏰ নিজে নিজে যা হয়",
            "menu": "👤 ইউজার যা দেখে",
        },
        "menu": "📖 <b>বট কীভাবে ব্যবহার করবেন</b>\n" + SEP + "\nঅ্যাডমিন সাইডের প্রতিটা বাটন ও কমান্ড কিসের জন্য, কী করলে কী হয় — সব এখানে। একটা বিষয় বাছুন:",
        "panel": "🛠 <b>অ্যাডমিন প্যানেলের বাটন</b>\n/admin দিলে প্যানেল খোলে।\n\n🔄 <b>Refresh</b> — সংখ্যাগুলো নতুন করে দেখায়।\n💾 <b>Backup</b> — এখনই সব ডেটার পুরো JSON ব্যাকআপ পাঠায় (প্রতি ঘণ্টায় নিজে থেকেও আসে)।\n📒 <b>Ledger CSV</b> — সব ইউজারের প্রতিটা ব্যালেন্স পরিবর্তন CSV ফাইলে।\n⏸ <b>Pause</b> / ▶️ <b>Resume</b> — Pause দিলে নতুন রাউন্ড শুরু হয় না, চলমান রাউন্ড ঠিকমতো শেষ হয়। Resume দিলে আবার নতুন রাউন্ড শুরু হয়।\n➖ <b>Ref 0.5%</b> / ➕ <b>Ref 0.5%</b> — রেফার কমিশন ০.৫% কমায় / বাড়ায় (সীমা ০–৫%)। পরিবর্তনের পর কেনা টিকিটে নতুন হার লাগে।\n📣 <b>Broadcast</b> — সব ইউজারকে (ব্যান করাদেরও) একটা মেসেজ (লেখা বা ছবি + ক্যাপশন) পাঠায়। আগে প্রিভিউ দেখে নিশ্চিত করতে হয়।\n🖼 <b>Images</b> — প্রতিটা লটারির ছবি দেখায় এবং কীভাবে বদলাবেন বলে।\n📊 <b>Today's report</b> — আজকের এখন পর্যন্ত হিসাব। পূর্ণ রিপোর্ট প্রতিদিন বাংলাদেশ সময় রাত ১২টায় নিজে থেকে আসে।\n📖 <b>How to use bot</b> — এই গাইড।\n\n<b>ড্যাশবোর্ডে যা দেখা যায়:</b> চলমান রাউন্ড, শেষ / বন্ধ রাউন্ড, ইউজার, টিকিট, ফি, পুরস্কার, উইথড্র, রেফার %, উইথড্র ON/OFF, অপেক্ষমাণ রিভিউ, ইউজারদের পাওনা বনাম xRocket ব্যালেন্স, Safe / LOW অবস্থা, ছবি।",
        "cmds": "⌨️ <b>অ্যাডমিন কমান্ড</b>\n/admin বা /stats — প্যানেল খোলে।\n/backup — ব্যাকআপ ফাইল পাঠায়।\n/ledger — লেজার CSV পাঠায়।\n/pause · /resume — নতুন রাউন্ড বন্ধ / চালু।\n/refpct 2.5 — রেফার কমিশন সেট করে (০–৫%)। শুধু /refpct দিলে বর্তমান হার দেখায়।\n/user 123456789 — ইউজারের ব্যালেন্স, রেফার হিসাব, শেষ লেনদেন এবং Ban / Unban বাটন।\n/ban 123456789 · /unban 123456789 — ব্যান / আনব্যান (/block ও /unblock একই কাজ করে)। ইউজার মেসেজ পায়।\n/wd_off · /wd_on — সবার উইথড্র বন্ধ / চালু (জরুরি বন্ধ)।\n/payout_ok CLIENT_ID — xRocket যে উইথড্র চেনে না, কিন্তু টাকা গিয়েছে: সম্পন্ন হিসেবে চিহ্নিত করে।\n/payout_fail CLIENT_ID — টাকা যায়নি: ইউজারের ব্যালেন্সে ফেরত দেয়।\n/setimage classic (বা premium) — ছবির ক্যাপশনে লিখলে লটারির ছবি সেট হয়।\n/delimage classic (বা premium) — ছবি মুছে দেয়।\n/images — দুই ছবি দেখায়।\n/broadcast — Broadcast শুরু করে।\n/report — আজকের এখন পর্যন্ত হিসাব; /report 2026-11-26 দিলে আগের দিনের।\n/howto — এই গাইড।",
        "users": "🚫 <b>ইউজার, ব্যান ও স্ট্রাইক</b>\n• <b>ব্যান</b>: সে আর কোনো বাটন বা কমান্ড ব্যবহার করতে পারে না; চাপলে 'আপনার অ্যাকাউন্ট সীমাবদ্ধ' দেখায়। কিন্তু নোটিফিকেশন সে এখনো পায় (জয়, রিফান্ড, উইথড্রের ফল, অ্যাডমিনের মেসেজ, Broadcast)।\n• ব্যান বা আনব্যান করলে ইউজার মেসেজ পায়, আর মেসেজ গেছে কি না আপনাকে জানানো হয়।\n• <b>৩ স্ট্রাইক নিয়ম</b>: নম্বর রিজার্ভ করে পেমেন্ট না করলে ১ স্ট্রাইক। ২ স্ট্রাইক হলে পরের বার নম্বর বাছাই করার সময় <b>সতর্কবার্তা</b> আসে (Continue / Cancel)। ৩য় বার পেমেন্ট না করলে <b>১২ ঘণ্টা</b> জয়েন বন্ধ; ব্যালেন্স, উইথড্র ও মেনু চলে। একবার টিকিট কিনলেই গণনা শূন্য হয়। কেউ ব্লক হলে আপনি মেসেজ পান।\n• /user দিলে মোট রেফার, রেফার ইনকাম, রেফারদের কেনা টিকিট এবং শেষ ১০টা লেনদেন দেখা যায়।",
        "money": "💸 <b>উইথড্র ও নিরাপত্তা</b>\n• প্রতিটা উইথড্র ইউজারের লেনদেনের ইতিহাসের সাথে মেলানো হয়। ব্যালেন্স ইতিহাসের চেয়ে বেশি হলে কিছু পাঠানো হয় না: আপনি <b>Approve / Reject</b> বাটনসহ মেসেজ পান, আর ইউজারকে জানানো হয় ম্যানুয়াল রিভিউ লাগছে।\n• ✅ Approve: উইথড্র পাঠানো হয় এবং ওই পার্থক্য এরপর থেকে মেনে নেওয়া হয়। ❌ Reject: কিছু পাঠানো হয় না, ব্যালেন্স আগের মতো।\n• প্রতিটা উইথড্রে (নতুন / সম্পন্ন / ব্যর্থ) নাম, username, ID ও সময়সহ আপনি নোটিফিকেশন পান।\n• ⚠️ 'LOW APP BALANCE': ইউজারদের মোট পাওনা + ১০% আপনার xRocket ব্যালেন্সের চেয়ে বেশি। xRocket-এ টাকা যোগ করুন।\n• /wd_off দিলে সব উইথড্র একবারে বন্ধ; /pause শুধু নতুন রাউন্ড বন্ধ করে।\n• পেমেন্ট বাতিল বা মেয়াদ শেষ হলে টিকিট হয় না, টাকাও যায় না। দেরিতে আসা পেমেন্ট ইউজারের ব্যালেন্সে ফেরত যায়।",
        "media": "🖼 <b>ছবি ও Broadcast</b>\n<b>লটারির ছবি</b> (প্রতি লটারির জন্য একটা)\n১. ছবিটা বটকে সাধারণ ফটো হিসেবে পাঠান ('as file' নয়)।\n২. ক্যাপশনে লিখুন /setimage classic অথবা /setimage premium। (অথবা আগে ছবি পাঠিয়ে তাতে Reply করে কমান্ড লিখুন।)\n৩. বট নিশ্চিত করে ছবিটা দেখায়। ছবি <b>পরের রাউন্ড</b> থেকে কাজ করে: মূল পোস্ট এবং ১০ / ২০ মিনিটের রিমাইন্ডারে। চলমান রাউন্ড আগের মতোই থাকে।\n• /delimage classic দিলে ছবি মোছে। /images দিলে কী সেট আছে দেখায়।\n• কাউন্টডাউন, ডুপ্লিকেট ও বিজয়ীর ছোট পোস্ট এবং রেজাল্ট পোস্ট শুধু লেখাই থাকে।\n\n<b>Broadcast</b>\n১. 📣 Broadcast চাপুন (বা /broadcast)।\n২. লেখা, অথবা ছবি + ক্যাপশন পাঠান (ক্যাপশন সর্বোচ্চ ১০২৪ অক্ষর)। বোল্ড, ইটালিক ও লিংক কাজ করে।\n৩. বট প্রিভিউ আর প্রাপকের সংখ্যা দেখায়। ✅ Send বা ❌ Cancel চাপুন।\n৪. ব্যাকআপে ধীরে ধীরে সব ইউজারকে (ব্যান করাদেরও) পাঠায়। শেষে রিপোর্ট পান: পৌঁছেছে / ব্লক / ব্যর্থ।\n• একসাথে একটাই Broadcast চলে। চলার সময় বট রিস্টার্ট করবেন না।",
        "auto": "⏰ <b>বট নিজে নিজে যা করে</b>\n• <b>দৈনিক রিপোর্ট</b> বাংলাদেশ সময় রাত ১২টায়: গেম, টিকিট, নতুন ইউজার, রেফার, ইউজার অনুযায়ী উইথড্র, আয় ইত্যাদি। রাত ১২টায় বট বন্ধ থাকলে ফিরে এসে পাঠায়।\n• <b>প্রতি ঘণ্টায় ব্যাকআপ</b> ফাইল।\n• <b>ব্যালেন্স চেক</b> প্রতি ১০ মিনিটে (LOW APP BALANCE সতর্কতা)।\n• <b>রিমাইন্ডার পোস্ট</b>: Classic প্রতি ১০ মিনিটে, Premium প্রতি ২০ মিনিটে; পুরনোটা মুছে যায়। ছবি সেট থাকলে ছবিসহ।\n• <b>পিন / আনপিন</b>: রাউন্ড চলার সময় লটারি পোস্ট পিন থাকে, রেজাল্টের পর আনপিন হয় (চ্যানেলে বটের 'Pin messages' অধিকার লাগে)।\n• <b>ড্র</b>: রাউন্ড পূর্ণ হয়ে সবাই নাম বাছাই করলে 1️⃣2️⃣3️⃣ কাউন্টডাউন, তারপর ৩টা লাইভ ডাইস। দুই লটারি একসাথে পূর্ণ হলে একটার পর একটা ড্র হয় (১০ সেকেন্ড বিরতি); প্রতিটা রেজাল্টের পরই নতুন রাউন্ড পোস্ট হয়।\n• <b>রাউন্ড বন্ধ</b>: ২৪ ঘণ্টায় ৬ জন না হলে সব টিকিটের টাকা ব্যালেন্সে ফেরত যায়।\n• <b>রেফার কমিশন</b> রাউন্ড শেষ হওয়ার পর দেওয়া হয়, শুধু xRocket দিয়ে পেমেন্ট করা টিকিটে।\n• ডেটা Firebase-এ থাকে; একসাথে শুধু একটা বট ইনস্ট্যান্স সক্রিয় থাকে।",
        "menu_users": "👤 <b>ইউজার যা দেখে</b>\n🎟 <b>লটারিতে জয়েন</b> — খোলা লটারি (Classic / Premium) → নম্বর বাছাই → xRocket বা ব্যালেন্সে পেমেন্ট → নাম কীভাবে দেখাবে বাছাই।\n📜 <b>লেনদেন</b> — টিকিট, জয়, রিফান্ড, রেফার বোনাস, উইথড্র স্ট্যাটাসসহ।\n💸 <b>উইথড্র</b> — পরিমাণ → নিশ্চিত → ইউজারের xRocket ওয়ালেটে (আপনার রিভিউ লাগতে পারে)।\n🌐 <b>ভাষা</b> — English, বাংলা, 中文, हिन्दी।\n👥 <b>রেফার</b> — নিজস্ব লিংক, কমিশন, হিসাব।\n📖 <b>গাইড</b> — ইউজারের ভাষায় সবকিছু বুঝিয়ে দেয়।\n• /start ও /menu দিলে মেনু খোলে।",
        "back": "⬅️ গাইডে ফিরুন",
        "panel_btn": "🛠 অ্যাডমিন প্যানেল",
    },
}
HOWTO_ORDER = ["panel", "cmds", "users", "money", "media", "auto", "menu"]


def show_howto(chat_id, message_id=None, section=None):
    lang = "bn" if lang_of(ADMIN_ID) == "bn" else "en"
    pack = HOWTO[lang]
    kb = types.InlineKeyboardMarkup()
    if section in HOWTO_ORDER:
        key = "menu_users" if section == "menu" else section
        text = pack[key]
        kb.add(types.InlineKeyboardButton(pack["back"], callback_data="hw:menu"))
        kb.add(types.InlineKeyboardButton(pack["panel_btn"], callback_data="ad:refresh"))
    else:
        text = pack["menu"]
        buttons = [types.InlineKeyboardButton(pack["titles"][k], callback_data=f"hw:{k}") for k in HOWTO_ORDER]
        for i in range(0, len(buttons), 2):
            kb.row(*buttons[i : i + 2])
        kb.add(types.InlineKeyboardButton(pack["panel_btn"], callback_data="ad:refresh"))
    edit_or_send(chat_id, message_id, text, kb)


@bot.message_handler(commands=["howto"])
def on_howto(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    show_howto(message.chat.id)


@bot.callback_query_handler(func=lambda c: c.data.startswith("hw:"))
def on_howto_cb(call):
    if not is_admin(call.from_user.id):
        ack(call)
        return
    ack(call)
    section = call.data.split(":", 1)[1]
    show_howto(call.message.chat.id, call.message.message_id, section)


def lang_markup():
    kb = types.InlineKeyboardMarkup()
    buttons = [types.InlineKeyboardButton(label, callback_data=f"lg:{code}") for code, label in LANGS]
    for i in range(0, len(buttons), 2):
        kb.row(*buttons[i : i + 2])
    return kb


def menu_markup(uid):
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(t(uid, "btn_join"), callback_data="join"))
    kb.row(
        types.InlineKeyboardButton(t(uid, "btn_tickets"), callback_data="mine"),
        types.InlineKeyboardButton(t(uid, "btn_withdraw"), callback_data="wd"),
    )
    kb.add(types.InlineKeyboardButton(t(uid, "btn_lang"), callback_data="lang"))
    kb.row(
        types.InlineKeyboardButton(t(uid, "btn_ref"), callback_data="ref"),
        types.InlineKeyboardButton(t(uid, "btn_guide"), callback_data="guide"),
    )
    return kb


def back_markup(uid):
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(t(uid, "btn_back"), callback_data="menu"))
    return kb


def back_lot_markup(uid):
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(t(uid, "btn_back_lot"), callback_data="join"))
    return kb


def menu_text(uid):
    with lock:
        bal = balance(uid)
        paused = state.get("paused")
    text = t(uid, "menu_body", bal=money(bal))
    if paused:
        text += "\n\n" + t(uid, "menu_paused")
    return text


def show_menu(chat_id, uid, message_id=None):
    edit_or_send(chat_id, message_id, menu_text(uid), menu_markup(uid))


def ticket_status(uid, rid, num):
    r = state["rounds"].get(str(rid)) if rid is not None else None
    if r is None:
        return t(uid, "st_end")
    if r["status"] in ("open", "drawing"):
        return t(uid, "st_ongoing")
    if r["status"] == "finished":
        for i, wn in enumerate(r.get("winners") or []):
            if wn.get("number") == num and wn.get("user_id") == uid:
                return t(uid, "st_win") + " " + MEDALS[i]
        w = r.get("winner") or {}
        if w.get("number") == num and w.get("user_id") == uid:
            return t(uid, "st_win")
        return t(uid, "st_end")
    return t(uid, "st_closed")


def history_line(uid, row, refunded):
    lang = lang_of(uid)
    when, _uid, kind, amount, _after, ref = row[:6]
    stamp = short_time(when, lang)
    match = RE_TICKET.search(ref)
    rid = int(match.group(1)) if match else None
    num = int(match.group(2)) if match else None
    if rid is None:
        m2 = RE_ROUND.search(ref)
        rid = int(m2.group(1)) if m2 else None
    rr = state["rounds"].get(str(rid)) if rid is not None else None
    tname = tier_label(tier_of(rr), lang)
    rid_text = rid if rid is not None else "?"
    emoji = NUMBER_EMOJI[num - 1] if num and 1 <= num <= SLOTS else "🎟"
    try:
        value = Decimal(amount)
    except InvalidOperation:
        value = Decimal("0")
    if kind in ("ticket", "ticket_xrocket"):
        method = t(uid, "method_x" if kind == "ticket_xrocket" else "method_bal")
        return t(
            uid,
            "hist_ticket",
            tname=tname,
            rid=rid_text,
            emoji=emoji,
            amount=money(abs(value)) if kind == "ticket" else money(fee_of(rr)),
            method=method,
            status=ticket_status(uid, rid, num),
            time=stamp,
        )
    if kind == "win":
        medal = ""
        for i, wn in enumerate((rr or {}).get("winners") or []):
            if wn.get("number") == num and wn.get("user_id") == uid:
                medal = MEDALS[i] + " "
        return t(
            uid,
            "hist_win",
            tname=tname,
            rid=rid_text,
            emoji=medal + emoji,
            amount=money(abs(value)),
            time=stamp,
        )
    if kind == "ref_bonus":
        return t(uid, "hist_ref", tname=tname, rid=rid_text, amount=money(abs(value)), time=stamp)
    if kind == "refund":
        return t(uid, "hist_refund", tname=tname, rid=rid_text, amount=money(abs(value)), time=stamp)
    if kind == "late_refund":
        return t(uid, "hist_late", amount=money(abs(value)), time=stamp)
    if kind == "withdraw":
        if ref in state["payouts"]:
            status = t(uid, "st_wd_pending")
        elif ref in refunded:
            status = t(uid, "st_wd_failed")
        else:
            status = t(uid, "st_wd_done")
        return t(uid, "hist_withdraw", amount=money(abs(value)), status=status, time=stamp)
    return t(uid, "hist_other", kind=html.escape(kind), amount=money(value), time=stamp)


def history_view(uid, page):
    all_rows = user_ledger(uid, None)
    with lock:
        refunded = {r[5] for r in all_rows if r[2] == "withdraw_refund"}
        rows = [r for r in reversed(all_rows) if r[2] != "withdraw_refund"]
        if not rows:
            return t(uid, "hist_empty"), back_markup(uid)
        pages = (len(rows) + HIST_PAGE - 1) // HIST_PAGE
        page = max(0, min(page, pages - 1))
        chunk = rows[page * HIST_PAGE : (page + 1) * HIST_PAGE]
        lines = [history_line(uid, row, refunded) for row in chunk]
    text = t(uid, "hist_title", rows="\n\n".join(lines), page=page + 1, pages=pages)
    kb = types.InlineKeyboardMarkup()
    nav = []
    if page > 0:
        nav.append(types.InlineKeyboardButton(t(uid, "btn_prev"), callback_data=f"hist:{page - 1}"))
    if page < pages - 1:
        nav.append(types.InlineKeyboardButton(t(uid, "btn_next"), callback_data=f"hist:{page + 1}"))
    if nav:
        kb.row(*nav)
    kb.add(types.InlineKeyboardButton(t(uid, "btn_back"), callback_data="menu"))
    return text, kb


def join_menu(chat_id, uid, message_id=None):
    """Shows every lottery that is open right now, one button each."""
    if show_join_block(chat_id, uid, message_id):
        return
    lang = lang_of(uid)
    rows = []
    kb = types.InlineKeyboardMarkup()
    active = 0
    with lock:
        for tier in TIER_ORDER:
            r = open_round(tier)
            c = cfg(tier)
            if r:
                rows.append(t(uid, "join_row", tier=r, n=len(r["entries"]), left=time_left(r)))
                kb.add(
                    types.InlineKeyboardButton(
                        f"{c['emoji']} {tier_name(tier, lang)} • {money(c['fee'])} USDT", callback_data=f"jt:{tier}"
                    )
                )
                active += 1
            else:
                rows.append(t(uid, "join_row_off", tier=tier))
    if not active:
        edit_or_send(chat_id, message_id, t(uid, "no_round"), back_markup(uid))
        return
    kb.add(types.InlineKeyboardButton(t(uid, "btn_back"), callback_data="menu"))
    edit_or_send(chat_id, message_id, t(uid, "join_title", rows="\n\n".join(rows)), kb)


def join_flow(chat_id, uid, tier, message_id=None, confirmed=False):
    if show_join_block(chat_id, uid, message_id):
        return
    lang = lang_of(uid)
    markup = back_lot_markup(uid)
    with lock:
        r = open_round(tier)
        if r is None:
            text = None
        else:
            if release_expired(r):
                save_state()
            mine = user_entries(r, uid)
            free = free_numbers(r)
            if len(mine) >= MAX_PER_USER:
                text = t(uid, "max_tickets")
            elif not free:
                text = t(uid, "all_taken")
            elif mine and not confirmed:
                held = " ".join(NUMBER_EMOJI[n - 1] for n in mine)
                text = t(uid, "already_hold", held=held, tier=r)
                markup = types.InlineKeyboardMarkup()
                markup.row(
                    types.InlineKeyboardButton(t(uid, "btn_yes_another"), callback_data=f"jok:{tier}"),
                    types.InlineKeyboardButton(t(uid, "btn_no"), callback_data="join"),
                )
            else:
                text = t(uid, "pick_number", id=r["id"], ends=fmt_time(r["ends"], lang), tier=r)
                markup = types.InlineKeyboardMarkup(row_width=3)
                markup.add(
                    *[
                        types.InlineKeyboardButton(NUMBER_EMOJI[n - 1], callback_data=f"pick:{r['id']}:{n}")
                        for n in free
                    ]
                )
                markup.add(types.InlineKeyboardButton(t(uid, "btn_back_lot"), callback_data="join"))
    if text is None:
        join_menu(chat_id, uid, message_id)  # this lottery is not open: show what is
        return
    edit_or_send(chat_id, message_id, text, markup)


def tier_for_round(rid):
    return tier_of(state["rounds"].get(str(rid)))


def route_join(chat_id, uid, param):
    if param in ("join_A", "join_B"):
        join_flow(chat_id, uid, param[-1])
    else:
        join_menu(chat_id, uid)


def valid_reservation(r, num, uid):
    if not r or r["status"] != "open" or time.time() >= r["ends"]:
        return False
    res = r["reserved"].get(str(num))
    return bool(res) and res["user_id"] == uid and res["expires"] > time.time()


def show_payment(chat_id, message_id, uid, rid, num):
    with lock:
        bal = balance(uid)
        r = state["rounds"].get(str(rid))
        fee = fee_of(r)
        tier = tier_of(r)
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(t(uid, "btn_pay_x"), callback_data=f"px:{rid}:{num}"))
    if bal >= fee:
        kb.add(types.InlineKeyboardButton(t(uid, "btn_pay_bal", bal=money(bal)), callback_data=f"pb:{rid}:{num}"))
    kb.add(types.InlineKeyboardButton(t(uid, "btn_cancel"), callback_data=f"cx:{rid}:{num}"))
    edit_or_send(
        chat_id, message_id, t(uid, "reserved_msg", emoji=NUMBER_EMOJI[int(num) - 1], num=num, tier=r), kb
    )


def register_referral(tg_user, raw):
    """A brand new user opened the bot with someone's link. The referrer is fixed forever."""
    if not raw.isdigit():
        return
    ref_id = int(raw)
    uid = tg_user.id
    with lock:
        if ref_id == uid or str(ref_id) not in state["users"]:
            return
        rec = user_rec(uid)
        if rec.get("ref_by"):
            return
        rec["ref_by"] = ref_id
        day_add("new_refs")
        save_state()
    safe_send(ref_id, t(ref_id, "ref_new", name=html.escape(tg_user.first_name or "User")))


def settle_referrals(r):
    """Called under the lock when a round finishes. Pays the commission and returns the DMs to send."""
    fee = fee_of(r)
    per_ref = {}
    for entry in r["entries"].values():
        ref = entry.get("ref_by")
        if not ref or str(ref) not in state["users"]:
            continue
        item = per_ref.setdefault(ref, {"tickets": 0, "amount": Decimal("0")})
        item["tickets"] += 1
        if REF_REAL_PAYMENT_ONLY and entry.get("via") != "xrocket":
            continue
        item["amount"] += ref_commission(fee, entry.get("ref_pct", "0"))
    out = {}
    for ref, item in per_ref.items():
        rec = state["users"][str(ref)]
        rec["ref_tickets"] = int(rec.get("ref_tickets", 0)) + item["tickets"]
        if item["amount"] > 0:
            add_balance(ref, item["amount"], "ref_bonus", f"round {r['id']} ref")
            rec["ref_income"] = money(Decimal(rec.get("ref_income", "0")) + item["amount"])
            stat_add("ref_paid", item["amount"])
            day_add("ref_paid", item["amount"])
            day_user("ref_earners", ref, item["amount"])
            out[ref] = (item["tickets"], item["amount"], balance(ref))
    return out


def referral_stats(uid):
    with lock:
        rec = state["users"].get(str(uid), {})
        count = sum(1 for u in state["users"].values() if u.get("ref_by") == uid)
        pending_tickets = 0
        pending_amount = Decimal("0")
        for tier in TIER_ORDER:
            r = current_round(tier)
            if not r or r["status"] not in ("open", "drawing"):
                continue
            fee = fee_of(r)
            for entry in r["entries"].values():
                if entry.get("ref_by") != uid:
                    continue
                pending_tickets += 1
                if not REF_REAL_PAYMENT_ONLY or entry.get("via") == "xrocket":
                    pending_amount += ref_commission(fee, entry.get("ref_pct", "0"))
        return {
            "n": count,
            "income": money(Decimal(rec.get("ref_income", "0"))),
            "tickets": int(rec.get("ref_tickets", 0)),
            "ptk": pending_tickets,
            "pinc": money(pending_amount),
        }


def pricing_args(uid):
    pct = ref_percent()
    a, b = TIERS["A"], TIERS["B"]
    note = t(uid, "ref_note") if REF_REAL_PAYMENT_ONLY else ""
    if pct <= 0:
        note += t(uid, "ref_off")
    return {
        "pct": fmt_pct(pct),
        "fee_a": money(a["fee"]),
        "fee_b": money(b["fee"]),
        "prizes_a": prizes_line("A"),
        "prizes_b": prizes_line("B"),
        "ca": money(ref_commission(a["fee"], pct)),
        "cb": money(ref_commission(b["fee"], pct)),
        "refnote": note,
    }


def show_referral(chat_id, uid, message_id=None):
    link = f"https://t.me/{BOT_USERNAME}?start=ref_{uid}"
    stats = referral_stats(uid)
    text = t(uid, "ref_page", link=link, **pricing_args(uid), **stats)
    kb = types.InlineKeyboardMarkup()
    share = f"https://t.me/share/url?url={quote(link, safe='')}&text={quote(t(uid, 'ref_share_text'), safe='')}"
    kb.add(types.InlineKeyboardButton(t(uid, "btn_share"), url=share))
    kb.add(types.InlineKeyboardButton(t(uid, "btn_guide"), callback_data="gd:refer"))
    kb.add(types.InlineKeyboardButton(t(uid, "btn_back"), callback_data="menu"))
    edit_or_send(chat_id, message_id, text, kb)


GUIDE_TOPICS = ["join", "draw", "prizes", "money", "refer", "faq"]


def show_guide(chat_id, uid, message_id=None, topic=None):
    kb = types.InlineKeyboardMarkup()
    if topic in GUIDE_TOPICS:
        text = t(uid, f"guide_{topic}", **pricing_args(uid))
        kb.add(types.InlineKeyboardButton(t(uid, "btn_back_guide"), callback_data="guide"))
        kb.add(types.InlineKeyboardButton(t(uid, "btn_back"), callback_data="menu"))
    else:
        text = t(uid, "guide_menu")
        buttons = [types.InlineKeyboardButton(t(uid, f"gb_{k}"), callback_data=f"gd:{k}") for k in GUIDE_TOPICS]
        for i in range(0, len(buttons), 2):
            kb.row(*buttons[i : i + 2])
        kb.add(types.InlineKeyboardButton(t(uid, "btn_back"), callback_data="menu"))
    edit_or_send(chat_id, message_id, text, kb)


@bot.callback_query_handler(func=lambda c: c.data == "ref")
def on_ref(call):
    ack(call)
    ensure_user(call.from_user)
    show_referral(call.message.chat.id, call.from_user.id, call.message.message_id)


@bot.callback_query_handler(func=lambda c: c.data == "guide" or c.data.startswith("gd:"))
def on_guide(call):
    ack(call)
    ensure_user(call.from_user)
    topic = call.data.split(":", 1)[1] if call.data.startswith("gd:") else None
    show_guide(call.message.chat.id, call.from_user.id, call.message.message_id, topic)


@bot.message_handler(commands=["refpct"])
def on_refpct(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split()
    if len(parts) < 2:
        safe_send(
            message.chat.id,
            f"👥 Referral commission: <b>{fmt_pct(ref_percent())}%</b> (max {fmt_pct(REF_MAX_PERCENT)}%)\n"
            "Change it with: /refpct 2.5\nNew value applies to tickets bought from now on.",
        )
        return
    try:
        value = Decimal(parts[1].replace(",", "."))
    except InvalidOperation:
        safe_send(message.chat.id, "Usage: /refpct 2.5")
        return
    if not value.is_finite() or value < 0 or value > REF_MAX_PERCENT:
        safe_send(message.chat.id, f"Value must be between 0 and {fmt_pct(REF_MAX_PERCENT)}.")
        return
    new = set_ref_percent(value)
    safe_send(
        message.chat.id,
        f"✅ Referral commission is now <b>{fmt_pct(new)}%</b>.\n"
        "It applies to tickets bought from now on; tickets already bought keep the rate they were bought with.",
    )


@bot.message_handler(commands=["start", "menu"])
def on_start(message):
    if message.chat.type != "private":
        return
    uid = message.from_user.id
    parts = (message.text or "").split(maxsplit=1)
    param = parts[1].strip() if len(parts) > 1 else ""
    with lock:
        is_new = str(uid) not in state["users"]
    ensure_user(message.from_user)
    if is_new and param.startswith("ref_"):
        register_referral(message.from_user, param[4:])
    with lock:
        has_lang = user_rec(uid).get("lang")
    if not has_lang:
        if param.startswith("join"):
            pending_join[uid] = param
        safe_send(message.chat.id, TEXT["en"]["lang_prompt"], lang_markup())
        return
    if param.startswith("join"):
        route_join(message.chat.id, uid, param)
    else:
        show_menu(message.chat.id, uid)


@bot.callback_query_handler(func=lambda c: c.data == "lang")
def on_lang_open(call):
    ack(call)
    edit_or_send(call.message.chat.id, call.message.message_id, TEXT["en"]["lang_prompt"], lang_markup())


@bot.callback_query_handler(func=lambda c: c.data.startswith("lg:"))
def on_lang_set(call):
    code = call.data.split(":", 1)[1]
    if code not in TEXT:
        ack(call)
        return
    uid = call.from_user.id
    ensure_user(call.from_user)
    with lock:
        user_rec(uid)["lang"] = code
        save_state()
    ack(call)
    edit_or_send(call.message.chat.id, call.message.message_id, t(uid, "lang_set"))
    param = pending_join.pop(uid, None)
    if param:
        route_join(call.message.chat.id, uid, param)
    else:
        show_menu(call.message.chat.id, uid)


@bot.callback_query_handler(func=lambda c: c.data == "menu")
def on_menu(call):
    ack(call)
    ensure_user(call.from_user)
    show_menu(call.message.chat.id, call.from_user.id, call.message.message_id)


@bot.callback_query_handler(func=lambda c: c.data in ("join", "join_ok"))
def on_join(call):
    ack(call)
    ensure_user(call.from_user)
    join_menu(call.message.chat.id, call.from_user.id, call.message.message_id)


@bot.callback_query_handler(func=lambda c: c.data.startswith("jt:") or c.data.startswith("jok:"))
def on_join_tier(call):
    ack(call)
    ensure_user(call.from_user)
    kind, tier = call.data.split(":", 1)
    if tier not in TIERS:
        join_menu(call.message.chat.id, call.from_user.id, call.message.message_id)
        return
    join_flow(call.message.chat.id, call.from_user.id, tier, call.message.message_id, kind == "jok")


@bot.callback_query_handler(func=lambda c: c.data == "mine" or c.data.startswith("hist:"))
def on_history(call):
    ack(call)
    ensure_user(call.from_user)
    uid = call.from_user.id
    page = 0
    if call.data.startswith("hist:"):
        try:
            page = int(call.data.split(":", 1)[1])
        except ValueError:
            page = 0
    text, kb = history_view(uid, page)
    edit_or_send(call.message.chat.id, call.message.message_id, text, kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith("pick:") or c.data.startswith("pw:"))
def on_pick(call):
    kind, rid, num = call.data.split(":")
    uid = call.from_user.id
    ensure_user(call.from_user)
    if join_block_left(uid) > 0:
        ack(call)
        show_join_block(call.message.chat.id, uid, call.message.message_id)
        return
    if kind == "pick":
        with lock:
            strikes = int(user_rec(uid).get("strikes", 0))
        if strikes >= STRIKE_LIMIT - 1:
            # one more unpaid reservation would block this user: warn first, nothing is reserved yet
            ack(call)
            kb = types.InlineKeyboardMarkup()
            kb.row(
                types.InlineKeyboardButton(t(uid, "btn_continue"), callback_data=f"pw:{rid}:{num}"),
                types.InlineKeyboardButton(t(uid, "btn_cancel"), callback_data="join"),
            )
            edit_or_send(
                call.message.chat.id,
                call.message.message_id,
                t(uid, "strike_warn", n=strikes, hours=JOIN_BLOCK_HOURS),
                kb,
            )
            return
    problem = None
    with lock:
        r = state["rounds"].get(rid)
        tier = tier_of(r)
        if not r or r["status"] != "open" or time.time() >= r["ends"]:
            problem = "alert_closed"
        else:
            release_expired(r)
            res = r["reserved"].get(num)
            if num in r["entries"] or (res and res["user_id"] != uid):
                problem = "alert_taken"
            elif len(user_entries(r, uid)) >= MAX_PER_USER:
                problem = "alert_max"
            else:
                for key, val in list(r["reserved"].items()):
                    if val["user_id"] == uid:
                        del r["reserved"][key]
                r["reserved"][num] = {"user_id": uid, "expires": time.time() + RESERVE_SECONDS}
                save_state()
    if problem:
        ack(call, t(uid, problem), True)
        join_flow(call.message.chat.id, uid, tier, call.message.message_id, True)
        return
    ack(call)
    refresh_post(r)
    show_payment(call.message.chat.id, call.message.message_id, uid, rid, num)


@bot.callback_query_handler(func=lambda c: c.data.startswith("cx:"))
def on_cancel_reserve(call):
    _, rid, num = call.data.split(":")
    uid = call.from_user.id
    with lock:
        r = state["rounds"].get(rid)
        if r and r["reserved"].get(num, {}).get("user_id") == uid:
            del r["reserved"][num]
            save_state()
        for inv in state["invoices"].values():
            if inv["user_id"] == uid and inv["round_id"] == int(rid) and inv["number"] == int(num):
                inv["cancelled"] = True  # cancelled by the user: no strike when it expires
    ack(call, t(uid, "alert_cancelled"))
    if r:
        refresh_post(r)
    show_menu(call.message.chat.id, uid, call.message.message_id)


@bot.callback_query_handler(func=lambda c: c.data.startswith("px:"))
def on_pay_xrocket(call):
    _, rid, num = call.data.split(":")
    uid = call.from_user.id
    with lock:
        r = state["rounds"].get(rid)
        valid = valid_reservation(r, num, uid)
        tier = tier_of(r)
        fee = fee_of(r)
    if not valid:
        ack(call, t(uid, "alert_reserve_expired"), True)
        join_flow(call.message.chat.id, uid, tier, call.message.message_id, True)
        return
    ack(call, t(uid, "alert_creating"))
    invoice = create_invoice(uid, rid, num, fee)
    link = invoice_link(invoice) if invoice else None
    if not invoice or not link:
        print("invoice response:", invoice)
        safe_send(call.message.chat.id, t(uid, "invoice_fail"), back_markup(uid))
        return
    invoice_id = str(invoice["id"])
    with lock:
        state["invoices"][invoice_id] = {
            "user_id": uid,
            "round_id": int(rid),
            "number": int(num),
            "fee": money(fee),
            "created": time.time(),
        }
        save_state()
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(t(uid, "btn_pay_on"), url=link))
    kb.add(types.InlineKeyboardButton(t(uid, "btn_check"), callback_data=f"chk:{invoice_id}"))
    kb.add(types.InlineKeyboardButton(t(uid, "btn_cancel"), callback_data=f"cx:{rid}:{num}"))
    edit_or_send(
        call.message.chat.id,
        call.message.message_id,
        t(uid, "invoice_ready", emoji=NUMBER_EMOJI[int(num) - 1], num=num, tier=r),
        kb,
    )


@bot.callback_query_handler(func=lambda c: c.data.startswith("pb:"))
def on_pay_balance(call):
    _, rid, num = call.data.split(":")
    uid = call.from_user.id
    ensure_user(call.from_user)
    problem = None
    with lock:
        r = state["rounds"].get(rid)
        tier = tier_of(r)
        fee = fee_of(r)
        if not valid_reservation(r, num, uid):
            problem = "alert_reserve_expired"
        elif balance(uid) < fee:
            problem = "alert_no_balance"
        else:
            add_balance(uid, -fee, "ticket", f"round {rid} ticket {num}")
            confirm_entry_locked(r, int(num), uid)
    if problem:
        ack(call, t(uid, problem), True)
        join_flow(call.message.chat.id, uid, tier, call.message.message_id, True)
        return
    ack(call, t(uid, "alert_paid_bal"))
    clear_markup(call)
    after_entry(rid, num, uid)


@bot.callback_query_handler(func=lambda c: c.data.startswith("chk:"))
def on_check(call):
    uid = call.from_user.id
    invoice_id = call.data.split(":", 1)[1]
    with lock:
        pending = invoice_id in state["invoices"]
    if not pending:
        ack(call, t(uid, "alert_processed"), True)
        return
    data = get_invoice(invoice_id)
    if data and data.get("status") == "paid":
        ack(call)
        handle_paid(invoice_id)
    else:
        ack(call, t(uid, "alert_not_received"), True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("nm:"))
def on_name(call):
    _, rid, num, mode = call.data.split(":")
    uid = call.from_user.id
    ensure_user(call.from_user)
    problem = None
    shown = ""
    with lock:
        r = state["rounds"].get(rid)
        entry = r["entries"].get(num) if r else None
        if not entry or entry["user_id"] != uid:
            problem = "alert_ticket_missing"
        elif r["status"] not in ("open", "drawing") or r.get("started"):
            problem = "alert_round_done"
        elif mode == "u" and not call.from_user.username:
            problem = "alert_no_username"
        else:
            entry["mode"] = "username" if mode == "u" else "uid"
            entry["username"] = call.from_user.username or ""
            save_state()
            shown = display(entry)
    if problem:
        ack(call, t(uid, problem), True)
        return
    ack(call, t(uid, "alert_saved"))
    edit_or_send(
        call.message.chat.id,
        call.message.message_id,
        t(uid, "name_done", emoji=NUMBER_EMOJI[int(num) - 1], num=num, shown=shown),
        menu_markup(uid),
    )
    refresh_post(r)


@bot.callback_query_handler(func=lambda c: c.data == "wd")
def on_withdraw(call):
    uid = call.from_user.id
    ensure_user(call.from_user)
    if not state.get("wd_enabled", True):
        ack(call, t(uid, "wd_off_alert"), True)
        return
    with lock:
        bal = balance(uid)
    if bal < MIN_WITHDRAW:
        ack(call, t(uid, "alert_wd_min"), True)
        return
    ack(call)
    ask_amount(call.message.chat.id, uid)


def ask_amount(chat_id, uid):
    msg = bot.send_message(chat_id, t(uid, "wd_ask"))
    bot.register_next_step_handler(msg, receive_amount)


def receive_amount(message):
    uid = message.from_user.id
    if is_banned(uid):
        safe_send(message.chat.id, t(uid, "banned"))
        return
    text = (message.text or "").strip()
    if text.startswith("/"):
        show_menu(message.chat.id, uid)
        return
    try:
        amount = Decimal(text.replace(",", "."))
    except InvalidOperation:
        bot.send_message(message.chat.id, t(uid, "wd_bad_number"))
        ask_amount(message.chat.id, uid)
        return
    if not amount.is_finite() or amount.as_tuple().exponent < -3:
        bot.send_message(message.chat.id, t(uid, "wd_bad_dec"))
        ask_amount(message.chat.id, uid)
        return
    with lock:
        bal = balance(uid)
    if amount < MIN_WITHDRAW:
        bot.send_message(message.chat.id, t(uid, "wd_min"))
        ask_amount(message.chat.id, uid)
        return
    if amount > bal:
        bot.send_message(message.chat.id, t(uid, "wd_nobal", bal=money(bal)))
        ask_amount(message.chat.id, uid)
        return
    if not state.get("wd_enabled", True):
        safe_send(message.chat.id, t(uid, "wd_off"))
        return
    diff, total, bal_now, rows = audit_user(uid)
    if diff > AUDIT_TOLERANCE:  # more money than the history explains: the admin must look at it first
        request_review(message.chat.id, uid, amount, diff, total, bal_now, rows)
        return
    drafts[uid] = amount
    kb = types.InlineKeyboardMarkup()
    kb.row(
        types.InlineKeyboardButton(t(uid, "btn_confirm"), callback_data="wd_confirm"),
        types.InlineKeyboardButton(t(uid, "btn_cancel"), callback_data="wd_cancel"),
    )
    safe_send(message.chat.id, t(uid, "wd_confirm", amount=money(amount)), kb)


@bot.callback_query_handler(func=lambda c: c.data == "wd_cancel")
def on_wd_cancel(call):
    uid = call.from_user.id
    drafts.pop(uid, None)
    ack(call, t(uid, "alert_cancelled"))
    clear_markup(call)
    show_menu(call.message.chat.id, uid)


def audit_user(uid):
    """Balance the ledger explains vs. the stored balance. Do not call while holding `lock`."""
    rows = ledger_rows(uid)
    total = Decimal("0")
    for row in rows:
        try:
            total += Decimal(row[3])
        except InvalidOperation:
            pass
    with lock:
        bal = balance(uid)
        offset = Decimal(str(state["users"].get(str(uid), {}).get("audit_offset", "0")))
    return bal - total - offset, total, bal, rows


def request_review(chat_id, uid, amount, diff, total, bal, rows):
    with lock:
        exists = any(a["user_id"] == uid for a in state["approvals"].values())
        if not exists:
            state["approval_counter"] = int(state.get("approval_counter", 0)) + 1
            aid = str(state["approval_counter"])
            state["approvals"][aid] = {
                "user_id": uid,
                "amount": money(amount),
                "created": time.time(),
                "diff": money(diff),
            }
            day_add("wd_review")
            save_state()
        rec = state["users"].get(str(uid), {})
        name = html.escape(rec.get("name", "") or "-")
        username = rec.get("username", "")
    if exists:
        safe_send(chat_id, t(uid, "wd_review_exists"), menu_markup(uid))
        return
    safe_send(chat_id, t(uid, "wd_review"), menu_markup(uid))
    last = html.escape("\n".join(f"{r[0][5:16]} {r[2]} {r[3]}" for r in rows[-8:])) or "-"
    kb = types.InlineKeyboardMarkup()
    kb.row(
        types.InlineKeyboardButton("✅ Approve", callback_data=f"wa:ok:{aid}"),
        types.InlineKeyboardButton("❌ Reject", callback_data=f"wa:no:{aid}"),
    )
    safe_send(
        ADMIN_ID,
        "⚠️ <b>Suspicious withdrawal — review needed</b>\n"
        f"{SEP}\n"
        f"👤 {name}  {('@' + html.escape(username)) if username else ''}\n"
        f"🆔 <code>{uid}</code>\n"
        f"💰 Requested: <b>{money(amount)} USDT</b>\n"
        f"💳 Bot balance: {money(bal)} USDT\n"
        f"🧾 Balance explained by history: {money(total)} USDT\n"
        f"❗ Unexplained extra balance: <b>{money(diff)} USDT</b>\n"
        f"{SEP}\n"
        f"Last transactions:\n<pre>{last}</pre>",
        kb,
    )


@bot.callback_query_handler(func=lambda c: c.data.startswith("wa:"))
def on_withdraw_review(call):
    if not is_admin(call.from_user.id):
        ack(call)
        return
    _, action, aid = call.data.split(":")
    with lock:
        a = state["approvals"].get(aid)
    if not a:
        ack(call, "Already handled.", True)
        return
    uid = a["user_id"]
    amount = Decimal(a["amount"])
    shown = getattr(call.message, "html_text", None) or call.message.text or ""
    if action == "no":
        with lock:
            state["approvals"].pop(aid, None)
            save_state()
        ack(call, "Rejected")
        edit_or_send(call.message.chat.id, call.message.message_id, shown + "\n\n❌ <b>Rejected</b>")
        safe_send(uid, t(uid, "wd_rejected"), menu_markup(uid))
        return
    _, total, bal, _rows = audit_user(uid)
    with lock:
        if balance(uid) < amount:
            low = True
        else:
            low = False
            state["approvals"].pop(aid, None)
            # the admin accepted this balance, so future audits start from here
            state["users"][str(uid)]["audit_offset"] = str(balance(uid) - total)
            save_state()
    if low:
        ack(call, "The user's balance is now lower than the requested amount. Reject it instead.", True)
        return
    ack(call, "Approved")
    edit_or_send(call.message.chat.id, call.message.message_id, shown + "\n\n✅ <b>Approved</b>")
    safe_send(uid, t(uid, "wd_approved"))
    start_withdrawal(uid, amount, uid)


def start_withdrawal(uid, amount, chat_id):
    client_id = f"wd-{uid}-{int(time.time() * 1000)}"
    with lock:
        if amount > balance(uid):
            return "no_balance"
        add_balance(uid, -amount, "withdraw", client_id)
        state["payouts"][client_id] = {"user_id": uid, "amount": money(amount), "created": time.time()}
        save_state()
    try:
        flush_state(raise_on_error=True)  # the deduction must be safely stored before any money leaves
    except Exception as e:
        print("withdraw: storage error:", e)
        with lock:
            state["payouts"].pop(client_id, None)
            add_balance(uid, amount, "withdraw_refund", client_id)
            save_state()
            left = balance(uid)
        safe_send(
            chat_id,
            t(uid, "wd_failed_api", reason="temporary storage problem, please try again", bal=money(left)),
            menu_markup(uid),
        )
        return "storage_error"
    day_user("wd_req", uid, amount)
    safe_send(chat_id, t(uid, "wd_processing"))
    notify_admin_withdraw("💸 <b>New withdrawal request</b>", uid, amount, client_id, "Status: sending to xRocket...")
    kind, data = api_create_payout(uid, amount, client_id)
    if kind == "error":
        with lock:
            state["payouts"].pop(client_id, None)
            add_balance(uid, amount, "withdraw_refund", client_id)
            save_state()
            left = balance(uid)
        safe_send(
            chat_id,
            t(uid, "wd_failed_api", reason=html.escape(str(data)), bal=money(left)),
            menu_markup(uid),
        )
        notify_admin_withdraw(
            "❌ <b>Withdrawal REJECTED by xRocket</b>",
            uid,
            amount,
            client_id,
            f"Reason: {html.escape(str(data))}\nAmount returned to the user's bot balance.",
        )
        return "rejected"
    if kind == "ok" and isinstance(data, dict):
        payout_id = data.get("payoutId") or data.get("id")
        with lock:
            if client_id in state["payouts"] and payout_id:
                state["payouts"][client_id]["payout_id"] = str(payout_id)
                save_state()
        if data.get("status") in ("finished", "failed"):
            resolve_payout(client_id, data.get("status"))
            return "ok"
    safe_send(chat_id, t(uid, "wd_pending"))
    return "ok"


@bot.callback_query_handler(func=lambda c: c.data == "wd_confirm")
def on_wd_confirm(call):
    uid = call.from_user.id
    amount = drafts.pop(uid, None)
    clear_markup(call)
    if amount is None:
        ack(call, t(uid, "alert_session"), True)
        return
    if not state.get("wd_enabled", True):
        ack(call, t(uid, "wd_off_alert"), True)
        return
    ack(call)
    if start_withdrawal(uid, amount, call.message.chat.id) == "no_balance":
        safe_send(call.message.chat.id, t(uid, "alert_no_balance"))


class HealthHandler(BaseHTTPRequestHandler):
    def _ok(self, body=True):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()
        if body:
            self.wfile.write(b"ok")

    def do_GET(self):
        self._ok()

    def do_HEAD(self):
        self._ok(False)

    def log_message(self, *args):
        pass


def start_health_server():
    """Render web services must listen on $PORT; UptimeRobot / the self-ping use this to keep the bot awake."""
    port = int(os.environ.get("PORT", "10000"))
    server = HTTPServer(("0.0.0.0", port), HealthHandler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    print("Health server on port", port)


def self_ping():
    url = os.environ.get("RENDER_EXTERNAL_URL", "").strip()
    if not url:
        return
    while True:
        time.sleep(9 * 60)
        try:
            requests.get(url, timeout=20)
        except requests.RequestException as e:
            print("self ping failed:", e)


def acquire_lease():
    deadline = time.time() + 150
    while True:
        try:
            if store.try_lock(INSTANCE_ID, LEASE_SECONDS):
                print("Instance lock acquired.")
                return
        except Exception as e:
            print("lock error:", e)
        if time.time() > deadline:
            print("Another instance still holds the lock. Exiting.")
            raise SystemExit(1)
        print("Waiting for the previous instance to stop...")
        time.sleep(3)


def lease_heartbeat():
    while True:
        time.sleep(10)
        try:
            if not store.refresh_lock(INSTANCE_ID, LEASE_SECONDS):
                print("Lost the instance lock - stopping to protect the data.")
                os._exit(1)
        except Exception as e:
            print("heartbeat error:", e)


def shutdown_handler(signum, frame):
    print("Shutting down: saving data...")
    try:
        flush_state()
    except Exception as e:
        print("final save failed:", e)
    try:
        store.release_lock(INSTANCE_ID)
    except Exception as e:
        print("lock release failed:", e)
    os._exit(0)


if __name__ == "__main__":
    start_health_server()
    store = make_store()
    acquire_lease()
    init_state()
    signal.signal(signal.SIGTERM, shutdown_handler)
    signal.signal(signal.SIGINT, shutdown_handler)
    try:
        BOT_USERNAME = bot.get_me().username
    except Exception as e:
        print("Invalid bot token:", e)
        raise SystemExit(1)
    check_key()
    for worker in (state_writer, lease_heartbeat, poller, maintenance, draw_worker, admin_loop, self_ping):
        threading.Thread(target=worker, daemon=True).start()
    print(f"Bot @{BOT_USERNAME} started. Channel: {CHANNEL}")
    bot.infinity_polling(skip_pending=True)
