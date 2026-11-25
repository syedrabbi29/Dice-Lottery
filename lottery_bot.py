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
from datetime import datetime, timedelta, timezone
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
        "name": {"en": "Classic", "bn": "ক্লাসিক"},
        "fee": Decimal("0.05"),
        "prizes": [Decimal("0.150"), Decimal("0.080"), Decimal("0.055")],
        "house": Decimal("0.015"),
        "reminder": 10 * 60,
    },
    "B": {
        "emoji": "💎",
        "name": {"en": "Premium", "bn": "প্রিমিয়াম"},
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
        "lang_prompt": "🌐 Choose your language / ভাষা বাছাই করুন",
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
        "lang_prompt": "🌐 Choose your language / ভাষা বাছাই করুন",
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


def tier_label(tier, lang="en"):
    c = cfg(tier)
    return f"{c['emoji']} {c['name'][lang]}"


def prizes_line(tier):
    return " • ".join(f"{MEDALS[i]} {money(p)}" for i, p in enumerate(cfg(tier)["prizes"]))


def new_user():
    return {"balance": "0.00", "name": "", "username": "", "lang": None}


def user_rec(uid):
    rec = state["users"].setdefault(str(uid), new_user())
    rec.setdefault("lang", None)
    return rec


def lang_of(uid):
    return state["users"].get(str(uid), {}).get("lang") or "en"


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
    template = TEXT[lang][key]
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


def ensure_user(tg_user):
    with lock:
        is_new = str(tg_user.id) not in state["users"]
        rec = user_rec(tg_user.id)
        name = tg_user.first_name or ""
        username = tg_user.username or ""
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
    if lang == "bn":
        return datetime.fromtimestamp(ts, BDT).strftime("%d %b %Y, %I:%M %p") + " (BDT)"
    return datetime.fromtimestamp(ts, UTC).strftime("%d %b %Y, %I:%M %p") + " (UTC)"


def short_time(text, lang="en"):
    try:
        dt = datetime.strptime(text, "%Y-%m-%d %H:%M:%S").replace(tzinfo=UTC)
    except ValueError:
        return text
    if lang == "bn":
        return dt.astimezone(BDT).strftime("%d %b, %I:%M %p") + " (BDT)"
    return dt.strftime("%d %b, %I:%M %p") + " (UTC)"


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
    try:
        msg = bot.send_message(CHANNEL, text, parse_mode="HTML", reply_markup=markup)
    except Exception as e:
        print("Could not post to the channel (is the bot an admin?):", e)
        return
    with lock:
        r["message_id"] = msg.message_id
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
        stat_add("prizes", sum((Decimal(w["prize"]) for w in r["winners"]), Decimal("0")))
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
        else:
            stat_add("withdrawn", amount)
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
    with lock:
        rec = state["users"].get(str(uid))
        if not rec:
            return False
        rec["banned"] = flag
        save_state()
    return True


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
    if not set_ban(uid, action == "ban"):
        ack(call, "User not found.", True)
        return
    ack(call, "🚫 Banned" if action == "ban" else "✅ Unbanned")
    details = user_details(uid)
    if details:
        edit_or_send(call.message.chat.id, call.message.message_id, details[0], details[1])


@bot.message_handler(commands=["block", "unblock"])
def on_block_command(message):
    if message.chat.type != "private" or not is_admin(message.from_user.id):
        return
    parts = (message.text or "").split()
    if len(parts) < 2 or not parts[1].isdigit():
        safe_send(message.chat.id, "Usage: /block 123456789  or  /unblock 123456789")
        return
    block = parts[0].startswith("/block")
    if set_ban(int(parts[1]), block):
        safe_send(message.chat.id, "🚫 User banned." if block else "✅ User unbanned.")
    else:
        safe_send(message.chat.id, "User not found.")


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


def lang_markup():
    kb = types.InlineKeyboardMarkup()
    kb.row(
        types.InlineKeyboardButton("English 🇬🇧", callback_data="lg:en"),
        types.InlineKeyboardButton("বাংলা 🇧🇩", callback_data="lg:bn"),
    )
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
                        f"{c['emoji']} {c['name'][lang]} • {money(c['fee'])} USDT", callback_data=f"jt:{tier}"
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
    if code not in ("en", "bn"):
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


@bot.callback_query_handler(func=lambda c: c.data.startswith("pick:"))
def on_pick(call):
    _, rid, num = call.data.split(":")
    uid = call.from_user.id
    ensure_user(call.from_user)
    if join_block_left(uid) > 0:
        ack(call)
        show_join_block(call.message.chat.id, uid, call.message.message_id)
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
