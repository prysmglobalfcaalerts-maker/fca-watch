"""
FCA and PRA regulatory change watcher.

Once a day this script:
  1. Collects new items from public feeds (FCA news, Bank of England / PRA
     publications, HM Treasury, new UK statutory instruments) and the FCA
     email alerts that arrive in the bot's own inbox.
  2. Asks Claude whether each item changes the scope of FCA or PRA
     regulation, or materially changes how a sector is regulated (including
     the capital and other prudential requirements on banks and insurers).
  3. Emails you a digest of the items that matter, or, if none qualify,
     a short "no changes today" email (see SEND_NO_CHANGE_EMAIL).

It remembers what it has already checked in seen.json, so you are never
alerted twice about the same thing.

Settings come from environment variables (GitHub Actions secrets):
  ANTHROPIC_API_KEY   - your Anthropic API key (required)
  BOT_EMAIL           - the Gmail address the bot uses (required)
  BOT_EMAIL_PASSWORD  - a Gmail *app password* for that address (required)
  NOTIFY_TO           - where alerts are sent (defaults to BOT_EMAIL)
  ALERTS_FROM         - text that appears in the FCA alert sender address
                        (defaults to "fca", which matches both
                        fca.org.uk and the GovDelivery sender UKFCA@...)
  MODEL               - Claude model to use (defaults to claude-haiku-5-5)
  TEST_MODE           - "true" to check the newest items, email the result
                        and change nothing (for trying it out)
  DRY_RUN             - "true" to print the email instead of sending it
"""

import email
import imaplib
import json
import os
import re
import smtplib
import time
from datetime import datetime, timedelta, timezone
from email.header import decode_header, make_header
from email.message import EmailMessage
from html import unescape
from pathlib import Path

import anthropic
import feedparser

# --------------------------------------------------------------------------
# Settings
# --------------------------------------------------------------------------

SEEN_FILE = Path(__file__).with_name("seen.json")
MAX_SEEN = 5000  # oldest entries are dropped beyond this
MODEL = os.environ.get("MODEL") or "claude-haiku-5-5"
TEST_MODE = os.environ.get("TEST_MODE", "").lower() in ("1", "true", "yes")
DRY_RUN = os.environ.get("DRY_RUN", "").lower() in ("1", "true", "yes")

# Send a short "no changes today" email on days when nothing qualifies.
# Set to False to only hear from the bot when something is flagged.
SEND_NO_CHANGE_EMAIL = True

# Public feeds to watch. "keywords" (optional) pre-filters busy feeds so only
# plausibly relevant items are sent to Claude, which keeps costs tiny.
FEEDS = [
    {
        "name": "FCA news",
        "url": "https://www.fca.org.uk/news/rss.xml",
    },
    {
        # Everything the PRA publishes: consultation papers, policy
        # statements, supervisory statements, statements of policy.
        "name": "PRA publications",
        "url": "https://www.bankofengland.co.uk/rss/prudential-regulation-publications",
    },
    {
        # Bank of England news. Filtered so interest-rate and monetary policy
        # news is never sent to Claude; only prudential/regulatory items are.
        "name": "Bank of England news",
        "url": "https://www.bankofengland.co.uk/rss/news",
        "keywords": [
            "prudential", "pra ", "capital", "liquidity", "solvency",
            "leverage", "basel", "buffer", "resolution", "ring-fenc",
            "insurer", "insurance", "regulat", "financial policy committee",
        ],
    },
    {
        "name": "HM Treasury publications",
        "url": "https://www.gov.uk/search/all.atom?organisations%5B%5D=hm-treasury",
    },
    {
        "name": "New UK statutory instruments",
        "url": "https://www.legislation.gov.uk/new/uksi/data.feed",
        "keywords": [
            "financial services", "financial conduct", "regulated activities",
            "consumer credit", "payment", "electronic money", "cryptoasset",
            "funeral", "insurance", "pension", "markets",
        ],
    },
]

# What counts as relevant. Edit this text to tune what you get alerted about.
SYSTEM_PROMPT = """You screen UK financial-services publications for one reader.
The reader wants to know whenever the scope of regulation by the FCA or the
Prudential Regulation Authority (PRA, part of the Bank of England) changes,
or the way a sector is regulated changes materially.

FLAG an item if it does any of these (including proposals, consultations,
draft legislation, final rules, or commencement dates):
- Brings a new activity, product, business type or industry into FCA or PRA
  regulation (e.g. changes to the Regulated Activities Order, new regimes like
  those for funeral plans, buy-now-pay-later or cryptoassets, or a new
  prudential regime for a type of firm).
- Takes an activity or industry out of FCA or PRA regulation.
- Materially changes how an already-regulated sector is regulated: a new or
  overhauled rulebook, a new authorisation or registration regime, new
  conduct standards for a whole sector, or moving supervision between
  regulators.
- Materially changes the prudential rules for banks, building societies or
  insurers: how much capital or liquidity they must hold, leverage, capital
  buffers (including decisions by the Financial Policy Committee),
  Basel 3.1, Solvency UK, ring-fencing, recovery and resolution, or which
  firms the rules apply to (e.g. thresholds, the small domestic deposit
  takers regime).
- Changes the FCA's or PRA's own powers, remit, objectives or structure.

DO NOT flag: interest rates, Bank Rate, Monetary Policy Committee decisions,
inflation, banknotes, markets operations or other monetary policy; enforcement
action, fines, warnings about unauthorised firms or scams; speeches with no
new proposal; fees and levies; statistics and data releases; regulatory
digests and newsletters that only summarise earlier publications;
appointments; routine or minor technical amendments (e.g. FCA quarterly
consultations, PRA Low Impact Amendments); or tax and spending matters that
do not affect financial regulation.

An item may be a single publication or an email digest listing several
publications. Flag each relevant publication separately.

Reply with ONLY a JSON object, no other text:
{"matches": [{"headline": "...", "title": "...", "doc_type": "...", "type": "...", "stage": "...", "why": "...", "link": "..."}]}
- headline: your own plain-English heading (max 12 words) saying what is
  changing and for whom, e.g. "FCA to update rules on simplified investment
  advice". It must make sense to someone who has not seen the publication.
- title: the publication's original title, copied exactly.
- doc_type: what kind of publication it is and, if given, who it is from,
  e.g. "Speech by the FCA deputy chief executive", "FCA consultation paper",
  "PRA policy statement", "PRA supervisory statement", "Bank of England
  Financial Policy Committee record", "HM Treasury consultation",
  "Statutory instrument".
- type: either "New to regulation" or "Change to an existing regime".
  Use "New to regulation" ONLY if the publication itself says the activity,
  product, industry or type of firm is not currently regulated by the FCA or
  PRA (or is being taken out of regulation). If it amends, overhauls or refers to rules
  that already apply, or if you are unsure, use "Change to an existing regime".
- stage: one of "Early idea / discussion", "Consultation", "Final rules",
  "Legislation", "Coming into force"
- why: one plain-English sentence saying what is changing and for whom
- link: the URL if one is given, otherwise ""
If nothing qualifies, reply {"matches": []}"""


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

def clean(text, limit):
    """Strip HTML and squash whitespace."""
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = unescape(re.sub(r"\s+", " ", text)).strip()
    return text[:limit]


def load_seen():
    if SEEN_FILE.exists():
        return json.loads(SEEN_FILE.read_text())
    return {}


def save_seen(seen):
    # Keep only the most recent MAX_SEEN entries.
    newest = sorted(seen.items(), key=lambda kv: kv[1])[-MAX_SEEN:]
    SEEN_FILE.write_text(json.dumps(dict(newest), indent=0))


# --------------------------------------------------------------------------
# Collecting items
# --------------------------------------------------------------------------

def fetch_feed_items(feed):
    parsed = feedparser.parse(
        feed["url"], agent="fca-watch/1.0 (personal regulatory monitoring)"
    )
    if not parsed.entries:
        print(f"WARNING: no items read from {feed['name']} ({feed['url']}). "
              f"Reason: {parsed.get('bozo_exception', 'feed was empty')}")
        return []

    items = []
    for entry in parsed.entries:
        title = clean(entry.get("title", ""), 300)
        summary = clean(entry.get("summary", ""), 2000)
        if feed.get("keywords"):
            haystack = f"{title} {summary}".lower()
            if not any(k in haystack for k in feed["keywords"]):
                continue
        uid = entry.get("id") or entry.get("link") or title
        items.append({
            "id": f"{feed['name']}|{uid}",
            "source": feed["name"],
            "title": title,
            "link": entry.get("link", ""),
            "text": summary,
        })
    print(f"{feed['name']}: {len(items)} items")
    return items


def email_body_text(msg, limit):
    plain, html = "", ""
    for part in msg.walk():
        ctype = part.get_content_type()
        if part.get_content_maintype() == "multipart":
            continue
        payload = part.get_payload(decode=True)
        if not payload:
            continue
        text = payload.decode(part.get_content_charset() or "utf-8", "replace")
        if ctype == "text/plain" and not plain:
            plain = text
        elif ctype == "text/html" and not html:
            html = text
    if plain:
        return re.sub(r"\s+", " ", plain).strip()[:limit]
    return clean(html, limit)


def fetch_email_items():
    """Read FCA email alerts from the bot's Gmail inbox (last 3 days)."""
    user = os.environ.get("BOT_EMAIL")
    password = os.environ.get("BOT_EMAIL_PASSWORD")
    sender_filter = os.environ.get("ALERTS_FROM") or "fca"
    if not user or not password:
        print("No bot inbox configured; skipping FCA email alerts.")
        return []

    since = (datetime.now(timezone.utc) - timedelta(days=3)).strftime("%d-%b-%Y")
    items = []
    try:
        imap = imaplib.IMAP4_SSL(os.environ.get("IMAP_HOST", "imap.gmail.com"))
        imap.login(user, password)
        imap.select("INBOX", readonly=True)
        _, data = imap.search(None, f'(SINCE {since} FROM "{sender_filter}")')
        for num in data[0].split():
            _, msg_data = imap.fetch(num, "(RFC822)")
            msg = email.message_from_bytes(msg_data[0][1])
            subject = str(make_header(decode_header(msg.get("Subject", ""))))
            uid = msg.get("Message-ID") or f"{subject}|{msg.get('Date')}"
            items.append({
                "id": f"email|{uid}",
                "source": "FCA email alert",
                "title": subject,
                "link": "",
                "text": email_body_text(msg, 15000),
            })
        imap.logout()
    except Exception as exc:  # keep going even if the inbox fails
        print(f"WARNING: could not read the bot inbox: {exc}")
    print(f"FCA email alerts: {len(items)} items")
    return items


# --------------------------------------------------------------------------
# Asking Claude
# --------------------------------------------------------------------------

def parse_matches(raw):
    start, end = raw.find("{"), raw.rfind("}")
    if start == -1 or end == -1:
        return None
    try:
        return json.loads(raw[start:end + 1]).get("matches", [])
    except json.JSONDecodeError:
        return None


def classify(client, item):
    """Return a list of matches, or None if Claude couldn't be reached."""
    user_msg = (
        f"Source: {item['source']}\nTitle: {item['title']}\n"
        f"Link: {item['link'] or 'n/a'}\n\nContent:\n{item['text']}"
    )
    for attempt in range(3):
        try:
            response = client.messages.create(
                model=MODEL,
                max_tokens=1000,
                system=SYSTEM_PROMPT,
                messages=[{"role": "user", "content": user_msg}],
            )
            raw = "".join(b.text for b in response.content if b.type == "text")
            matches = parse_matches(raw)
            if matches is not None:
                return matches
            print(f"WARNING: unreadable answer for '{item['title']}'")
        except anthropic.APIError as exc:
            print(f"WARNING: API error on '{item['title']}': {exc}")
        time.sleep(5 * (attempt + 1))
    return None  # left unseen, so it is retried tomorrow


# --------------------------------------------------------------------------
# Sending the alert
# --------------------------------------------------------------------------

def send_email(subject, body):
    if DRY_RUN:
        print(f"\n--- EMAIL (dry run) ---\nSubject: {subject}\n\n{body}")
        return
    sender = os.environ["BOT_EMAIL"]
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = os.environ.get("NOTIFY_TO") or sender
    msg.set_content(body)
    with smtplib.SMTP_SSL(os.environ.get("SMTP_HOST", "smtp.gmail.com"), 465) as smtp:
        smtp.login(sender, os.environ["BOT_EMAIL_PASSWORD"])
        smtp.send_message(msg)
    print(f"Email sent: {subject}")


def format_digest(matches):
    blocks = []
    for m in matches:
        blocks.append("\n".join([
            (m.get("headline") or m.get("title") or "(untitled)").upper(),
            f"From:   {m.get('doc_type') or m.get('source', '')} – "
            f"\u201c{m.get('title', '')}\u201d",
            f"Type:   {m.get('type', 'Change to an existing regime')}",
            f"Stage:  {m.get('stage', 'unknown')}",
            f"What:   {m.get('why', '')}",
            f"Link:   {m.get('link') or 'see source'}",
        ]))
    return ("\n\n" + "-" * 40 + "\n\n").join(blocks) + "\n"


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    today = datetime.now(timezone.utc).strftime("%d %b %Y")
    first_run = not SEEN_FILE.exists()
    seen = load_seen()

    items = []
    for feed in FEEDS:
        items += fetch_feed_items(feed)
    items += fetch_email_items()

    if TEST_MODE:
        # Check the 3 newest items from each source and change nothing.
        per_source = {}
        for item in items:
            per_source.setdefault(item["source"], [])
            if len(per_source[item["source"]]) < 3:
                per_source[item["source"]].append(item)
        new_items = [i for group in per_source.values() for i in group]
    else:
        new_items = [i for i in items if i["id"] not in seen]
        # A source added since the bot started (e.g. the PRA feeds) is
        # recorded silently the first time it appears, so you aren't sent
        # alerts about everything that was already sitting in its feed.
        known = {k.split("|", 1)[0] for k in seen}
        if seen:
            now = datetime.now(timezone.utc).isoformat()
            fresh = [i for i in new_items
                     if i["id"].split("|", 1)[0] not in known]
            for item in fresh:
                seen[item["id"]] = now
            if fresh:
                print(f"Recorded {len(fresh)} items from newly added sources "
                      f"as a starting point")
            new_items = [i for i in new_items if i not in fresh]
    print(f"{len(new_items)} items to check")

    if first_run and not TEST_MODE:
        # Record what already exists so you aren't flooded with old news.
        now = datetime.now(timezone.utc).isoformat()
        for item in new_items:
            seen[item["id"]] = now
        save_seen(seen)
        send_email(
            "FCA watch is set up",
            f"Your FCA regulatory watch is working.\n\n"
            f"It recorded {len(new_items)} existing items as a starting point. "
            f"From now on you'll get an email only when something new changes "
            f"the scope of FCA regulation or how a sector is regulated.",
        )
        return

    client = anthropic.Anthropic()
    matches = []
    for item in new_items:
        result = classify(client, item)
        if result is None:
            continue
        seen[item["id"]] = datetime.now(timezone.utc).isoformat()
        for m in result:
            m["source"] = item["source"]
            if not m.get("link"):
                m["link"] = item["link"]
            matches.append(m)

    if TEST_MODE:
        body = (f"Test run: checked {len(new_items)} recent items.\n\n"
                + (format_digest(matches) if matches
                   else "None of them were flagged as regulatory scope changes, "
                        "which is normal for most days."))
        send_email(f"[TEST] FCA watch – {len(matches)} flagged ({today})", body)
        return

    save_seen(seen)
    if matches:
        send_email(
            f"FCA/PRA regulatory change alert – {len(matches)} item(s) ({today})",
            format_digest(matches),
        )
    elif SEND_NO_CHANGE_EMAIL:
        checked = (f"The bot checked {len(new_items)} new publication(s) since "
                   f"its last run and none of them qualified."
                   if new_items else
                   "There were no new publications since its last run.")
        send_email(
            f"FCA/PRA regulatory watch – no changes today ({today})",
            f"No changes found today.\n\n"
            f"There are no new areas being brought into regulation and no "
            f"material changes to existing regimes from the FCA, the Bank of "
            f"England / PRA, HM Treasury or new UK legislation.\n\n"
            f"{checked}\n",
        )
    else:
        print("Nothing relevant today; no email sent.")


if __name__ == "__main__":
    main()
