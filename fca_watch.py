"""
Regulatory change watcher.

Runs two "watches" once a day, each with its own sources, screening
instructions and email:

  1. FCA/PRA watch – changes to the scope of FCA or PRA regulation, or material
     changes to how a sector is regulated (including the capital and other
     prudential requirements on banks and insurers).

  2. Just watch – parliamentary activity (Hansard, bills), government and
     regulator publications, and trade association positions on the pensions
     and life insurance sector, as they affect Just Group plc (formerly Just
     Retirement).

For each watch the script:
  a. Collects new items from its sources (RSS/Atom feeds, news pages of
     organisations without feeds, and alert emails in the bot's inbox).
  b. Asks Claude whether each item is relevant, using that watch's
     instructions.
  c. Emails a digest of relevant items or, if none qualify, a short
     "no changes today" email (see SEND_NO_CHANGE_EMAIL).

It remembers what each watch has already checked in seen.json, so nobody is
alerted twice about the same thing. Sources added later are recorded silently
the first time they appear, so old items in them don't trigger alerts.

Settings come from environment variables (GitHub Actions secrets):
  ANTHROPIC_API_KEY   - your Anthropic API key (required)
  BOT_EMAIL           - the Gmail address the bot uses (required)
  BOT_EMAIL_PASSWORD  - a Gmail *app password* for that address (required)
  NOTIFY_TO           - where FCA/PRA alerts are sent (defaults to BOT_EMAIL)
  NOTIFY_TO_JUST      - where Just alerts are sent (defaults to NOTIFY_TO)
  TEST_NOTIFY_TO      - where test-run emails are sent (defaults to the
                        normal recipients)
  MODEL               - Claude model to use (defaults to claude-haiku-5-5)
  TEST_MODE           - "true" to check the newest items, email the result
                        and change nothing (for trying it out)
  DRY_RUN             - "true" to print emails instead of sending them
"""

import email
import imaplib
import json
import os
import re
import smtplib
import time
import urllib.request
from datetime import datetime, timedelta, timezone
from email.header import decode_header, make_header
from email.message import EmailMessage
from html import unescape
from pathlib import Path
from urllib.parse import urljoin

import anthropic
import feedparser

# --------------------------------------------------------------------------
# Settings
# --------------------------------------------------------------------------

SEEN_FILE = Path(__file__).with_name("seen.json")
MAX_SEEN = 20000  # oldest entries are dropped beyond this
MODEL = os.environ.get("MODEL") or "claude-haiku-5-5"
TEST_MODE = os.environ.get("TEST_MODE", "").lower() in ("1", "true", "yes")
DRY_RUN = os.environ.get("DRY_RUN", "").lower() in ("1", "true", "yes")

# Send a short "no changes today" email on days when nothing qualifies.
# Set to False to only hear from the bot when something is flagged.
SEND_NO_CHANGE_EMAIL = True

USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 "
              "regulatory-watch-bot/2.0")

# --------------------------------------------------------------------------
# Sources
# --------------------------------------------------------------------------
# Three kinds of source:
#   "feed"  - an RSS or Atom feed.
#   "page"  - a news listing page for organisations without a feed. The bot
#             picks out links matching link_pattern and, for new items, opens
#             the article to read its text.
#   "email" - alert emails in the bot's Gmail inbox from a given sender.
# "keywords" (optional) pre-filters busy sources so only plausibly relevant
# items are sent to Claude, which keeps costs tiny.
# In page URLs, {year} and {prev_year} are filled in automatically.

SOURCES = [
    # ---- Original FCA/PRA sources -------------------------------------------
    {
        "name": "FCA news",
        "kind": "feed",
        "url": "https://www.fca.org.uk/news/rss.xml",
    },
    {
        # Everything the PRA publishes: consultation papers, policy
        # statements, supervisory statements, statements of policy.
        "name": "PRA publications",
        "kind": "feed",
        "url": "https://www.bankofengland.co.uk/rss/prudential-regulation-publications",
    },
    {
        # Bank of England news. Filtered so interest-rate and monetary policy
        # news is never sent to Claude; only prudential/regulatory items are.
        "name": "Bank of England news",
        "kind": "feed",
        "url": "https://www.bankofengland.co.uk/rss/news",
        "keywords": [
            "prudential", "pra ", "capital", "liquidity", "solvency",
            "leverage", "basel", "buffer", "resolution", "ring-fenc",
            "insurer", "insurance", "regulat", "financial policy committee",
        ],
    },
    {
        "name": "HM Treasury publications",
        "kind": "feed",
        "url": "https://www.gov.uk/search/all.atom?organisations%5B%5D=hm-treasury",
    },
    {
        "name": "New UK statutory instruments",
        "kind": "feed",
        "url": "https://www.legislation.gov.uk/new/uksi/data.feed",
        "keywords": [
            "financial services", "financial conduct", "regulated activities",
            "consumer credit", "payment", "electronic money", "cryptoasset",
            "funeral", "insurance", "pension", "markets", "annuit",
            "retirement", "occupational",
        ],
    },
    {
        "name": "FCA email alert",
        "kind": "email",
        "from": "fca",       # matches fca.org.uk and the GovDelivery sender
        "id_group": "email",  # kept as "email" so existing records still match
    },

    # ---- Added for the Just watch -------------------------------------------
    {
        # Debates, written questions and answers, statements and committee
        # mentions in the Commons and Lords, via TheyWorkForYou keyword alerts
        # sent to the bot's inbox (TheyWorkForYou is built on Hansard).
        "name": "Hansard (TheyWorkForYou alert)",
        "kind": "email",
        "from": "theyworkforyou",
        "id_group": "email-twfy",
    },
    {
        # New public bills and bills that have moved to a new stage.
        "name": "Parliament public bills",
        "kind": "feed",
        "url": "https://bills.parliament.uk/rss/publicbills.rss",
    },
    {
        "name": "DWP publications",
        "kind": "feed",
        "url": "https://www.gov.uk/search/all.atom?organisations%5B%5D=department-for-work-pensions",
        "keywords": [
            "pension", "annuit", "retirement", "defined benefit", "superfund",
            "surplus", "trustee", "auto-enrol", "automatic enrolment",
            "dashboard", "later life", "decumulation", "pensions commission",
            "consolidation", "small pots", "value for money",
        ],
    },
    {
        "name": "The Pensions Regulator",
        "kind": "page",
        "pages": [
            "https://www.thepensionsregulator.gov.uk/media-hub/press-releases?year={year}",
            "https://www.thepensionsregulator.gov.uk/media-hub/press-releases?year={prev_year}",
        ],
        "link_pattern": r"/media-hub/press-releases/\d{4}-press-releases/[A-Za-z0-9-]+/?$",
    },
    {
        "name": "Pensions UK",
        "kind": "page",
        "pages": ["https://www.pensionsuk.org.uk/News"],
        "link_pattern": r"pensionsuk\.org\.uk/News/Article/[^/?#]+$",
    },
    {
        "name": "Association of British Insurers",
        "kind": "page",
        "pages": [
            "https://www.abi.org.uk/news/news-articles/",
            "https://www.abi.org.uk/news/",
        ],
        "link_pattern": r"abi\.org\.uk/news/news-articles/\d{4}/\d{1,2}/[A-Za-z0-9-]+/?$",
    },
    {
        "name": "Equity Release Council",
        "kind": "page",
        "pages": ["https://www.equityreleasecouncil.com/information-hub/news/"],
        "link_pattern": r"equityreleasecouncil\.com/news/[A-Za-z0-9-]+/?$",
    },
]

# --------------------------------------------------------------------------
# Screening instructions. Edit these to tune what each watch flags.
# --------------------------------------------------------------------------

JSON_FORMAT = """
An item may be a single publication or an email digest listing several
publications or parliamentary mentions. Flag each relevant one separately.

Reply with ONLY a JSON object, no other text:
{"matches": [{"headline": "...", "title": "...", "doc_type": "...", "type": "...", "stage": "...", "why": "...", "link": "..."}]}
- headline: your own plain-English heading (max 12 words) saying what is
  changing and for whom. It must make sense to someone who has not seen the
  publication.
- title: the publication's original title (or debate/question heading),
  copied exactly.
- doc_type: what kind of publication it is and who it is from, e.g.
  "FCA consultation paper", "PRA policy statement", "HM Treasury
  consultation", "Statutory instrument", "House of Commons debate",
  "House of Lords written answer", "Westminster Hall debate", "Public bill
  (Commons report stage)", "DWP consultation", "TPR press release",
  "Pensions UK press release", "ABI response", "Equity Release Council
  statement".
- stage: one of "Early idea / discussion", "Consultation", "Final rules",
  "Legislation", "Coming into force"
- link: the URL if one is given, otherwise ""
If nothing qualifies, reply {"matches": []}"""

FCA_PROMPT = """You screen UK financial-services publications for one reader.
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
""" + JSON_FORMAT + """
- type: either "New to regulation" or "Change to an existing regime".
  Use "New to regulation" ONLY if the publication itself says the activity,
  product, industry or type of firm is not currently regulated by the FCA or
  PRA (or is being taken out of regulation). If it amends, overhauls or
  refers to rules that already apply, or if you are unsure, use "Change to
  an existing regime".
- why: one plain-English sentence saying what is changing and for whom"""

JUST_PROMPT = """You screen UK parliamentary, government, regulator and trade
association material for a public affairs team monitoring the pensions and
life insurance sector on behalf of Just Group plc (formerly Just Retirement,
trading as "Just"). Just is a UK retirement specialist. Its main businesses
are: defined benefit pension de-risking (bulk purchase annuities, buy-ins and
buy-outs); individual retirement income (guaranteed income for life
annuities, including medically underwritten and care annuities); lifetime
mortgages (equity release); and retirement advice and guidance services.

FLAG an item if it does any of these (including early ideas, parliamentary
debate and questions, consultations, bills and their stages, final rules,
statutory instruments or commencement dates):
- Mentions Just Group, Just Retirement or "Just" the company by name (only
  when it clearly means the company). Always flag these.
- Proposes, debates or makes changes to legislation, regulation or
  government or regulator policy affecting:
  * annuities and retirement income: decumulation, default retirement
    income solutions under the Pension Schemes Act 2026, the advice/guidance
    boundary and targeted support for retirement decisions, pension freedoms
  * defined benefit pensions: scheme funding, surplus release, superfunds
    and consolidation, buy-ins and buy-outs, the Pension Protection Fund,
    Pensions Regulator codes and powers, trustee duties
  * the prudential regime for life insurers: Solvency UK, the matching
    adjustment, funded reinsurance, bulk annuity stress tests, capital
  * equity release and later-life lending: lifetime mortgage rules, later
    life mortgage advice, Equity Release Council standards
  * long-term care funding, where it affects how people fund care in
    retirement
  * pension taxation (e.g. inheritance tax on pensions, tax-free lump sums)
    and the state pension, where it affects retirement income decisions
  * investment requirements or incentives for pension schemes and insurers
    (e.g. Mansion House commitments), and how the Consumer Duty applies to
    retirement products
- Reports a trade association (e.g. Pensions UK, ABI, Equity Release
  Council) setting out a position on, responding to, or calling for one of
  the changes above.
- Announces a parliamentary committee inquiry or report on any of the
  topics above.

DO NOT flag: monetary policy and interest rates; market statistics and
sales data; member news, events, awards, conferences and appointments;
general insurance (motor, home, travel, health) unless the change applies to
all insurers; local government or public sector pension scheme
administration unless it affects private-sector schemes or insurers;
routine parliamentary business with no substantive content on these topics
(e.g. a passing mention in a list); enforcement against individual firms
other than Just; scams and consumer warnings; routine or minor technical
amendments.
""" + JSON_FORMAT + """
- type: one of "New to regulation", "Change to an existing regime" or
  "Parliamentary or industry scrutiny". Use "New to regulation" ONLY if the
  material itself says the activity is not currently regulated (or is being
  taken out of regulation). Use "Parliamentary or industry scrutiny" for
  debates, questions, committee work or trade association calls that do not
  themselves propose or make a specific change. Otherwise, or if unsure,
  use "Change to an existing regime".
- why: one plain-English sentence saying what is happening and why it
  matters to Just. If Just is named, start with "Just named: "."""

# --------------------------------------------------------------------------
# Watches: which sources each one reads and where its email goes
# --------------------------------------------------------------------------

WATCHES = [
    {
        "key": "fca",
        "seen_prefix": "",  # original watch; records kept in the old format
        "sources": {
            "FCA news", "PRA publications", "Bank of England news",
            "HM Treasury publications", "New UK statutory instruments",
            "FCA email alert",
        },
        "prompt": FCA_PROMPT,
        "notify_env": ["NOTIFY_TO"],
        "alert_subject": "FCA/PRA regulatory change alert",
        "none_subject": "FCA/PRA regulatory watch – no changes today",
        "none_body": (
            "There are no new areas being brought into regulation and no "
            "material changes to existing regimes from the FCA, the Bank of "
            "England / PRA, HM Treasury or new UK legislation."
        ),
    },
    {
        "key": "just",
        "seen_prefix": "just::",
        "sources": None,  # None = every source above
        "prompt": JUST_PROMPT,
        "notify_env": ["NOTIFY_TO_JUST", "NOTIFY_TO"],
        "alert_subject": "Just – pensions & insurance alert",
        "none_subject": "Just – pensions & insurance watch – no changes today",
        "none_body": (
            "No relevant parliamentary activity, regulatory changes or trade "
            "association positions affecting the pensions and life insurance "
            "sector were found today across Hansard, Parliament bills, the "
            "FCA, the Bank of England / PRA, HM Treasury, DWP, the Pensions "
            "Regulator, Pensions UK, the ABI, the Equity Release Council or "
            "new UK legislation."
        ),
    },
]

# Sources that could not be read this run, reported at the foot of emails.
SOURCE_PROBLEMS = {}


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

def clean(text, limit):
    """Strip HTML and squash whitespace."""
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = unescape(re.sub(r"\s+", " ", text)).strip()
    return text[:limit]


def http_get(url):
    req = urllib.request.Request(url, headers={
        "User-Agent": USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,*/*;q=0.8",
        "Accept-Language": "en-GB,en;q=0.9",
    })
    with urllib.request.urlopen(req, timeout=30) as resp:
        charset = resp.headers.get_content_charset() or "utf-8"
        return resp.read().decode(charset, "replace")


def group_of(item_id):
    """The source group an item id belongs to (the part before '|')."""
    return item_id.split("|", 1)[0]


def load_seen():
    if SEEN_FILE.exists():
        return json.loads(SEEN_FILE.read_text())
    return {}


def save_seen(seen):
    # Keep only the most recent MAX_SEEN entries.
    newest = sorted(seen.items(), key=lambda kv: kv[1])[-MAX_SEEN:]
    SEEN_FILE.write_text(json.dumps(dict(newest), indent=0))


def seen_for_watch(seen, watch):
    """The item ids a watch has already checked."""
    prefix = watch["seen_prefix"]
    if prefix:
        return {k[len(prefix):] for k in seen if k.startswith(prefix)}
    return {k for k in seen if "::" not in k}


def keyword_ok(source, title, text):
    if not source.get("keywords"):
        return True
    haystack = f"{title} {text}".lower()
    return any(k in haystack for k in source["keywords"])


# --------------------------------------------------------------------------
# Collecting items
# --------------------------------------------------------------------------

def fetch_feed_items(source):
    parsed = feedparser.parse(source["url"], agent=USER_AGENT)
    if not parsed.entries:
        reason = parsed.get("bozo_exception", "feed was empty")
        print(f"WARNING: no items read from {source['name']}: {reason}")
        SOURCE_PROBLEMS[source["name"]] = "feed could not be read"
        return []

    items = []
    for entry in parsed.entries:
        title = clean(entry.get("title", ""), 300)
        summary = clean(entry.get("summary", ""), 2000)
        if not keyword_ok(source, title, summary):
            continue
        uid = entry.get("id") or entry.get("link") or title
        items.append({
            "id": f"{source['name']}|{uid}",
            "source": source["name"],
            "title": title,
            "link": entry.get("link", ""),
            "text": summary,
        })
    print(f"{source['name']}: {len(items)} items")
    return items


ANCHOR_RE = re.compile(r"<a\b[^>]*?href\s*=\s*[\"']([^\"']+)[\"'][^>]*>(.*?)</a>",
                       re.I | re.S)


def extract_links(html, base_url, pattern):
    """Return {url: title} for links on a page matching pattern."""
    found = {}
    for match in ANCHOR_RE.finditer(html):
        url = urljoin(base_url, unescape(match.group(1).strip())).split("#")[0]
        if not re.search(pattern, url):
            continue
        title = clean(match.group(2), 300)
        if len(title) > len(found.get(url, "")):
            found[url] = title
    for url, title in found.items():
        if not title or title.lower() in ("read more", "more", "find out more"):
            slug = url.rstrip("/").rsplit("/", 1)[-1]
            found[url] = slug.replace("-", " ").strip().capitalize()
    return found


def fetch_page_items(source):
    year = datetime.now(timezone.utc).year
    found, errors = {}, []
    for page in source["pages"]:
        url = page.format(year=year, prev_year=year - 1)
        try:
            links = extract_links(http_get(url), url, source["link_pattern"])
            for link, title in links.items():
                if len(title) > len(found.get(link, "")):
                    found[link] = title
        except Exception as exc:
            errors.append(f"{url}: {exc}")
    if not found:
        detail = "; ".join(errors) or "no news links found on the page"
        print(f"WARNING: no items read from {source['name']}: {detail}")
        SOURCE_PROBLEMS[source["name"]] = "news page could not be read"
        return []

    items = []
    for link, title in found.items():
        if not keyword_ok(source, title, ""):
            continue
        items.append({
            "id": f"{source['name']}|{link}",
            "source": source["name"],
            "title": title,
            "link": link,
            "text": "",
            "needs_article": True,
        })
    print(f"{source['name']}: {len(items)} items")
    return items


def fetch_article_text(url, title, limit=5000):
    """Read the main text of an article page (used for page sources)."""
    html = http_get(url)
    html = re.sub(r"<(script|style|nav|header|footer|aside|form|noscript)\b.*?</\1>",
                  " ", html, flags=re.I | re.S)
    text = clean(html, 200000)
    start = text.find(title[:60]) if title else -1
    return text[start:start + limit] if start >= 0 else text[:limit]


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


def fetch_email_items(sources):
    """Read alert emails from the bot's Gmail inbox (last 3 days)."""
    user = os.environ.get("BOT_EMAIL")
    password = os.environ.get("BOT_EMAIL_PASSWORD")
    if not sources:
        return []
    if not user or not password:
        print("No bot inbox configured; skipping alert emails.")
        return []

    since = (datetime.now(timezone.utc) - timedelta(days=3)).strftime("%d-%b-%Y")
    items = []
    try:
        imap = imaplib.IMAP4_SSL(os.environ.get("IMAP_HOST", "imap.gmail.com"))
        imap.login(user, password)
        imap.select("INBOX", readonly=True)
        for source in sources:
            _, data = imap.search(None, f'(SINCE {since} FROM "{source["from"]}")')
            count = 0
            for num in data[0].split():
                _, msg_data = imap.fetch(num, "(RFC822)")
                msg = email.message_from_bytes(msg_data[0][1])
                subject = str(make_header(decode_header(msg.get("Subject", ""))))
                uid = msg.get("Message-ID") or f"{subject}|{msg.get('Date')}"
                items.append({
                    "id": f"{source['id_group']}|{uid}",
                    "source": source["name"],
                    "title": subject,
                    "link": "",
                    "text": email_body_text(msg, 15000),
                })
                count += 1
            print(f"{source['name']}: {count} items")
        imap.logout()
    except Exception as exc:  # keep going even if the inbox fails
        print(f"WARNING: could not read the bot inbox: {exc}")
        for source in sources:
            SOURCE_PROBLEMS[source["name"]] = "bot inbox could not be read"
    return items


def collect_items():
    items = []
    for source in SOURCES:
        try:
            if source["kind"] == "feed":
                items += fetch_feed_items(source)
            elif source["kind"] == "page":
                items += fetch_page_items(source)
        except Exception as exc:
            print(f"WARNING: {source['name']} failed: {exc}")
            SOURCE_PROBLEMS[source["name"]] = "could not be read"
    items += fetch_email_items([s for s in SOURCES if s["kind"] == "email"])
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


def classify(client, item, prompt):
    """Return a list of matches, or None if Claude couldn't be reached."""
    user_msg = (
        f"Source: {item['source']}\nTitle: {item['title']}\n"
        f"Link: {item['link'] or 'n/a'}\n\nContent:\n{item['text'] or '(title only)'}"
    )
    for attempt in range(3):
        try:
            response = client.messages.create(
                model=MODEL,
                max_tokens=1500,
                system=prompt,
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
# Sending emails
# --------------------------------------------------------------------------

def recipients(watch):
    # Test runs go only to TEST_NOTIFY_TO, if it is set.
    if TEST_MODE and os.environ.get("TEST_NOTIFY_TO"):
        return os.environ["TEST_NOTIFY_TO"]
    for var in watch["notify_env"]:
        if os.environ.get(var):
            return os.environ[var]
    return os.environ.get("BOT_EMAIL", "")


def send_email(subject, body, to):
    if DRY_RUN:
        print(f"\n--- EMAIL (dry run) to {to} ---\nSubject: {subject}\n\n{body}")
        return
    sender = os.environ["BOT_EMAIL"]
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = to or sender
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
            f"“{m.get('title', '')}”",
            f"Type:   {m.get('type', 'Change to an existing regime')}",
            f"Stage:  {m.get('stage', 'unknown')}",
            f"What:   {m.get('why', '')}",
            f"Link:   {m.get('link') or 'see source'}",
        ]))
    return ("\n\n" + "-" * 40 + "\n\n").join(blocks) + "\n"


def problems_note(watch):
    names = [n for n in SOURCE_PROBLEMS
             if watch["sources"] is None or n in watch["sources"]]
    if not names:
        return ""
    return ("\n\nNote: these sources could not be read today, so anything "
            "they published will be picked up on a later run: "
            + ", ".join(names) + ".\n")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def watch_items(watch, items):
    if watch["sources"] is None:
        return items
    return [i for i in items if i["source"] in watch["sources"]]


def main():
    today = datetime.now(timezone.utc).strftime("%d %b %Y")
    now = datetime.now(timezone.utc).isoformat()
    first_run = not SEEN_FILE.exists()
    seen = load_seen()
    items = collect_items()

    # Work out what each watch needs to check.
    to_check = {}
    for watch in WATCHES:
        candidates = watch_items(watch, items)
        if TEST_MODE:
            # Check the 3 newest items from each source and change nothing.
            per_source = {}
            for item in candidates:
                group = per_source.setdefault(item["source"], [])
                if len(group) < 3:
                    group.append(item)
            to_check[watch["key"]] = [i for g in per_source.values() for i in g]
            continue

        done = seen_for_watch(seen, watch)
        new = [i for i in candidates if i["id"] not in done]
        # Sources this watch has never seen before (including every source
        # on a watch's first run) are recorded silently as a starting point,
        # so old items already sitting in them don't trigger alerts.
        known_groups = {group_of(k) for k in done}
        fresh = [i for i in new if group_of(i["id"]) not in known_groups]
        for item in fresh:
            seen[watch["seen_prefix"] + item["id"]] = now
        if fresh:
            print(f"[{watch['key']}] Recorded {len(fresh)} items from newly "
                  f"added sources as a starting point")
        fresh_ids = {i["id"] for i in fresh}
        to_check[watch["key"]] = [i for i in new if i["id"] not in fresh_ids]
        print(f"[{watch['key']}] {len(to_check[watch['key']])} items to check")

    if first_run and not TEST_MODE:
        save_seen(seen)
        for watch in WATCHES:
            send_email(
                f"{watch['alert_subject']} – watch is set up",
                "Your regulatory watch is working. It recorded the items "
                "already published as a starting point, and from now on "
                "you'll get a daily email about anything new.",
                recipients(watch),
            )
        return

    # Read the full text of new items from news pages (they have no summary).
    for item in {i["id"]: i for lst in to_check.values() for i in lst}.values():
        if item.get("needs_article") and not item["text"] and item["link"]:
            try:
                item["text"] = fetch_article_text(item["link"], item["title"])
            except Exception as exc:
                print(f"WARNING: could not open {item['link']}: {exc}")

    client = anthropic.Anthropic()
    for watch in WATCHES:
        matches = []
        checked = to_check[watch["key"]]
        for item in checked:
            result = classify(client, item, watch["prompt"])
            if result is None:
                continue
            if not TEST_MODE:
                seen[watch["seen_prefix"] + item["id"]] = (
                    datetime.now(timezone.utc).isoformat())
            for m in result:
                m["source"] = item["source"]
                if not m.get("link"):
                    m["link"] = item["link"]
                matches.append(m)

        to = recipients(watch)
        note = problems_note(watch)
        if TEST_MODE:
            body = (f"Test run: checked {len(checked)} recent items.\n\n"
                    + (format_digest(matches) if matches
                       else "None of them were flagged, which is normal for "
                            "most days.\n") + note)
            send_email(f"[TEST] {watch['alert_subject']} – "
                       f"{len(matches)} flagged ({today})", body, to)
        elif matches:
            send_email(f"{watch['alert_subject']} – {len(matches)} item(s) "
                       f"({today})", format_digest(matches) + note, to)
        elif SEND_NO_CHANGE_EMAIL:
            summary = (f"The bot checked {len(checked)} new item(s) since its "
                       f"last run and none of them qualified."
                       if checked else
                       "There were no new items since its last run.")
            send_email(f"{watch['none_subject']} ({today})",
                       f"No changes found today.\n\n{watch['none_body']}\n\n"
                       f"{summary}\n{note}", to)
        else:
            print(f"[{watch['key']}] Nothing relevant today; no email sent.")

    if not TEST_MODE:
        save_seen(seen)


if __name__ == "__main__":
    main()
