#!/usr/bin/env python3
"""Green Day とその周辺バンドのニュースをRSSで集め、
日本語の見出し・要約・解説を付けて docs/ に書き出す。

収集元のほとんどは英語の音楽メディアなので、見出しも要約も記事ごとの解説も
すべて日本語にして載せる。原文の全訳はしない（翻訳権の侵害になるため）。
原文を読みたい人向けには、詳細ページから Google 翻訳を通した原文へリンクする。

GitHub Actions から6時間ごとに実行され、差分がコミットされると
GitHub Pages 側のサイトが更新される。ローカルでも同じスクリプトが動く。
"""

from __future__ import annotations

import concurrent.futures
import datetime as dt
import hashlib
import html
import json
import os
import re
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from difflib import SequenceMatcher

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, BASE_DIR)

import llm_providers  # noqa: E402  （.env 読み込みより前でよい。キーは呼び出し時に参照される）

FEEDS_PATH = os.path.join(BASE_DIR, "feeds.json")
OUTPUT_PATH = os.path.join(BASE_DIR, "docs", "articles.json")
# 一度見送った記事のID置き場。同じ記事がRSSに数日残るので、
# これが無いと毎回おなじ記事をLLMに投げ直すことになる。
SKIPPED_PATH = os.path.join(BASE_DIR, "docs", "skipped.json")
DETAIL_DIR = os.path.join(BASE_DIR, "docs", "articles")

USER_AGENT = "greenday-news/1.0 (+https://github.com/mifune39428)"
FETCH_TIMEOUT = 25

# 新しく取り込む記事の対象期間。これより古い記事は拾わない。
# 音楽ニュースは1本の発表が数日かけて各媒体に広がるので、少し長めに取る。
INTAKE_DAYS = 5
# サイトに残す期間と件数の上限。
KEEP_DAYS = 45
KEEP_MAX = 400
# 1回のLLM呼び出しでまとめて処理する記事数。
# Groqの無料枠は分あたりトークン数（TPM 6000）が厳しいので、大きくし過ぎない。
BATCH_SIZE = 5
# 1回の実行で日本語化する上限。無料枠の1日あたり回数を使い切らないための蓋。
# 溢れた分は次の実行（6時間後）に回る。
MAX_NEW_PER_RUN = 40
# そのうち Green Day 本体の記事のために空けておく枠。
# 周辺バンドは数が多く、素で回すと本命が押し出される。
CORE_QUOTA = 16
# 1回の実行で解説（詳細ページ）を作る件数と、同時に走らせる数。
MAX_DETAILS_PER_RUN = 25
DETAIL_WORKERS = 3
# ページから読み取った公開日がこれより古い記事は載せない。
# Googleニュースは何年も前の記事を今日の日付で配ってくることがある。
STALE_DAYS = 40
# 見送った記事IDを覚えておく期間。RSSから消えれば二度と来ないので短くてよい。
SKIP_MEMORY_DAYS = 14
# 1回の実行で、過去の記事のサムネイルを取りに行く件数の上限。
BACKFILL_PER_RUN = 40
# 同じバンドの同じ日の記事を、いくつまで載せるか。
# 大きなライブが1本あると各紙が別々の角度で書くので（開演前・レポ・写真・出演者の発言）、
# 見出しが似ていなくても一覧が同じ公演で埋まる。数を決めて上から取るのが確実。
MAX_PER_BAND_DAY = 3

CATEGORIES = [
    "新曲・新作",
    "ライブ・ツアー",
    "フェス出演",
    "メンバー・発言",
    "再結成・メンバー変更",
    "再発・記念盤",
    "映像・映画・書籍",
    "チャート・受賞",
    "その他",
]

# 記事の主役として選ばせるバンド。ここに無いバンドは「その他」に寄せる。
# 画面のチップは実際に記事があるバンドしか出ないので、多めに並べてよい。
BANDS = [
    "Green Day",
    "Blink-182",
    "The Offspring",
    "Rancid",
    "Bad Religion",
    "NOFX",
    "Sum 41",
    "Weezer",
    "My Chemical Romance",
    "Fall Out Boy",
    "Paramore",
    "Alkaline Trio",
    "Descendents",
    "Social Distortion",
    "Dropkick Murphys",
    "Pennywise",
    "AFI",
    "Jimmy Eat World",
    "Rise Against",
    "The Interrupters",
    "Good Charlotte",
    "New Found Glory",
    "Simple Plan",
    "Anti-Flag",
    "The Linda Lindas",
    "その他",
]

CORE_BAND = "Green Day"

# この語が見出しか抜粋に入っていない記事は拾わない（LLMに投げる前のふるい）。
# 表記ゆれを吸うため、比較の前に空白・中黒・ハイフンを落として小文字に揃える。
# 「Offspring」「Rancid」は普通の英単語でもあるので、ここは通して
# 実際にバンドの話かどうかはLLM側で判定させる。
KEYWORDS = [
    # Green Day 本体とメンバー、サイドプロジェクト
    "green day", "グリーンデイ", "billie joe armstrong", "ビリージョー",
    "mike dirnt", "マイクダーント", "tre cool", "tré cool", "トレクール",
    "pinhead gunpowder", "foxboro hot tubs", "the longshot", "the coverups",
    "dookie", "american idiot", "ドゥーキー", "アメリカンイディオット",
    # 周辺バンド
    "blink-182", "blink 182", "ブリンク182", "offspring", "オフスプリング",
    "rancid", "ランシド", "bad religion", "バッドレリジョン", "nofx",
    "sum 41", "サム41", "weezer", "ウィーザー",
    "my chemical romance", "マイケミカルロマンス", "マイケミ",
    "fall out boy", "フォールアウトボーイ", "paramore", "パラモア",
    "alkaline trio", "アルカリントリオ", "descendents", "ディセンデンツ",
    "social distortion", "ソーシャルディストーション",
    "dropkick murphys", "ドロップキックマーフィーズ",
    "pennywise", "ペニーワイズ", "operation ivy", "オペレーションアイヴィー",
    "jimmy eat world", "ジミーイートワールド", "rise against", "ライズアゲインスト",
    "the interrupters", "インタラプターズ", "good charlotte", "グッドシャーロット",
    "new found glory", "ニューファウンドグローリー", "simple plan", "シンプルプラン",
    "anti-flag", "アンタイフラッグ", "the linda lindas", "リンダリンダズ",
    "lagwagon", "screeching weasel", "yellowcard", "イエローカード",
    "taking back sunday", "the bouncing souls", "millencolin", "ミレンコリン",
    "hot water music", "against me", "the menzingers", "joyce manor",
]

# 記事URLで落とすもの。チケット転売・歌詞・セットリスト・写真だけのページは
# ニュースではないので入口で捨てる。
BLOCK_URL_RE = re.compile(
    r"/lyrics?/|/setlists?/|/tickets?/|/tour-dates?/|/photo/\d|/photos/|/gallery/"
    r"|/galleries/|/picture-gallery/|/videos?/|/ranking/|/quiz|/merch/|/shop/"
    r"|/product/|/tag/|/podcast/",
    re.I,
)

# Googleニュース経由で紛れ込む、報道ではないものの出典。部分一致で落とす。
BLOCK_SOURCES = [
    # 株価・投資の自動生成記事（"グリーンデイ"が銘柄名の話として混ざる）
    "Moomoo", "moomoo", "Yahoo Finance", "Yahoo!ファイナンス", "みんかぶ", "株探",
    "Investing.com", "Seeking Alpha", "Simply Wall St", "TipRanks", "Zacks",
    # チケット販売・公演データベース（告知の焼き直しで、数日で消える）
    "Ticketmaster", "StubHub", "SeatGeek", "Vivid Seats", "Bandsintown",
    "Songkick", "setlist.fm", "TicketNews", "Live Nation",
    # 中身の無いまとめ・SEO記事の量産元
    "Simplemost", "MSN", "Yahoo Entertainment", "BroadwayWorld", "Hindustan Times",
    "Times of India", "Sportskeeda", "EconoTimes", "Zenger",
    # 他媒体の発表を機械的に書き直して量産する海外の配信サイト。
    # 初回の収集では5件が入り込み、そのうち1件は公演の年まで違っていた。
    "Ad-hoc-news", "AOL", "OneIndia", "Devdiscourse", "Pressat",
    "Gazeta Express", "Modern Ghana", "Mshale", "streamlinefeed", "Music Times",
    "Contactmusic", "Ratings Game Music", "The Hans India", "Latin Times",
    "Pulse Nigeria", "Sahara Reporters", "Vanguard News",
    # 他媒体の記事を転載するだけの配信ポータル。数時間でページごと消えて404になる。
    "ｄメニューニュース", "dメニューニュース", "au Webポータル",
    "エキサイトニュース", "ニコニコニュース", "Infoseek", "ライブドアニュース",
    "NewsPicks", "gooニュース",
    # SNSと動画そのもの。記事ではないので出典にしない。
    "facebook.com", "Facebook", "Instagram", "YouTube", "TikTok", "Reddit",
    "X (formerly Twitter)", "Twitter",
]

# 記事ページではないドメイン。Googleニュース経由でSNSの投稿や動画が混ざる。
BLOCK_DOMAINS = (
    "facebook.com", "instagram.com", "twitter.com", "x.com", "youtube.com",
    "youtu.be", "tiktok.com", "reddit.com", "threads.net", "pinterest.",
    "open.spotify.com", "music.apple.com", "soundcloud.com",
)


def blocked_domain(url: str) -> bool:
    host = urllib.parse.urlsplit(url).netloc.lower()
    return any(host == d or host.endswith("." + d) or d in host for d in BLOCK_DOMAINS)

# Googleニュースの <source> がドメインのまま入ってくる媒体を、読める名前に直す。
DOMAIN_NAMES = {
    "news.yahoo.co.jp": "Yahoo!ニュース",
    "natalie.mu": "音楽ナタリー",
    "www.barks.jp": "BARKS",
    "nme-jp.com": "NME Japan",
    "www.udiscovermusic.jp": "uDiscoverMusic",
    "rockinon.com": "rockin'on",
    "千葉テレビ放送株式会社": "チバテレ",
    "チバテレ+": "チバテレ",
    "www.nme.com": "NME",
    "www.kerrang.com": "Kerrang!",
    "consequence.net": "Consequence",
    "www.stereogum.com": "Stereogum",
    "www.punknews.org": "Punknews.org",
    # 同じ媒体が名乗り方を変えて二重に出ないように寄せる。
    "Kerrang": "Kerrang!",
    "Consequence of Sound": "Consequence",
    "Theprp.com": "The PRP",
    "theprp.com": "The PRP",
    "Stereogum.com": "Stereogum",
    "NME.com": "NME",
    "Rolling Stone Japan": "Rolling Stone Japan",
    "Loudersound": "Louder",
    "loudersound.com": "Louder",
    "Guitar World Magazine": "Guitar World",
    "Alternative Press Magazine": "Alternative Press",
    "Brooklyn Vegan": "BrooklynVegan",
    "Spin": "SPIN",
}

JST = dt.timezone(dt.timedelta(hours=9))

ATOM = "{http://www.w3.org/2005/Atom}"
MEDIA = "{http://search.yahoo.com/mrss/}"
DC = "{http://purl.org/dc/elements/1.1/}"
CONTENT = "{http://purl.org/rss/1.0/modules/content/}"
RSS10 = "{http://purl.org/rss/1.0/}"


# --------------------------------------------------------------------------
# 下ごしらえ
# --------------------------------------------------------------------------

def load_env() -> None:
    """.env があれば読む（GitHub Actions では Secrets が環境変数で入るので不要）。"""
    path = os.path.join(BASE_DIR, ".env")
    if not os.path.exists(path):
        return
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, _, value = line.partition("=")
            os.environ.setdefault(key.strip(), value.strip().strip("'\""))


def strip_html(text: str) -> str:
    text = re.sub(r"(?is)<(script|style).*?</\1>", " ", text or "")
    text = re.sub(r"(?s)<[^>]+>", " ", text)
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def canonical_url(url: str) -> str:
    """トラッキング用のクエリを落として、同じ記事が別URLに見えないようにする。"""
    try:
        parts = urllib.parse.urlsplit(url.strip())
    except ValueError:
        return url.strip()
    query = [
        (k, v)
        for k, v in urllib.parse.parse_qsl(parts.query)
        if not k.lower().startswith(("utm_", "fbclid", "gclid", "ref", "at_"))
    ]
    # Google ニュース経由のリンクだけはクエリに記事IDが載るので触らない。
    if "news.google.com" in parts.netloc:
        query = urllib.parse.parse_qsl(parts.query)
    cleaned = parts._replace(query=urllib.parse.urlencode(query), fragment="")
    return urllib.parse.urlunsplit(cleaned).rstrip("/")


def article_id(url: str) -> str:
    return hashlib.sha1(canonical_url(url).encode("utf-8")).hexdigest()[:16]


def parse_date(raw: str) -> dt.datetime | None:
    raw = (raw or "").strip()
    if not raw:
        return None
    try:
        from email.utils import parsedate_to_datetime

        parsed = parsedate_to_datetime(raw)
        if parsed is not None:
            if parsed.tzinfo is None:
                parsed = parsed.replace(tzinfo=dt.timezone.utc)
            return parsed.astimezone(dt.timezone.utc)
    except (TypeError, ValueError):
        pass
    try:
        parsed = dt.datetime.fromisoformat(raw.replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=dt.timezone.utc)
        return parsed.astimezone(dt.timezone.utc)
    except ValueError:
        return None


# バンド名は媒体ごとに表記がぶれる（Blink-182 / blink 182 / ブリンク182、
# Green Day / グリーン・デイ / グリーンデイ）。空白・中黒・ハイフンを落として比べる。
NOISE_CHARS_RE = re.compile(r"[\s　・･\-‐‑–—_'’\"“”]+")


def fold(text: str) -> str:
    return NOISE_CHARS_RE.sub("", (text or "").lower())


FOLDED_KEYWORDS = [fold(word) for word in KEYWORDS]


def mentions_band(*texts: str) -> bool:
    haystack = fold(" ".join(texts))
    return any(word in haystack for word in FOLDED_KEYWORDS)


# --------------------------------------------------------------------------
# RSS / Atom / RDF の取得
# --------------------------------------------------------------------------

def _text(node, *paths: str) -> str:
    for path in paths:
        found = node.find(path)
        if found is not None:
            if found.text:
                return found.text
            # Atom の <link href="..."> のように属性側に入っている場合。
            href = found.get("href")
            if href:
                return href
    return ""


# 記事のサムネイルとして使わない画像（計測用の透明画像、ページ共通のアイコンなど）。
# 本文HTMLの最初の <img> を拾うと、媒体によっては「いいね」ボタンの絵が来る。
IMAGE_BLOCKLIST = (
    "feedburner", "gravatar", "/pixel", "1x1", "blank.gif", "spacer", "doubleclick",
    "icon_", "/icon", "-icon", "avatar", "/sprite", "/logo", "_logo", "banner_",
)
IMG_TAG_RE = re.compile(r'<img[^>]+src=["\']([^"\']+)["\']', re.I)
OG_IMAGE_RE = re.compile(
    r'<meta[^>]+(?:property|name)=["\'](?:og:image(?::url)?|twitter:image(?::src)?)["\']'
    r'[^>]+content=["\']([^"\']+)["\']|'
    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+'
    r'(?:property|name)=["\'](?:og:image(?::url)?|twitter:image(?::src)?)["\']',
    re.I,
)


def usable_image(url: str, base: str) -> str:
    url = html.unescape((url or "").strip())
    if not url:
        return ""
    url = urllib.parse.urljoin(base, url)
    if not url.startswith(("http://", "https://")):
        return ""
    if any(word in url.lower() for word in IMAGE_BLOCKLIST):
        return ""
    return url


def image_from_entry(entry, base: str) -> str:
    """RSSの中に入っている画像を探す。媒体ごとに置き場所が違うので順に当たる。"""
    for node in entry.findall(f"{MEDIA}thumbnail") + entry.findall(f"{MEDIA}content"):
        medium = (node.get("medium") or node.get("type") or "").lower()
        if medium and "image" not in medium:
            continue
        found = usable_image(node.get("url", ""), base)
        if found:
            return found

    for node in entry.findall("enclosure") + entry.findall(f"{ATOM}link"):
        if "image" in (node.get("type") or "").lower():
            found = usable_image(node.get("url") or node.get("href") or "", base)
            if found:
                return found

    # 本文HTMLの最初の <img>。多くの媒体はここにアイキャッチが入っている。
    raw_body = " ".join(
        node.text or ""
        for tag in ("description", f"{CONTENT}encoded", f"{RSS10}description",
                    f"{ATOM}summary", f"{ATOM}content")
        for node in entry.findall(tag)
    )
    for candidate in IMG_TAG_RE.findall(raw_body):
        found = usable_image(candidate, base)
        if found:
            return found
    return ""


# --------------------------------------------------------------------------
# Google ニュースのリンクを元媒体のURLに戻す
# --------------------------------------------------------------------------

GOOGLE_BATCH_URL = "https://news.google.com/_/DotsSplashUi/data/batchexecute"
SIGNATURE_RE = re.compile(r'data-n-a-sg="([^"]+)"')
TIMESTAMP_RE = re.compile(r'data-n-a-ts="([^"]+)"')


def resolve_google_url(url: str) -> str:
    """news.google.com の転送URLから、元媒体の記事URLを取り出す。

    転送ページはJavaScriptで飛ぶ作りなので、HTTPを追うだけでは元URLが分からない。
    ページに埋まっている署名（sg）と時刻（ts）を Google の batchexecute に投げると
    元URLが返る。取れなければ転送URLのまま使う（リンクとしては機能する）。
    """
    if "news.google.com" not in url:
        return url
    try:
        gid = url.split("/articles/")[1].split("?")[0]
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(request, timeout=15) as response:
            # 署名はページのかなり後ろに入っているので、途中で切らずに全部読む。
            page = response.read().decode("utf-8", errors="ignore")
        signature, timestamp = SIGNATURE_RE.search(page), TIMESTAMP_RE.search(page)
        if not signature or not timestamp:
            return url

        payload = [[
            "Fbv4je",
            json.dumps([
                "garturlreq",
                [["X", "X", ["X", "X"], None, None, 1, 1, "US:en", None, 1,
                  None, None, None, None, None, 0, 1],
                 "X", "X", 1, [1, 1, 1], 1, 1, None, 0, 0, None, 0],
                gid, int(timestamp.group(1)), signature.group(1),
            ]),
            None, "1",
        ]]
        data = urllib.parse.urlencode({"f.req": json.dumps([payload])}).encode()
        request = urllib.request.Request(
            GOOGLE_BATCH_URL,
            data=data,
            headers={
                "User-Agent": USER_AGENT,
                "Content-Type": "application/x-www-form-urlencoded;charset=UTF-8",
            },
        )
        with urllib.request.urlopen(request, timeout=15) as response:
            body = response.read().decode("utf-8", errors="ignore")
    except Exception:  # noqa: BLE001  取れなくても転送URLで記事は読める
        return url
    return parse_garturlres(body) or url


def parse_garturlres(body: str) -> str:
    """batchexecute の返事から元URLを取り出す。

    返事は `[["wrb.fr","Fbv4je","[\\"garturlres\\",\\"https://…\\",1]",…]]` の形で、
    URLは二重にJSONエスケープされている。素直に2段階で読む。
    """
    for line in body.splitlines():
        if "garturlres" not in line:
            continue
        try:
            for part in json.loads(line):
                if isinstance(part, list) and len(part) > 2 and part[0] == "wrb.fr":
                    inner = json.loads(part[2])
                    if len(inner) > 1 and str(inner[1]).startswith("http"):
                        return canonical_url(inner[1])
        except (json.JSONDecodeError, TypeError, ValueError):
            continue
    return ""


def resolve_google_urls(items: list[dict]) -> None:
    targets = [item for item in items if "news.google.com" in item["url"]]
    if not targets:
        return
    print(f"  Googleニュースのリンク {len(targets)}件を元媒体のURLに変換中 …")
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        for item, resolved in zip(targets, pool.map(lambda i: resolve_google_url(i["url"]), targets)):
            item["url"] = resolved
    remaining = sum(1 for item in targets if "news.google.com" in item["url"])
    print(f"  変換できたもの {len(targets) - remaining}件")


# 記事ページに書かれている公開日時。媒体ごとに置き場所が違うので順に当たる。
PUBLISHED_PATTERNS = [
    re.compile(r'<meta[^>]+property=["\']article:published_time["\'][^>]+content=["\']([^"\']+)', re.I),
    re.compile(r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']article:published_time["\']', re.I),
    re.compile(r'"datePublished"\s*:\s*"([^"]+)"', re.I),
    re.compile(r'<meta[^>]+name=["\'](?:pubdate|publish-date|date)["\'][^>]+content=["\']([^"\']+)', re.I),
    re.compile(r'<time[^>]+datetime=["\']([^"\']+)', re.I),
]


def page_meta(url: str) -> tuple[str, str]:
    """記事ページを1回だけ読み、og:image と公開日時を取り出す。

    Googleニュース経由だと、何年も前の記事が今日の日付で流れてくることがある。
    音楽メディアは記念日ネタで昔の記事を再配信することも多いので、
    ページ側に公開日が書いてあればそちらを見て古い記事を落とす。
    """
    try:
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(request, timeout=12) as response:
            head = response.read(250_000).decode("utf-8", errors="ignore")
            final_url = response.geturl()
    except Exception:  # noqa: BLE001  取れなくても記事自体は載せる
        return "", ""

    image = ""
    match = OG_IMAGE_RE.search(head)
    if match:
        image = usable_image(match.group(1) or match.group(2) or "", final_url)

    published = ""
    for pattern in PUBLISHED_PATTERNS:
        found = pattern.search(head)
        if found and parse_date(found.group(1)):
            published = found.group(1)
            break
    return image, published


def inspect_pages(items: list[dict], skipped: dict[str, str] | None = None) -> list[dict]:
    """掲載が決まった記事のページを1件ずつ読み、サムネイルと本当の公開日を確かめる。

    公開日が読めた記事はそちらの日付を採用し、古すぎるものは落とす。
    日付が書かれていない記事は、そのまま載せる（判断材料が無いので疑わない）。
    """
    if not items:
        return items
    print(f"  記事ページを確認 {len(items)}件 …")
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        metas = list(pool.map(lambda i: page_meta(i["url"]), items))

    now = dt.datetime.now(dt.timezone.utc)
    kept, images = [], 0
    for item, (image, published) in zip(items, metas):
        if image and not item.get("image"):
            item["image"] = image
            images += 1
        parsed = parse_date(published) if published else None
        if parsed:
            if parsed < now - dt.timedelta(days=STALE_DAYS):
                title = item.get("title_ja") or item["title_original"]
                print(f"  ・古い記事のため除外（{parsed.astimezone(JST):%Y-%m-%d}）: {title}")
                if skipped is not None:
                    skipped[item["id"]] = dt.datetime.now(dt.timezone.utc).isoformat()
                continue
            if parsed <= now + dt.timedelta(hours=12):
                item["published"] = parsed.isoformat()
        kept.append(item)
    print(f"  サムネイルを補えたもの {images}件 / 掲載 {len(kept)}件")
    return kept


def fetch_og_image(url: str) -> str:
    """RSSに画像が無い記事は、元ページの og:image を見に行く。"""
    try:
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(request, timeout=12) as response:
            head = response.read(200_000).decode("utf-8", errors="ignore")
            final_url = response.geturl()
    except Exception:  # noqa: BLE001  取れなくても記事自体は載せる
        return ""
    match = OG_IMAGE_RE.search(head)
    if not match:
        return ""
    return usable_image(match.group(1) or match.group(2) or "", final_url)


def fill_missing_images(items: list[dict], limit: int = 0) -> None:
    """画像がまだ無い記事について、元ページの og:image を取りに行く。

    limit を渡すと1回に取りに行く件数を抑える（既存記事の穴埋め用）。
    """
    targets = [item for item in items if not item.get("image")]
    if limit:
        targets = targets[:limit]
    if not targets:
        return
    print(f"  サムネイル未取得 {len(targets)}件をページから取得中 …")
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        for item, image in zip(targets, pool.map(lambda i: fetch_og_image(i["url"]), targets)):
            item["image"] = image
    print(f"  取得できたもの {sum(1 for item in targets if item['image'])}件")


def fetch_feed(feed: dict) -> list[dict]:
    request = urllib.request.Request(feed["url"], headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=FETCH_TIMEOUT) as response:
        raw = response.read()

    root = ET.fromstring(raw)
    entries = (
        root.findall(".//item")
        or root.findall(f".//{RSS10}item")
        or root.findall(f".//{ATOM}entry")
    )

    items = []
    for entry in entries:
        title = strip_html(_text(entry, "title", f"{ATOM}title", f"{RSS10}title"))
        link = _text(entry, "link", f"{RSS10}link", f"{ATOM}link").strip()
        if not link:
            # Atom は複数の <link> を持つので rel="alternate" を拾う。
            for candidate in entry.findall(f"{ATOM}link"):
                if candidate.get("rel", "alternate") == "alternate":
                    link = (candidate.get("href") or "").strip()
                    break
        if not title or not link:
            continue

        source = feed["name"]
        if feed.get("google_news"):
            # Google ニュースの見出しは「本文の見出し - 媒体名」の形。
            # 媒体名は <source> にも入っているので、そちらを出典として使う。
            actual = strip_html(_text(entry, "source"))
            if actual:
                source = DOMAIN_NAMES.get(actual, actual)
                if title.endswith(f" - {actual}"):
                    title = title[: -len(actual) - 3].strip()
            else:
                title = re.sub(r"\s+-\s+[^-]{2,30}$", "", title).strip()
        # rockin'on の見出しは「ニュース - 本文の見出し」の形。区分を落とす。
        title = re.sub(r"^(ニュース|NEWS|コラム|インタビュー)\s+-\s+", "", title).strip()

        if any(blocked in source for blocked in BLOCK_SOURCES):
            continue
        if BLOCK_URL_RE.search(link) or blocked_domain(link):
            continue

        published = parse_date(
            _text(entry, "pubDate", f"{DC}date", f"{ATOM}published", f"{ATOM}updated", "date")
        )
        body = strip_html(
            _text(
                entry,
                "description",
                f"{CONTENT}encoded",
                f"{RSS10}description",
                f"{ATOM}summary",
                f"{ATOM}content",
            )
        )
        # Google ニュースの description は他媒体へのリンク集なので要約の材料にならない。
        if feed.get("google_news"):
            body = ""

        # どのフィードも、対象バンドの名前が出てくる記事だけ拾う。
        # 総合的な音楽メディアが中心なので、これが無いと無関係な記事だらけになる。
        if feed.get("filter", True) and not mentions_band(title, body):
            continue

        items.append(
            {
                "id": article_id(link),
                "url": canonical_url(link),
                "title_original": title,
                "excerpt": body[:800],
                "source": source,
                "image": image_from_entry(entry, link),
                "from_google": bool(feed.get("google_news")),
                "lang": feed.get("lang", "en"),
                "region": feed.get("region", "global"),
                "published": (published or dt.datetime.now(dt.timezone.utc)).isoformat(),
            }
        )
    return items


def collect_feed_items(feeds: list[dict]) -> list[dict]:
    collected: list[dict] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        futures = {pool.submit(fetch_feed, feed): feed for feed in feeds}
        for future in concurrent.futures.as_completed(futures):
            feed = futures[future]
            try:
                items = future.result()
            except Exception as exc:  # 1本落ちても全体は続ける
                print(f"  × {feed['name']} ({feed['url'][:60]}…): {type(exc).__name__}: {exc}")
                continue
            print(f"  ○ {feed['name']}: {len(items)}件")
            collected.extend(items)
    return collected


# --------------------------------------------------------------------------
# 重複の除去
# --------------------------------------------------------------------------

def normalize_title(title: str) -> str:
    title = re.sub(r"[\s　]+", "", title.lower())
    return re.sub(r"[!-/:-@\[-`{-~、。「」・…—–\-]", "", title)


TOKEN_RE = re.compile(r"[A-Za-z]{2,}|[0-9]+|[ァ-ヶー]{2,}|[一-龥]{2,}")


def title_tokens(title: str) -> set[str]:
    return {t.lower() for t in TOKEN_RE.findall(title)}


def same_story(a: dict, b: dict) -> bool:
    """日本語化した見出しで、同じ出来事を伝えているかどうかを見る。

    音楽ニュースは1本の発表を各媒体が一斉に書くので、原題が違っても
    日本語の見出しになって初めて同じニュースだと分かる。
    """
    published_a, published_b = parse_date(a["published"]), parse_date(b["published"])
    if published_a and published_b and abs((published_a - published_b).total_seconds()) > 72 * 3600:
        return False

    left, right = normalize_title(a["title_ja"]), normalize_title(b["title_ja"])
    if SequenceMatcher(None, left, right).ratio() >= 0.75:
        return True

    tokens_a, tokens_b = title_tokens(a["title_ja"]), title_tokens(b["title_ja"])
    if len(tokens_a) >= 3 and len(tokens_b) >= 3:
        if len(tokens_a & tokens_b) / len(tokens_a | tokens_b) >= 0.7:
            return True
    return False


def dedupe_stories(
    new_items: list[dict], existing_items: list[dict]
) -> tuple[list[dict], set[str]]:
    """同じ出来事を伝える記事は1本に絞る。日本語の記事を優先して残す。

    掲載する新着と、入れ替えで取り下げる既存記事のIDを返す。
    """
    recent = existing_items[:150]
    ordered = sorted(new_items, key=lambda item: 0 if item["lang"] == "ja" else 1)
    kept: list[dict] = []
    replaced: set[str] = set()
    for item in ordered:
        older = next(
            (o for o in recent if o["id"] not in replaced and same_story(item, o)), None
        )
        if older is not None:
            # 海外の短報を先に載せたあとに国内媒体の記事が届いたら、そちらへ差し替える。
            if item["lang"] == "ja" and older.get("lang") != "ja":
                print(f"  ・国内記事に差し替え: {item['title_ja']}（{item['source']}）")
                replaced.add(older["id"])
                kept.append(item)
            else:
                print(f"  ・既出のため除外: {item['title_ja']}（{item['source']}）")
            continue
        if any(same_story(item, other) for other in kept):
            print(f"  ・重複のため除外: {item['title_ja']}（{item['source']}）")
            continue
        kept.append(item)
    return kept, replaced


def enforce_band_day_cap(items: list[dict], skipped: dict[str, str]) -> list[dict]:
    """同じバンド・同じ日の記事を MAX_PER_BAND_DAY 本までに絞る。

    見出しを比べる重複除去だけでは、同じ公演を別々の角度から書いた記事
    （開演前の告知・当日のレポ・共演者の話・メンバーの発言）が残ってしまう。
    語がほとんど重ならないので機械的には別の話に見えるが、読者にとっては同じ出来事。
    日ごとに数を決めて、注目度の高いものから残す。

    落とした記事は skipped に控える（次の実行でLLMに投げ直さないため）。
    """
    order = sorted(
        range(len(items)),
        key=lambda i: (
            # 日本語の記事は、同じ出来事を伝える英語の記事より読者の役に立つ。
            # 数が少ないので、ここで先に確保しないと英語の焼き直しに押し出される。
            0 if items[i].get("lang") == "ja" else 1,
            -items[i].get("importance", 3),
            0 if items[i].get("has_detail") else 1,
            0 if items[i].get("image") else 1,
            i,
        ),
    )
    now = dt.datetime.now(dt.timezone.utc).isoformat()
    counts: dict[tuple[str, str], int] = {}
    dropped: set[int] = set()
    for index in order:
        item = items[index]
        published = parse_date(item.get("published", ""))
        day = published.astimezone(JST).strftime("%Y-%m-%d") if published else "?"
        key = (item.get("band", "その他"), day)
        counts[key] = counts.get(key, 0) + 1
        if counts[key] > MAX_PER_BAND_DAY:
            dropped.add(index)
            skipped[item["id"]] = now
    if dropped:
        print(f"  ・同じバンドの同じ日の記事が多いため{len(dropped)}件を見送り")
        for index in sorted(dropped):
            print(f"    - {items[index].get('title_ja', '')}（{items[index]['source']}）")
    return [item for i, item in enumerate(items) if i not in dropped]


def is_duplicate(title: str, known_titles: list[str]) -> bool:
    target = normalize_title(title)
    if not target:
        return False
    for known in known_titles:
        if not known:
            continue
        if target == known:
            return True
        if abs(len(target) - len(known)) <= max(6, len(target) * 0.3):
            if SequenceMatcher(None, target, known).ratio() >= 0.86:
                return True
    return False


# --------------------------------------------------------------------------
# 日本語化（見出し・要約・分類）
# --------------------------------------------------------------------------

PROMPT_TEMPLATE = """あなたは Green Day とパンク／オルタナ周辺のバンドを追う日本語ニュースサイトの編集者です。
海外・国内の記事の見出しと抜粋を渡すので、日本の読者向けに「日本語の短い見出し」と「日本語の要約」を作り、
分類してください。英語の記事も必ず日本語で書きます。今日は{today}です（日本時間）。

厳守すること:
- 原文をそのまま写さない・逐語訳しない。事実を踏まえて自分の言葉で短くまとめる。
- 事実を足さない。抜粋に書かれていない日付・会場・曲名・数字を創作しない。
  抜粋が無く見出しだけの場合は、見出しから確実に言えることだけを書く。
- 見出し(title_ja)は日本語で45文字以内。煽らず、内容が分かる形にする。
  バンド名・人名・アルバム名・曲名は英語の原表記のまま残してよい。
- 要約(summary_ja)は日本語で80〜140文字。1〜3文。英語の記事も日本語で書く。
- relevant: 対象バンドそのものの話題なら true。
  他のアーティストの記事に「Green Day のような」と比喩で一度出てくるだけ、
  「Green Day を聴いて育った」という無関係な人物のコメント、株価や銘柄の自動生成記事、
  チケット販売ページの焼き直しは false。
- type は "report" か "recommend" のどちらか。
  report = バンドの動き（新曲・アルバム発表、ツアーやフェスの発表、メンバーの発言や
  インタビュー、脱退・加入、再発、映像作品、チャート成績、受賞など）を
  「起きたこと・これから起きること」として伝える記事。このサイトの中心なので必ず載せる。
  recommend = 編集部の好みで並べただけの記事。ニュースになる出来事が無く、
  「歴代ベスト〇曲」「アルバム全〇作を格付け」「〇選」「聴くべき」が主題のもの。
  判断の例:
    「Green Day が新曲を配信リリース」→ report
    「Billie Joe がインタビューで Dookie 制作を振り返る」→ report（本人の発言なので）
    「Green Day が来年の来日公演を発表」→ report
    「Green Day のアルバム全14作を格付け」→ recommend
    「歴代最高のパンク・ボーカリスト15人」→ recommend
  1枚のアルバム、1本の公演、1本の映像について書いたレビューは report にする
  （複数の作品を並べて順位を付けるものだけが recommend）。
  迷ったら report にする。
- noise: 求人・占い・株価の自動生成記事・見出しだけの転載など、
  そもそも記事の体をなしていないものだけ true。
- band は記事の主役を次から必ず1つ選ぶ: {bands}
  Green Day 本体、メンバー個人（Billie Joe Armstrong / Mike Dirnt / Tré Cool）、
  サイドプロジェクト（Pinhead Gunpowder / The Coverups / The Longshot / Foxboro Hot Tubs）
  の話題はすべて "Green Day" にする。一覧に無いバンドが主役なら "その他"。
- artists は記事に出てくるバンド名・人名を最大4つ、原表記のまま配列で。無ければ空配列。
- japan: 来日公演、日本のフェス出演、日本盤のリリース、日本での出来事など
  日本に関係する話題なら true。それ以外は false。
- category は次から必ず1つ選ぶ: {categories}
- importance は1〜5の整数。5=新アルバム発表や解散・再結成など誰もが知るべき発表、
  4=新曲リリース・大型ツアーやフェスの発表・来日公演の発表、3=普通のニュース、1=小ネタ。
- 出力はJSON配列のみ。前置き・説明・コードフェンスを付けない。

出力形式（要素数は入力と同じ{count}件、iは入力の番号）:
[{{"i":1,"relevant":true,"type":"report","noise":false,"title_ja":"...","summary_ja":"...","band":"Green Day","artists":["Green Day"],"japan":false,"category":"新曲・新作","importance":3}}]

入力記事:
{articles}
"""


def build_prompt(batch: list[dict]) -> str:
    lines = []
    for index, item in enumerate(batch, start=1):
        lines.append(
            f"[{index}] 出典: {item['source']}（{'英語' if item['lang'] == 'en' else '日本語'}）\n"
            f"見出し: {item['title_original']}\n"
            f"抜粋: {item['excerpt'][:600] or '(抜粋なし)'}\n"
        )
    return PROMPT_TEMPLATE.format(
        today=dt.datetime.now(JST).strftime("%Y年%-m月%-d日"),
        bands=" / ".join(BANDS),
        categories=" / ".join(CATEGORIES),
        count=len(batch),
        articles="\n".join(lines),
    )


def parse_llm_json(text: str, expected: int) -> list[dict]:
    cleaned = text.strip()
    cleaned = re.sub(r"^```(?:json)?\s*|\s*```$", "", cleaned, flags=re.MULTILINE).strip()
    start, end = cleaned.find("["), cleaned.rfind("]")
    if start == -1 or end == -1:
        raise llm_providers.ResponseInvalid("JSON配列が見つかりません")
    try:
        data = json.loads(cleaned[start : end + 1])
    except json.JSONDecodeError as exc:
        raise llm_providers.ResponseInvalid(f"JSONとして読めません: {exc}") from exc
    if not isinstance(data, list) or not data:
        raise llm_providers.ResponseInvalid("空の配列です")
    if len(data) != expected:
        raise llm_providers.ResponseInvalid(f"{expected}件のはずが{len(data)}件です")
    for entry in data:
        if not isinstance(entry, dict) or not entry.get("title_ja") or not entry.get("summary_ja"):
            raise llm_providers.ResponseInvalid("title_ja / summary_ja が欠けています")
    return data


def clean_artists(raw) -> list[str]:
    """記事に出てくるバンド名・人名。タグとして出すので短いものだけ残す。"""
    if not isinstance(raw, list):
        return []
    names, seen = [], set()
    for value in raw:
        name = re.sub(r"\s+", " ", str(value)).strip(" 　、,")
        if not name or len(name) > 30:
            continue
        key = fold(name)
        if key in seen:
            continue
        seen.add(key)
        names.append(name)
    return names[:4]


def enrich(items: list[dict], skipped: dict[str, str]) -> list[dict]:
    """LLMで日本語の見出し・要約・分類を付ける。失敗した分は捨てて次回に回す。

    載せないと判断した記事は skipped に控える（同じ記事を毎回LLMに投げ直さないため）。
    LLMの呼び出しに失敗した分は控えない。次回もう一度やり直す。
    """
    now = dt.datetime.now(dt.timezone.utc).isoformat()
    results: list[dict] = []
    for offset in range(0, len(items), BATCH_SIZE):
        batch = items[offset : offset + BATCH_SIZE]
        print(f"  日本語化 {offset + 1}〜{offset + len(batch)}件目 …")
        try:
            text = llm_providers.generate_text(
                build_prompt(batch),
                validate=lambda t, n=len(batch): parse_llm_json(t, n),
            )
            entries = parse_llm_json(text, len(batch))
        except llm_providers.LLMError as exc:
            # 生煮えの記事をサイトに出すより、今回は見送って次の実行で拾い直す。
            # RSSには数日分残っているので、枠が空けば自然に再挑戦される。
            print(f"  × 日本語化に失敗（この{len(batch)}件は次回に回します）: {exc}")
            continue

        by_index = {}
        for entry in entries:
            try:
                by_index[int(entry.get("i", 0))] = entry
            except (TypeError, ValueError):
                continue

        for index, item in enumerate(batch, start=1):
            entry = by_index.get(index) or entries[index - 1]
            if entry.get("relevant") is False:
                print(f"  ・対象バンドの話題ではないため除外: {item['title_original'][:50]}")
                skipped[item["id"]] = now
                continue
            if entry.get("noise") is True:
                print(f"  ・記事の体をなしていないため除外: {entry.get('title_ja', '')}")
                skipped[item["id"]] = now
                continue
            if str(entry.get("type", "report")).strip() == "recommend":
                print(f"  ・ランキング・〇選の記事のため除外: {entry.get('title_ja', '')}")
                skipped[item["id"]] = now
                continue
            category = str(entry.get("category", "")).strip()
            band = str(entry.get("band", "")).strip()
            item["title_ja"] = str(entry["title_ja"]).strip()
            item["summary_ja"] = str(entry["summary_ja"]).strip()
            item["category"] = category if category in CATEGORIES else "その他"
            item["band"] = band if band in BANDS else "その他"
            item["artists"] = clean_artists(entry.get("artists"))
            item["japan"] = bool(entry.get("japan"))
            try:
                item["importance"] = max(1, min(5, int(entry.get("importance", 3))))
            except (TypeError, ValueError):
                item["importance"] = 3
            results.append(item)
    return results


def to_public(item: dict) -> dict:
    """サイトに出す形に整える。原文の抜粋は公開データに残さない。"""
    return {key: value for key, value in item.items() if key not in ("excerpt", "from_google")}


# --------------------------------------------------------------------------
# 記事ごとの日本語解説（詳細ページ）
# --------------------------------------------------------------------------

BLOCK_TAGS_RE = re.compile(
    r"(?is)<(script|style|noscript|svg|iframe|form|nav|aside|header|footer|figcaption)[^>]*>.*?</\1>"
)
ARTICLE_BLOCK_RE = re.compile(r"(?is)<article[^>]*>(.*?)</article>")
PARAGRAPH_RE = re.compile(r"(?is)<p[^>]*>(.*?)</p>")


def fetch_article_text(url: str) -> str:
    """記事ページから本文の段落だけを取り出す。解説を書くための材料にする。"""
    try:
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(request, timeout=20) as response:
            raw = response.read(600_000).decode("utf-8", errors="ignore")
    except Exception:  # noqa: BLE001
        return ""

    body = BLOCK_TAGS_RE.sub(" ", raw)
    # <article> があれば本文はその中。無ければページ全体から拾う。
    block = ARTICLE_BLOCK_RE.search(body)
    scope = block.group(1) if block else body

    paragraphs = []
    for chunk in PARAGRAPH_RE.findall(scope):
        text = strip_html(chunk)
        # ナビゲーションや広告の短い断片を落とす。
        if len(text) >= 40:
            paragraphs.append(text)
    return "\n".join(paragraphs)[:6000]


DETAIL_PROMPT = """あなたは Green Day とパンク／オルタナ周辺のバンドを追う日本語メディアの編集者です。
記事の原文を渡すので、日本の読者が原文を読まなくても内容が分かる日本語の解説を書いてください。
原文が英語でも、解説はすべて日本語で書きます。

厳守すること:
- 原文を逐語訳しない。事実を自分の言葉で整理し直して書く。
- 原文に書かれていない事実・数値・日付・会場名・曲名を足さない。分からないことは書かない。
- 歌詞や発言をそのまま長く引用しない。発言は要旨を日本語でまとめる。
- 海外の価格や日程は原文の表記のまま書く（勝手に円換算・日本時間換算をしない）。
- points は3〜5個の箇条書き。1つ40文字以内。記事の要点だけを並べる。
- body は800〜1200文字。2〜4段落に分け、段落の区切りは改行2つ。見出しや箇条書きは入れない。
- バンド名・アルバム名・曲名は英語の原表記のままでよい。
- 噂や観測記事は「〜と報じられている」「〜とされる」と伝聞であることを必ず示す。
- 「この記事では」「筆者は」のようなメタな言い回しを使わない。
- 出力はJSONオブジェクトのみ。前置き・説明・コードフェンスを付けない。

出力形式:
{{"points": ["...", "..."], "body": "..."}}

記事の見出し: {title}
出典: {source}（{lang}）
原文:
{text}
"""


def parse_detail_json(text: str) -> dict:
    cleaned = re.sub(r"^```(?:json)?\s*|\s*```$", "", text.strip(), flags=re.MULTILINE).strip()
    start, end = cleaned.find("{"), cleaned.rfind("}")
    if start == -1 or end == -1:
        raise llm_providers.ResponseInvalid("JSONオブジェクトが見つかりません")
    try:
        data = json.loads(cleaned[start : end + 1])
    except json.JSONDecodeError as exc:
        raise llm_providers.ResponseInvalid(f"JSONとして読めません: {exc}") from exc
    points = data.get("points")
    body = str(data.get("body", "")).strip()
    if not isinstance(points, list) or not 2 <= len(points) <= 6:
        raise llm_providers.ResponseInvalid("points が3〜5個ではありません")
    if len(body) < 300:
        raise llm_providers.ResponseInvalid(f"body が短すぎます（{len(body)}文字）")
    return {"points": [str(p).strip() for p in points if str(p).strip()], "body": body}


def build_detail(item: dict) -> dict | None:
    """1記事ぶんの解説を作る。原文が取れなければ作らない（要約だけ表示する）。"""
    text = fetch_article_text(item["url"])
    if len(text) < 400:
        return None
    prompt = DETAIL_PROMPT.format(
        title=item["title_original"],
        source=item["source"],
        lang="英語" if item["lang"] == "en" else "日本語",
        text=text,
    )
    try:
        raw = llm_providers.generate_text(prompt, validate=parse_detail_json)
    except llm_providers.LLMError as exc:
        print(f"  × 解説の生成に失敗（次回に回します）: {item['title_ja']} / {exc}")
        return None
    detail = parse_detail_json(raw)
    detail["chars"] = len(detail["body"])
    return detail


def write_detail_file(item: dict, detail: dict) -> None:
    os.makedirs(DETAIL_DIR, exist_ok=True)
    payload = {
        "id": item["id"],
        "title_ja": item["title_ja"],
        "summary_ja": item["summary_ja"],
        "points": detail["points"],
        "body": detail["body"],
        "source": item["source"],
        "url": item["url"],
        "lang": item["lang"],
        "region": item["region"],
        "band": item.get("band", "その他"),
        "artists": item.get("artists", []),
        "japan": bool(item.get("japan")),
        "category": item["category"],
        "importance": item["importance"],
        "image": item.get("image", ""),
        "published": item["published"],
    }
    with open(os.path.join(DETAIL_DIR, f"{item['id']}.json"), "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=1)
        f.write("\n")


# 本文が取れない記事（有料会員向け・JavaScript頼みのページ）は何度やっても取れない。
# この回数だけ試して駄目なら、その記事は要約だけで載せる。
MAX_DETAIL_TRIES = 2


def needs_detail(item: dict) -> bool:
    return not item.get("has_detail") and item.get("detail_tries", 0) < MAX_DETAIL_TRIES


def generate_details(new_items: list[dict], existing_items: list[dict]) -> None:
    """新着から順に解説を作る。英語の記事を先に回し、枠が余ったら古い記事を埋める。"""
    targets = [item for item in new_items if needs_detail(item)]
    # 英語の記事は日本語の解説が無いと読めないので、先に枠を使う。
    targets.sort(key=lambda item: 0 if item["lang"] == "en" else 1)
    if len(targets) < MAX_DETAILS_PER_RUN:
        # existing_items には new_items も含まれるので、二重に処理しないよう除く。
        queued = {item["id"] for item in targets}
        backlog = [
            item
            for item in existing_items
            if item["id"] not in queued
            and needs_detail(item)
            and not os.path.exists(os.path.join(DETAIL_DIR, f"{item['id']}.json"))
        ]
        backlog.sort(key=lambda item: 0 if item["lang"] == "en" else 1)
        targets += backlog[: MAX_DETAILS_PER_RUN - len(targets)]
    targets = targets[:MAX_DETAILS_PER_RUN]
    if not targets:
        return

    print(f"■ 日本語の解説を生成（{len(targets)}件）")
    done = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=DETAIL_WORKERS) as pool:
        for item, detail in zip(targets, pool.map(build_detail, targets)):
            if detail is None:
                item["detail_tries"] = item.get("detail_tries", 0) + 1
                continue
            item.pop("detail_tries", None)
            write_detail_file(item, detail)
            item["has_detail"] = True
            done += 1
            print(f"  ○ {detail['chars']}字 {item['title_ja']}")
    print(f"  {done}/{len(targets)}件を作成")


def cleanup_details(kept_ids: set[str]) -> None:
    """一覧から消えた記事の解説ファイルを片付ける。"""
    if not os.path.isdir(DETAIL_DIR):
        return
    removed = 0
    for name in os.listdir(DETAIL_DIR):
        if name.endswith(".json") and name[:-5] not in kept_ids:
            os.remove(os.path.join(DETAIL_DIR, name))
            removed += 1
    if removed:
        print(f"  古い解説ファイルを{removed}件削除")


# --------------------------------------------------------------------------
# 保存
# --------------------------------------------------------------------------

def load_skipped() -> dict[str, str]:
    """前回までに見送った記事のID。値は見送った日時（古いものは捨てる）。"""
    try:
        with open(SKIPPED_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}
    cutoff = dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=SKIP_MEMORY_DAYS)
    return {
        key: value
        for key, value in data.get("ids", {}).items()
        if (parse_date(value) or cutoff) >= cutoff
    }


def save_skipped(skipped: dict[str, str]) -> None:
    with open(SKIPPED_PATH, "w", encoding="utf-8") as f:
        json.dump({"ids": skipped}, f, ensure_ascii=False, indent=0)
        f.write("\n")


def load_existing() -> dict:
    if not os.path.exists(OUTPUT_PATH):
        return {"updated_at": None, "items": []}
    try:
        with open(OUTPUT_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError):
        return {"updated_at": None, "items": []}
    data.setdefault("items", [])
    return data


def main() -> int:
    load_env()

    with open(FEEDS_PATH, encoding="utf-8") as f:
        feeds = [feed for feed in json.load(f)["feeds"] if feed.get("enabled", True)]

    print(f"■ RSS取得（{len(feeds)}本）")
    fetched = collect_feed_items(feeds)
    print(f"  合計 {len(fetched)}件")

    existing = load_existing()
    existing_items = existing["items"]
    skipped = load_skipped()
    known_ids = {item["id"] for item in existing_items}
    known_urls = {canonical_url(item["url"]) for item in existing_items}
    known_titles = [normalize_title(item.get("title_original", "")) for item in existing_items]

    now = dt.datetime.now(dt.timezone.utc)
    cutoff = now - dt.timedelta(days=INTAKE_DAYS)

    # 日本語の記事を先に見ることで、同じ話題が海外からも流れてきたときに
    # 読者が読みやすい国内媒体のほうを残す。
    fetched.sort(key=lambda item: item["published"], reverse=True)
    fetched.sort(key=lambda item: 0 if item["lang"] == "ja" else 1)  # 安定ソート

    new_items: list[dict] = []
    for item in fetched:
        published = parse_date(item["published"])
        if published is None or published < cutoff or published > now + dt.timedelta(hours=12):
            continue
        if item["id"] in known_ids or item["url"] in known_urls:
            continue
        if item["id"] in skipped:  # 前回までに見送った記事
            continue
        if is_duplicate(item["title_original"], known_titles):
            continue
        known_ids.add(item["id"])
        known_urls.add(item["url"])
        known_titles.append(normalize_title(item["title_original"]))
        new_items.append(item)

    new_items.sort(key=lambda item: item["published"], reverse=True)

    print(f"■ 新着 {len(new_items)}件（重複と期間外を除外）")
    if len(new_items) > MAX_NEW_PER_RUN:
        print(f"  うち{MAX_NEW_PER_RUN}件を今回処理（残りは次回）")
        # Green Day 本体の枠を先に確保する。
        # これが無いと、記事数の多い周辺バンドで枠が埋まる。
        core = [item for item in new_items if mentions_band(item["title_original"])
                and fold(CORE_BAND) in fold(item["title_original"])][:CORE_QUOTA]
        taken = {item["id"] for item in core}
        rest = [item for item in new_items if item["id"] not in taken]
        new_items = core + rest[: MAX_NEW_PER_RUN - len(core)]
        new_items.sort(key=lambda item: item["published"], reverse=True)

    if new_items:
        # 日本語化にはLLMの枠を使うので、その前に捨てられるものは捨てておく。
        # 転送URLを元の記事URLに戻すと、歌詞ページや他フィードとの重複が見えるようになる。
        resolve_google_urls(new_items)
        stamp = dt.datetime.now(dt.timezone.utc).isoformat()
        screened: list[dict] = []
        for item in new_items:
            if BLOCK_URL_RE.search(item["url"]) or blocked_domain(item["url"]):
                print(f"  ・ニュースではないページのため除外: {item['title_original']}")
                skipped[item["id"]] = stamp
                continue
            if item["url"] in known_urls:  # 別のフィードから同じ記事が来ていた
                skipped[item["id"]] = stamp
                continue
            known_urls.add(item["url"])
            screened.append(item)
        # ページに書かれた公開日を見て、古い記事を落とす（同時にサムネイルも取る）。
        new_items = inspect_pages(screened, skipped)

    enriched: list[dict] = []
    replaced: set[str] = set()
    if new_items:
        enriched = enrich(new_items, skipped)
        print(f"  日本語化 {len(enriched)}件（無関係・ランキング記事と判定された分は除外）")
        enriched, replaced = dedupe_stories(enriched, existing_items)
        print(f"  掲載対象 {len(enriched)}件")

    # 既に載っている記事にも、あとから足した出典名の変換とブロックを後追いで効かせる。
    kept_existing = [
        {
            **item,
            "source": DOMAIN_NAMES.get(item["source"], item["source"]),
            # あとから足した画像の除外条件を、既に載っている記事にも効かせる。
            # 空にしておけば下のサムネイル補完で取り直される。
            "image": usable_image(item.get("image", ""), item["url"]),
        }
        for item in existing_items
        if item["id"] not in replaced
        and item.get("category") in CATEGORIES
        and not any(blocked in item["source"] for blocked in BLOCK_SOURCES)
        and not BLOCK_URL_RE.search(item["url"])
        and not blocked_domain(item["url"])
    ]

    merged = enriched + kept_existing
    merged = [
        item
        for item in merged
        if (parse_date(item.get("published", "")) or now) >= now - dt.timedelta(days=KEEP_DAYS)
    ]
    merged.sort(key=lambda item: item["published"], reverse=True)
    merged = merged[:KEEP_MAX]
    merged = enforce_band_day_cap(merged, skipped)
    # 上限で落ちた新着には解説を作らない（作っても一覧に出ないので無駄になる）。
    kept_ids = {item["id"] for item in merged}
    enriched = [item for item in enriched if item["id"] in kept_ids]

    # 以前の実行で画像が付かなかった記事を、少しずつ埋めていく。
    stale = [item for item in merged if not item.get("image")][:BACKFILL_PER_RUN]
    if stale:
        print("■ 既存記事のサムネイル補完")
        resolve_google_urls(stale)
        fill_missing_images(stale)

    generate_details(enriched, merged)
    cleanup_details({item["id"] for item in merged})

    merged = [to_public(item) for item in merged]

    payload = {
        "updated_at": now.astimezone(JST).isoformat(),
        "categories": CATEGORIES,
        # 画面のチップは、実際に記事があるバンドだけ出す。
        "bands": [b for b in BANDS if any(item.get("band") == b for item in merged)],
        "sources": sorted({item["source"] for item in merged}),
        "count": len(merged),
        "detail_count": sum(1 for item in merged if item.get("has_detail")),
        "items": merged,
    }

    os.makedirs(os.path.dirname(OUTPUT_PATH), exist_ok=True)
    with open(OUTPUT_PATH, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=1)
        f.write("\n")

    save_skipped(skipped)

    print(f"■ 書き出し: {OUTPUT_PATH}（掲載 {len(merged)}件 / 解説 {payload['detail_count']}件）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
