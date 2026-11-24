"""Internal linking opportunities — select a client, optionally enter an anchor,
then click Find opportunities. Core-page discovery, crawling, GSC enrichment,
matching, audit, insights and workbook generation run together.

Core pages come from three signals: links in the main navigation, links in the
footer, and links that appear on most pages (site-wide menus whose markup is not
recognisable). You can add or remove core pages and give URL patterns such as
^/solutions/ in the app; those choices are kept for the client.

GitHub: commit app.py and requirements.txt; Streamlit entrypoint is app.py.
Python 3.11 or newer is recommended (set it in the Streamlit Cloud app settings).
One-time Secrets for Google sign-in on Streamlit Cloud:
    app_password = "a-private-password"
    google_client_secret_json = '<complete downloaded Web application JSON>'
    google_redirect_uri = 'https://YOUR-APP.streamlit.app/component/streamlit_oauth.authorize_button/index.html'
Register that exact redirect URI on the Google Cloud Web application client.
For desktop use, start with `streamlit run app.py -- --local` (or set the
operator environment variable INTERNAL_LINK_MODE=local). Only then can
google_client_secret_path point to a Desktop client JSON and Screaming Frog
run on that computer. Existing gsc_token_json credentials still work. On a
desktop behind a corporate proxy, also set INTERNAL_LINK_USE_PROXY=1.

Google credentials stay in memory and travel to a background worker through a
stdin pipe. Never commit credentials. Cloud mode uses a bounded HTML crawler;
local mode uses the installed Screaming Frog CLI when available. Saved crawl
results are reused for 24 hours unless Refresh is selected in the collapsed
connection/crawl drawer. Host storage can be reset on redeploy/reboot.
"""
from __future__ import annotations

import argparse
import copy
import gzip
import hashlib
import hmac
import ipaddress
import io
import json
import math
import os
import platform
import queue
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import unicodedata
import uuid
from collections import Counter, OrderedDict, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed, wait, FIRST_COMPLETED
from datetime import date, datetime, timedelta, timezone
from contextlib import contextmanager
from contextvars import ContextVar
from functools import lru_cache
from html import escape as html_escape
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit
from urllib.robotparser import RobotFileParser
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
from sklearn.feature_extraction.text import ENGLISH_STOP_WORDS
from filelock import FileLock

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("INTERNAL_LINK_DATA_DIR", str(APP_DIR / "data"))).expanduser().resolve()
APP_VERSION = "2.4.0"
INSIGHT_VERSION = "3"
CRAWL_SCHEMA = 3
GOOGLE_CREDENTIALS_INFO = None  # Worker memory only; never included in job JSON.
IS_WORKER = False
JSON_SNAPSHOT = ContextVar("internal_link_json_snapshot", default=None)
GOOGLE_CALLBACK_BASE = "/component/streamlit_oauth.authorize_button"
GOOGLE_CALLBACK_PATH = GOOGLE_CALLBACK_BASE + "/index.html"
GOOGLE_CALLBACK_PATHS = {GOOGLE_CALLBACK_BASE, GOOGLE_CALLBACK_BASE + "/", GOOGLE_CALLBACK_PATH}
GOOGLE_HTTP_TIMEOUT = 15
GOOGLE_DATA_TIMEOUT = 120
GOOGLE_CONNECT_TIMEOUT = 45
UA = "CadenceInternalLinks/1.0"
SCOPES = ["https://www.googleapis.com/auth/webmasters.readonly"]
GOOGLE_POPUP_HTML = r'''<!doctype html>
<html><head><meta charset="utf-8"><meta name="referrer" content="no-referrer">
<style>
body { margin:0; font:14px system-ui,sans-serif; }
button { width:100%; min-height:38px; border:1px solid #ff4b4b; border-radius:8px;
         background:#ff4b4b; color:white; font:inherit; cursor:pointer; }
button:disabled { opacity:.6; cursor:wait; }
#status { margin:7px 0 2px; font-size:12px; line-height:1.4; }
</style></head><body>
<button id="connect" type="button">Connect Google</button>
<p id="status" role="status" aria-live="polite"></p>
<script>
(() => {
  const button = document.getElementById("connect");
  const status = document.getElementById("status");
  let args = {}, timer = null;
  const send = (type, fields = {}) => window.parent.postMessage(
    {isStreamlitMessage:true, type, ...fields}, "*");
  const resize = () => send("streamlit:setFrameHeight", {height:Math.max(46, document.body.scrollHeight)});
  const value = data => send("streamlit:setComponentValue", {value:data, dataType:"json"});
  // Streamlit Cloud may canonicalize index.html to the component directory.
  // Accept that alias only at the exact expected origin and callback path.
  const canonicalPath = path => path.replace(/\/index\.html$/, "/").replace(/\/+$/, "");
  const finish = (data, message) => {
    if (timer !== null) window.clearInterval(timer);
    timer = null;
    button.disabled = false;
    status.textContent = message;
    resize();
    value(data);
  };
  window.addEventListener("message", event => {
    if (event.source !== window.parent || event.data?.type !== "streamlit:render") return;
    args = event.data.args || {};
    button.textContent = args.name || "Connect Google";
    if (timer === null) button.disabled = Boolean(event.data.disabled);
    if (event.data.theme) document.body.style.color = event.data.theme.textColor || "inherit";
    resize();
  });
  button.addEventListener("click", () => {
    if (timer !== null) return;
    let authorization, expected;
    try {
      authorization = new URL(args.authorization_url);
      expected = new URL(authorization.searchParams.get("redirect_uri"));
      if (authorization.origin !== "https://accounts.google.com") throw new Error("invalid provider");
    } catch (_) {
      finish({_ui_error:"invalid_connection"}, "Restart Google sign-in in the app.");
      return;
    }
    const popup = window.open(authorization.href, "googleSearchConsoleSignIn",
      "popup=yes,width=600,height=750");
    if (!popup) {
      finish({_ui_error:"popup_blocked"}, "Allow this site's popups, then click Connect Google again.");
      return;
    }
    try { popup.focus(); } catch (_) {}
    button.disabled = true;
    status.textContent = "Finish Google sign-in in the popup. Keep this app tab open.";
    resize();
    const started = Date.now();
    timer = window.setInterval(() => {
      if (Date.now() - started > 180000) {
        finish({_ui_error:"popup_timeout"}, "Google has not returned. Restart sign-in in the app.");
        return;
      }
      try {
        if (popup.closed) {
          finish({_ui_error:"popup_closed"}, "The sign-in popup closed before returning. Try again.");
          return;
        }
        const current = new URL(popup.location.href);
        if (current.origin !== expected.origin || canonicalPath(current.pathname) !== canonicalPath(expected.pathname)) return;
        const params = current.searchParams;
        if (!params.has("code") && !params.has("error")) return;
        const response = {};
        for (const name of ["code", "state", "error"]) {
          if (params.has(name)) response[name] = params.get(name);
        }
        popup.close();
        finish(response, "Google returned. Loading your client list…");
      } catch (error) {
        // Reading the popup is expected to fail while it is on Google's origin.
        if (error.name !== "SecurityError") {
          finish({_ui_error:"popup_unavailable"}, "The browser could not return sign-in to the app. Restart sign-in.");
        }
      }
    }, 500);
  });
  window.addEventListener("pagehide", () => { if (timer !== null) window.clearInterval(timer); });
  send("streamlit:componentReady", {apiVersion:1});
  resize();
})();
</script></body></html>'''
MODEL = "sentence-transformers/all-MiniLM-L6-v2"
STAGES = {
    "crawl": "Run Screaming Frog",
    "sitemaps": "Discover sitemap URLs",
    "gsc": "Download GSC data",
    "content": "Fetch / refresh page content",
    "recommendations": "Find contextual link opportunities",
    "audit": "Audit existing internal links",
}
AUDITS = {
    "orphans": "Potential orphan pages",
    "buried": "Buried / unreachable core pages",
    "support": "Core pages with weak contextual support",
    "anchors": "Vague / missing contextual anchors",
    "destinations": "Broken / redirected / non-indexable destinations",
    "canonicals": "Canonical tags that point to broken or redirecting URLs",
}
EMPTY_EXCLUSIONS = r"/(?:privacy(?:-policy)?|terms(?:-and-conditions)?|login|cart|checkout|account|search|tag|author)(?:/|$)"
TOKEN_RE = re.compile(r"[\w]+(?:[-’'][\w]+)*", re.UNICODE)
BAD_EDGE = set("a an the this that these those our your their its for to of in on at by with from and or but as is are was were be been being can could would should will may might how what why when where which who we you they it also more most very such into through than then have has had do does did using use used help helps improve improves including include includes provides provide offers offer".split())
GENERIC = set("company companies solution solutions service services product products information learn read more here click website page pages business businesses system systems tool tools technology technologies guide best good new support need needs help including provide provides offer offers".split())
GENERIC_ANCHORS = {"click here", "here", "read more", "learn more", "more", "this", "this page", "this link", "website", "link", "view more", "find out more", "details", "more information"}


class Cancelled(RuntimeError):
    pass


class DownloadTimeout(TimeoutError):
    """Our own whole-download deadline; never retried on another address."""


def deployment_mode():
    """Only the server operator can enable desktop executable access."""
    return "local" if os.environ.get("INTERNAL_LINK_MODE", "hosted").strip().lower() == "local" else "hosted"


class PreparedProfile(dict):
    """Runtime-only O(1) blog membership; JSON still contains an ordinary list."""
    @property
    def blog_urls_set(self):
        values = self.get("blog_urls", [])
        if getattr(self, "_blog_values", None) is not values or getattr(self, "_blog_length", -1) != len(values):
            self._blog_values, self._blog_length = values, len(values)
            self._blog_set = set(values)
        return self._blog_set


@contextmanager
def dataset_snapshot():
    """Reuse decoded inputs within one run only; never share session secrets."""
    token = JSON_SNAPSHOT.set({})
    try:
        yield
    finally:
        JSON_SNAPSHOT.reset(token)


def update_profiles(mutator):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    with FileLock(str(DATA_DIR / "profiles.guard"), timeout=10):
        # Copy before mutating so a cached decoded object is never changed in place.
        profiles = copy.deepcopy(read_json(DATA_DIR / "profiles.json", []))
        result = mutator(profiles)
        atomic_json(DATA_DIR / "profiles.json", profiles)
        return profiles if result is None else result


def utc_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def text_norm(value):
    return re.sub(r"\s+", " ", unicodedata.normalize("NFKC", str(value or ""))).strip()


def slug(value):
    return re.sub(r"[^a-z0-9_-]+", "-", str(value).lower()).strip("-")[:70] or "client"


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, default=str).encode()).hexdigest()


def progress_update(log, done, total, message):
    """Count real work when a total exists; do not invent crawl percentages."""
    if callable(getattr(log, "progress", None)):
        log.progress(int(done), int(total), message)
    else:
        log(message)


def atomic_json(path, value, private=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    try:
        with temp.open("w", encoding="utf-8") as handle:
            # Compact output: large crawl datasets are read on every run.
            json.dump(value, handle, ensure_ascii=False, separators=(",", ":"), allow_nan=False, default=str)
        if private:
            try:
                temp.chmod(0o600)
            except OSError:
                pass
        os.replace(temp, path)
        cache = JSON_SNAPSHOT.get()
        if cache is not None:
            for key in [key for key in cache if str(path) in key]:
                cache.pop(key, None)
    finally:
        temp.unlink(missing_ok=True)


def read_json(path, default=None):
    path = Path(path)
    try:
        stat = path.stat()
    except FileNotFoundError:
        return default
    cache = JSON_SNAPSHOT.get()
    key = (str(path), stat.st_mtime_ns, stat.st_size)
    if cache is not None and key in cache:
        return cache[key]
    with path.open(encoding="utf-8") as handle:
        value = json.load(handle)
    if cache is not None:
        cache[key] = value
    return value


def file_sha256(path):
    with Path(path).open("rb") as handle:
        if hasattr(hashlib, "file_digest"):
            return hashlib.file_digest(handle, "sha256").hexdigest()
        hasher = hashlib.sha256()
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            hasher.update(chunk)
        return hasher.hexdigest()


def read_job_lock():
    """Tolerate incomplete metadata left by older app versions/redeployments."""
    try:
        value = read_json(DATA_DIR / "jobs" / "queue.lock", {})
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError):
        return {}


def client_dir(profile):
    return DATA_DIR / "clients" / slug(profile["id"])


def save_dataset(profile, name, rows, **meta):
    atomic_json(client_dir(profile) / f"{name}.json", {"meta": {"created_at": utc_now(), "app_version": APP_VERSION, **meta}, "rows": rows})


def dataset(profile, name):
    return read_json(client_dir(profile) / f"{name}.json", {"meta": {}, "rows": []})


def input_signature(profile, names):
    stamps, cache = {}, JSON_SNAPSHOT.get()
    for name in names:
        path = client_dir(profile) / f"{name}.json"
        try:
            stat = path.stat()
        except FileNotFoundError:
            stamps[name] = None
            continue
        key = ("sha256", str(path), stat.st_mtime_ns, stat.st_size)
        if cache is not None and key in cache:
            stamps[name] = cache[key]
        else:
            stamps[name] = file_sha256(path)
            if cache is not None:
                cache[key] = stamps[name]
    return digest({"profile": profile, "datasets": stamps})


def prune_files(folder, pattern, keep=10):
    files = sorted(Path(folder).glob(pattern), key=lambda p: p.stat().st_mtime, reverse=True)
    for old in files[keep:]:
        try:
            old.unlink()
        except OSError:
            pass


def url_key(value):
    """Conservative identity: keep meaningful params, path case and trailing slash."""
    try:
        parts = urlsplit(str(value).strip())
        if parts.scheme.lower() not in {"http", "https"} or not parts.hostname or parts.username:
            return ""
        scheme = parts.scheme.lower()
        host = parts.hostname.lower().encode("idna").decode()
        if ":" in host:
            host = f"[{host}]"
        port = parts.port
        if port and not ((scheme == "https" and port == 443) or (scheme == "http" and port == 80)):
            host += f":{port}"
        params = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
                  if not k.lower().startswith("utm_") and k.lower() not in {"gclid", "fbclid", "msclkid", "dclid"}]
        return urlunsplit((scheme, host, parts.path or "/", urlencode(params, doseq=True), ""))
    except (ValueError, UnicodeError):
        return ""


def loose_key(value):
    """Same page despite http/https, www and trailing-slash differences (used for canonical checks)."""
    key = url_key(value)
    if not key:
        return ""
    parts = urlsplit(key)
    return parts.netloc.removeprefix("www.") + (parts.path.rstrip("/") or "/") + ("?" + parts.query if parts.query else "")


def site_hosts(profile):
    root = urlsplit(profile["root_url"]).hostname or ""
    return {root.lower(), *[x.strip().lower() for x in profile.get("allowed_hosts", []) if x.strip()]}


def same_site(url, profile):
    return bool(url_key(url)) and (urlsplit(url).hostname or "").lower() in site_hosts(profile)


def is_home(url, profile):
    return url_key(url) == url_key(profile["root_url"]) or urlsplit(url).path in {"", "/"}


ARCHIVE_PATH = re.compile(r"/(?:category|categories|product-category|tag|tags|author|authors|topics?)/|/page/\d+/?$", re.I)


def is_archive(url):
    """Category/tag/author listings and paginated pages: not editable article copy."""
    path = urlsplit(url).path or "/"
    leaf = path.strip("/").split("/")[-1].lower()
    return bool(ARCHIVE_PATH.search(path)) or leaf in {"blog", "blogs", "news", "articles", "insights"}


def blog_by_path(url, profile):
    path = urlsplit(url).path
    leaf = path.strip("/").split("/")[-1].lower()
    if leaf in {"blog", "blogs", "resources", "articles", "insights", "news"}:
        return False
    if re.search(r"/(?:tag|tags|author|authors|category|categories|page)/", path, re.I):
        return False
    return bool(re.search(profile.get("blog_pattern", r"/(blog|resources|articles|insights)/"), path, re.I))


def is_blog(url, profile):
    known = profile.blog_urls_set if isinstance(profile, PreparedProfile) else profile.get("blog_urls", [])
    if url_key(url) in known:
        return True
    return blog_by_path(url, profile)


def excluded(url, profile):
    return bool(profile.get("exclude_pattern") and re.search(profile["exclude_pattern"], urlsplit(url).path, re.I))


def phrase_pattern(phrase):
    words = text_norm(phrase).split()
    return re.compile(r"(?<!\w)" + r"\s+".join(re.escape(x) for x in words) + r"(?!\w)", re.I) if words else re.compile(r"(?!)")


@lru_cache(maxsize=256)
def _brand_regex(terms):
    body = "|".join(r"\s+".join(re.escape(w) for w in term.split()) for term in sorted(terms, key=len, reverse=True))
    return re.compile(r"(?<!\w)(?:" + body + r")(?!\w)", re.I) if body else re.compile(r"(?!)")


def brand_pattern(profile):
    return _brand_regex(tuple(sorted({text_norm(x) for x in profile.get("brand_terms", []) if text_norm(x)})))


def without_brand(value, profile):
    return text_norm(brand_pattern(profile).sub(" ", text_norm(value)))


def default_profile(name, root, prop=""):
    host = urlsplit(root).hostname or ""
    bare = host.removeprefix("www.")
    return {
        "id": slug(name) + "-" + uuid.uuid4().hex[:6], "name": name, "root_url": url_key(root),
        "gsc_property": prop, "brand_terms": [bare.split(".")[0]], "brands_confirmed": False,
        "allowed_hosts": ["www." + bare, bare], "blog_pattern": r"/(blog|blogs|resources|articles|insights|news)/",
        "exclude_pattern": EMPTY_EXCLUSIONS, "main_selector": "", "core_pages": [],
        "core_patterns": [], "core_excluded": [], "sf_config": "", "sitemap_urls": [],
    }


def validate_profile(profile):
    if not url_key(profile.get("root_url", "")):
        raise ValueError("Enter a complete http(s) crawl URL.")
    for name in ["blog_pattern", "exclude_pattern"]:
        try:
            re.compile(profile.get(name, ""))
        except re.error as exc:
            raise ValueError(f"Invalid {name}: {exc}") from exc
    for pattern in profile.get("core_patterns", []):
        try:
            re.compile(pattern)
        except re.error as exc:
            raise ValueError(f"Invalid core page pattern {pattern!r}: {exc}") from exc
    if profile.get("main_selector"):
        from bs4 import BeautifulSoup
        BeautifulSoup("<main></main>", "lxml").select(profile["main_selector"])
    for core in profile.get("core_pages", []):
        if not same_site(core["url"], profile):
            raise ValueError(f"Core page is outside the allowed hosts: {core['url']}")


def aliases_for(pages, profile):
    """Redirects, plus canonical tags that point at a verified live page."""
    mapping = {}
    for p in pages:
        url = url_key(p["url"])
        redirect = url_key(p.get("redirect", ""))
        canonical = url_key(p.get("canonical", ""))
        if 300 <= int(p.get("status") or 0) < 400 and same_site(redirect, profile):
            mapping[url] = redirect
        elif ("canonical" in str(p.get("indexability_status", "")).lower() and not p.get("indexable") and not p.get("invalid_canonical")
              and same_site(canonical, profile) and loose_key(canonical) != loose_key(url)):
            mapping[url] = canonical
    return mapping


def resolve_alias(url, mapping):
    value = url_key(url)
    seen = set()
    while value in mapping and value not in seen:
        seen.add(value)
        value = mapping[value]
    return value


def normalize_canonicals(pages, profile):
    """Ignore canonical tags whose target is missing, broken, redirecting or points back.

    WordPress sites can emit canonicals such as /solutions__trashed/page/. Trusting
    them would mark real pages non-indexable. Such pages stay indexable and are
    reported as 'invalid canonical'. Returns the number of invalid canonicals.
    """
    by_url = {p["url"]: p for p in pages}
    by_loose = {}
    for p in pages:
        by_loose.setdefault(loose_key(p["url"]), p)

    def lookup(url):
        return by_url.get(url_key(url)) or by_loose.get(loose_key(url))

    invalid = 0
    for p in pages:
        if p.get("status") != 200 or not p.get("html"):
            continue
        canonical = url_key(p.get("canonical", ""))
        noindex = bool(p.get("noindex")) or "noindex" in str(p.get("indexability_status", "")).lower()
        if not canonical or loose_key(canonical) == loose_key(p["url"]):
            if not noindex and "canonical" in str(p.get("indexability_status", "")).lower():
                p["indexable"], p["indexability_status"] = True, ""
            continue
        if not same_site(canonical, profile):
            continue  # Cross-domain canonical: respect it.
        target, hops, reason = lookup(canonical), 0, ""
        while target is not None and 300 <= int(target.get("status") or 0) < 400 and target.get("redirect") and hops < 5:
            target, hops = lookup(target["redirect"]), hops + 1
        if target is None:
            p["canonical_unverified"] = True  # Not crawled: keep Google's likely interpretation.
            continue
        target_noindex = bool(target.get("noindex")) or "noindex" in str(target.get("indexability_status", "")).lower()
        if loose_key(target["url"]) == loose_key(p["url"]):
            reason = "redirects back to this page"
        elif target.get("status") != 200:
            reason = f"returns HTTP {target.get('status') or 'no response'}"
        elif not target.get("html"):
            reason = "is not an HTML page"
        elif target_noindex:
            reason = "is noindex"
        if reason:
            invalid += 1
            p["invalid_canonical"] = canonical
            p["indexable"] = not noindex
            p["indexability_status"] = "noindex" if noindex else f"Invalid canonical: target {reason}"
        elif hops:
            p["canonical"] = target["url"]
    return invalid


def frame_rows(df):
    # pandas serializes NaN/Infinity as JSON null without mutating object columns.
    return json.loads(df.to_json(orient="records", force_ascii=False))


def read_sf_csv(source):
    raw = source.read() if hasattr(source, "read") else Path(source).read_bytes()
    if isinstance(raw, str):
        raw = raw.encode()
    for encoding in ["utf-8-sig", "utf-16", "cp1252"]:
        try:
            decoded = raw.decode(encoding)
            # SF exports can be preceded by an extra descriptive line.
            lines = decoded.splitlines()
            header = next((i for i, line in enumerate(lines[:6]) if re.search(r"Address|Source", line, re.I)), 0)
            return pd.read_csv(io.StringIO("\n".join(lines[header:])), sep=None, engine="python", keep_default_na=False)
        except (UnicodeError, ValueError, pd.errors.ParserError):
            continue
    raise ValueError("Could not read this Screaming Frog CSV. Export CSV with its header row.")


def sf_column(df, *names):
    columns = {re.sub(r"[^a-z0-9]", "", str(c).lower()): c for c in df.columns}
    return next((columns[re.sub(r"[^a-z0-9]", "", n.lower())] for n in names if re.sub(r"[^a-z0-9]", "", n.lower()) in columns), None)


def sf_tables(internal_df, inlinks_df, profile):
    address = sf_column(internal_df, "Address", "URL")
    if not address:
        raise ValueError("Internal CSV requires an Address column.")
    field_map = {"status": ("Status Code",), "content_type": ("Content Type", "Content"),
                 "title": ("Title 1", "Title"), "h1": ("H1-1", "H1 1", "H1"),
                 "canonical": ("Canonical Link Element 1", "Canonical Link Element", "Canonical"),
                 "redirect": ("Redirect URL",), "indexability": ("Indexability",),
                 "indexability_status": ("Indexability Status",), "sf_depth": ("Crawl Depth",),
                 "sf_link_score": ("Link Score",), "meta_robots": ("Meta Robots 1", "Meta Robots"),
                 "x_robots": ("X-Robots-Tag 1", "X-Robots-Tag",)}
    fields = {k: sf_column(internal_df, *v) for k, v in field_map.items()}
    if not fields["status"] or not fields["indexability"] or not fields["content_type"]:
        raise ValueError("Internal:All must include Status Code, Content/Content Type and Indexability.")
    pages = {}
    for raw in internal_df.to_dict("records"):
        url = url_key(raw[address])
        if not same_site(url, profile):
            continue
        row = {key: str(raw.get(col, "")) if col else "" for key, col in fields.items()}
        row["url"] = url
        row["status"] = int(float(row["status"])) if re.fullmatch(r"\d+(?:\.0+)?", row["status"]) else 0
        row["indexable"] = row.pop("indexability").strip().lower() == "indexable"
        row["html"] = "html" in row["content_type"].lower()
        row["canonical"] = url_key(urljoin(url, row["canonical"])) if row["canonical"] else ""
        row["redirect"] = url_key(urljoin(url, row["redirect"])) if row["redirect"] else ""
        robots = row["meta_robots"] + " " + row["x_robots"]
        row["noindex"] = bool(re.search(r"\b(?:noindex|none)\b", robots, re.I))
        row["source_nofollow"] = bool(re.search(r"\b(?:nofollow|none)\b", robots, re.I))
        pages[url] = row
    src = sf_column(inlinks_df, "Source")
    dst = sf_column(inlinks_df, "Destination")
    if not src or not dst:
        raise ValueError("All Inlinks CSV requires Source and Destination columns. Link checks cannot run without it.")
    link_fields = {"type": sf_column(inlinks_df, "Type"), "anchor": sf_column(inlinks_df, "Anchor", "Anchor Text"),
                   "position": sf_column(inlinks_df, "Link Position", "Position"), "follow": sf_column(inlinks_df, "Follow"),
                   "rel": sf_column(inlinks_df, "Rel"), "alt": sf_column(inlinks_df, "Alt Text", "Alt"),
                   "locator": sf_column(inlinks_df, "Link Path", "XPath")}
    links, seen = [], set()
    for raw in inlinks_df.to_dict("records"):
        link = {key: str(raw.get(col, "")) if col else "" for key, col in link_fields.items()}
        if link["type"] and "hyperlink" not in link["type"].lower():
            continue
        source = url_key(raw[src])
        destination = url_key(urljoin(source, str(raw[dst])))
        if not same_site(source, profile) or not same_site(destination, profile):
            continue
        link.update(source=source, destination=destination)
        link["followable"] = link["follow"].lower() not in {"false", "0", "no", "nofollow"} and not re.search(r"\bnofollow\b", link["rel"], re.I)
        link["followable"] = bool(link["followable"] and not pages.get(source, {}).get("source_nofollow"))
        position = link["position"].strip().lower()
        link["contextual"] = position in {"content", "main content", "body content", "main"}
        link["position_known"] = bool(position and position not in {"unknown", "nan", "none"})
        key = (source, destination, link["anchor"], link["position"], link["locator"])
        if key not in seen:
            links.append(link)
            seen.add(key)
    page_list = list(pages.values())
    invalid = normalize_canonicals(page_list, profile)
    warnings = [] if link_fields["position"] else ["Link Position is missing. Contextual counts are unknown and existing hyperlink pairs are conservatively excluded from new recommendations."]
    if invalid:
        warnings.append(f"{invalid} page(s) have canonical tags pointing to broken or redirecting URLs; they are treated as indexable and listed in Existing-link issues.")
    meta = {"links_verified": True, "position_available": bool(link_fields["position"]), "warnings": warnings}
    return page_list, links, meta


def save_crawl(profile, internal_df, inlinks_df, source, **extras):
    pages, links, meta = sf_tables(internal_df, inlinks_df, profile)
    generation = uuid.uuid4().hex
    save_dataset(profile, "pages", pages, generation=generation, source=source, crawl_schema=CRAWL_SCHEMA, **extras)
    save_dataset(profile, "links", links, generation=generation, source=source, crawl_schema=CRAWL_SCHEMA, **meta, **extras)
    return len(pages), len(links)


def find_sf(override=""):
    candidates = [override] if override else []
    if platform.system() == "Windows":
        for env_name in ["ProgramFiles", "ProgramFiles(x86)"]:
            base = os.environ.get(env_name, r"C:\Program Files")
            candidates.append(str(Path(base) / "Screaming Frog SEO Spider" / "ScreamingFrogSEOSpiderCli.exe"))
    elif platform.system() == "Darwin":
        candidates.append("/Applications/Screaming Frog SEO Spider.app/Contents/MacOS/ScreamingFrogSEOSpiderLauncher")
    for name in ["screamingfrogseospider", "ScreamingFrogSEOSpiderCli.exe"]:
        found = shutil.which(name)
        if found:
            candidates.append(found)
    for candidate in candidates:
        if candidate and Path(candidate).is_file():
            return str(Path(candidate).resolve())
    raise FileNotFoundError("Screaming Frog CLI was not found. Set its executable path under Connection & crawl options.")


def run_sf(profile, options, log, check_cancel):
    if deployment_mode() != "local":
        raise ValueError("Desktop Screaming Frog can only be launched in Local computer mode on that computer. In Streamlit Cloud, import its CSV exports.")
    if profile.get("demo"):
        raise ValueError("The demo uses synthetic local data. Select a real client for live crawling.")
    output = client_dir(profile) / "crawls" / (datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:6])
    output.mkdir(parents=True, exist_ok=True)
    cmd = [find_sf(options.get("sf_path", "")), "--crawl", profile["root_url"], "--headless", "--save-crawl",
           "--output-folder", str(output), "--export-format", "csv", "--export-tabs", "Internal:All", "--bulk-export", "Links:All Inlinks"]
    if profile.get("sf_config"):
        config = Path(profile["sf_config"]).expanduser()
        if not config.is_file():
            raise FileNotFoundError("The saved Screaming Frog configuration does not exist.")
        cmd += ["--config", str(config.resolve())]
    with (output / "sf.log").open("w", encoding="utf-8") as stdout:
        process = subprocess.Popen(cmd, stdout=stdout, stderr=subprocess.STDOUT, shell=False)
        try:
            started = time.monotonic()
            last_report = 0
            while process.poll() is None:
                check_cancel()
                if time.monotonic() - started > int(options.get("crawl_timeout_minutes", 180)) * 60:
                    raise TimeoutError("Crawl exceeded the configured timeout. See the crawl log.")
                if time.monotonic() - last_report > 2:
                    last_report = time.monotonic()
                    with (output / "sf.log").open("rb") as running_log:
                        running_log.seek(0, 2)
                        running_log.seek(max(0, running_log.tell() - 4000))
                        tail = running_log.read().decode("utf-8", errors="replace")
                    crawl_lines = "\n".join(line for line in tail.splitlines() if re.search(r"crawl|complete", line, re.I))
                    percentages = re.findall(r"(\d+(?:\.\d+)?)\s*%", crawl_lines)
                    detail = tail.strip().splitlines()[-1] if tail.strip() else f"Screaming Frog is running ({int(time.monotonic() - started)} seconds)."
                    progress_update(log, min(100, int(float(percentages[-1]))) if percentages else 0, 100 if percentages else 0, detail[-300:])
                time.sleep(0.5)
        except BaseException:
            process.terminate()
            try:
                process.wait(timeout=15)
            except subprocess.TimeoutExpired:
                process.kill()
            raise
    if process.returncode:
        tail = (output / "sf.log").read_text(encoding="utf-8", errors="replace")[-4000:]
        raise RuntimeError(f"Screaming Frog exited with code {process.returncode}. {tail}")
    internal, inlinks = None, None
    for path in output.rglob("*.csv"):
        try:
            sample = read_sf_csv(path)
            if sf_column(sample, "Address") and sf_column(sample, "Indexability"):
                internal = sample
            elif sf_column(sample, "Source") and sf_column(sample, "Destination"):
                inlinks = sample
        except (ValueError, pd.errors.ParserError):
            continue
    if internal is None or inlinks is None:
        raise RuntimeError("Required Internal:All and Links:All Inlinks exports were not found. Check the SF log and saved crawl configuration.")
    counts = save_crawl(profile, internal, inlinks, "Screaming Frog CLI", crawl_directory=str(output), root=profile["root_url"])
    log(f"Imported {counts[0]:,} pages and {counts[1]:,} hyperlink records.")


def validate_public_url(url):
    """Return the approved numeric addresses used by the actual connection."""
    parts = urlsplit(url)
    if parts.scheme not in {"http", "https"} or not parts.hostname or parts.username or parts.password or "%" in parts.hostname:
        raise ValueError("Enter a public http(s) website URL.")
    try:
        literal = ipaddress.ip_address(parts.hostname)
        addresses = [literal]
    except ValueError:
        try:
            host = parts.hostname.encode("idna").decode()
            addresses = list(dict.fromkeys(ipaddress.ip_address(info[4][0]) for info in
                         socket.getaddrinfo(host, parts.port or (443 if parts.scheme == "https" else 80), type=socket.SOCK_STREAM)))
        except (OSError, UnicodeError) as exc:
            raise ValueError("The website's public address could not be resolved.") from exc
    allow_private = deployment_mode() == "local" and os.environ.get("INTERNAL_LINK_ALLOW_PRIVATE") == "1"
    if not addresses or (not allow_private and any(not address.is_global or
            (getattr(address, "ipv4_mapped", None) and not address.ipv4_mapped.is_global) for address in addresses)):
        raise ValueError("Only public websites can be crawled; private and local network addresses are blocked.")
    return [str(a) for a in addresses]


_POOLS = OrderedDict()
_POOL_LOCK = threading.Lock()


def _connection_pool(scheme, address, port, hostname):
    """Keep-alive pools pinned to one validated address and TLS hostname."""
    import requests
    import urllib3
    key = (scheme, address, port, hostname)
    with _POOL_LOCK:
        pool = _POOLS.get(key)
        if pool is not None:
            _POOLS.move_to_end(key)
            return pool
        kwargs = {"port": port, "timeout": urllib3.Timeout(connect=10, read=35), "retries": False, "maxsize": 4}
        if scheme == "https":
            pool = urllib3.HTTPSConnectionPool(address, server_hostname=hostname, assert_hostname=hostname,
                                               cert_reqs="CERT_REQUIRED", ca_certs=requests.certs.where(), **kwargs)
        else:
            pool = urllib3.HTTPConnectionPool(address, **kwargs)
        _POOLS[key] = pool
        while len(_POOLS) > 48:
            _, old = _POOLS.popitem(last=False)
            old.close()
        return pool


def _read_limited(chunks, max_bytes):
    data, deadline = bytearray(), time.monotonic() + 120
    for part in chunks:
        data.extend(part)
        if len(data) > max_bytes:
            raise ValueError(f"Response exceeded the {max_bytes:,}-byte limit.")
        if time.monotonic() > deadline:
            raise DownloadTimeout("Website response exceeded the download time limit.")
    return bytes(data)


def _get_bytes_with_proxy(url, max_bytes):
    """Desktop-only path for corporate proxies (INTERNAL_LINK_USE_PROXY=1)."""
    import requests
    current, first_redirect = url_key(url), None
    for _ in range(7):
        validate_public_url(current)
        with requests.get(current, headers={"User-Agent": UA}, timeout=(10, 35), allow_redirects=False, stream=True) as response:
            headers = {k.lower(): v for k, v in response.headers.items()}
            if response.status_code in {301, 302, 303, 307, 308} and headers.get("location"):
                first_redirect = first_redirect or response.status_code
                current = url_key(urljoin(current, headers["location"]))
                continue
            data = _read_limited(response.iter_content(65536), max_bytes)
            if first_redirect:
                headers["__redirect_status__"] = str(first_redirect)
            return response.status_code, headers, current, data
    raise ValueError("The website returned too many redirects.")


def get_bytes(url, max_bytes=5_000_000):
    """Pin each hop to validated IPs, retaining TLS hostname checks and SNI.

    Direct urllib3 pools deliberately do not inherit environment HTTP proxies.
    A second DNS lookup of the untrusted hostname cannot change the peer.
    """
    import requests
    import urllib3
    if deployment_mode() == "local" and os.environ.get("INTERNAL_LINK_USE_PROXY") == "1":
        return _get_bytes_with_proxy(url, max_bytes)
    current, first_redirect = url_key(url), None
    for _ in range(7):
        addresses = validate_public_url(current)
        parts = urlsplit(current)
        hostname = parts.hostname.encode("idna").decode()
        host_header = f"[{hostname}]" if ":" in hostname else hostname
        default_port = 443 if parts.scheme == "https" else 80
        if parts.port and parts.port != default_port:
            host_header += f":{parts.port}"
        target = requests.utils.requote_uri(urlunsplit(("", "", parts.path or "/", parts.query, "")))
        last_error = None
        for address in addresses[:4]:
            pool = _connection_pool(parts.scheme, address, parts.port or default_port, hostname)
            response, reusable = None, False
            try:
                response = pool.urlopen("GET", target, headers={"Host": host_header, "User-Agent": UA, "Accept-Encoding": "gzip, deflate"},
                                        redirect=False, assert_same_host=False, preload_content=False)
                headers = {k.lower(): v for k, v in response.headers.items()}
                status = response.status
                if status in {301, 302, 303, 307, 308} and headers.get("location"):
                    first_redirect = first_redirect or status
                    current = url_key(urljoin(current, headers["location"]))
                    response.drain_conn()
                    reusable = True
                    break
                data = _read_limited(response.stream(65536, decode_content=True), max_bytes)
                reusable = True
                if first_redirect:
                    headers["__redirect_status__"] = str(first_redirect)
                return status, headers, current, data
            except DownloadTimeout:
                raise  # A slow page is slow on every address; do not multiply the wait.
            except (urllib3.exceptions.HTTPError, OSError) as exc:
                last_error = exc
            finally:
                if response is not None:
                    if reusable:
                        response.release_conn()
                    else:
                        response.close()
        else:
            raise OSError(f"Could not download the website from its approved public addresses ({type(last_error).__name__}: {last_error}).") from last_error
    raise ValueError("The website returned too many redirects.")


def css_path(tag):
    parts = []
    for node in [tag, *list(tag.parents)]:
        if node.name in {"[document]", "html"}:
            break
        siblings = list(node.parent.find_all(node.name, recursive=False)) if node.parent else [node]
        index = next((i for i, sibling in enumerate(siblings, 1) if sibling is node), 1)
        parts.append(f"{node.name}:nth-of-type({index})")
    return " > ".join(reversed(parts))


# Whole tokens only. Theme flags on body/html are never page-region evidence.
NAV_TOKENS = {"nav", "navbar", "navigation", "menu", "main-nav", "main-navigation", "site-navigation", "primary-menu", "main-menu", "primary-nav", "primary-navigation", "site-nav", "mega-menu", "megamenu", "menu-main", "top-menu", "mobile-menu", "dropdown-menu", "sub-menu", "submenu", "et_pb_menu",
              "w-nav", "w-nav-menu", "navbar_component", "nav_component", "elementor-nav-menu", "e-n-menu", "hfe-nav-menu"}
HEADER_TOKENS = {"header", "site-header", "page-header", "header_wrap", "header_component", "header-wrapper", "masthead", "global-header", "top-header", "elementor-location-header"}
FOOTER_TOKENS = {"footer", "site-footer", "footer_wrap", "footer_component", "footer-wrapper", "page-footer", "global-footer", "footer-widgets", "colophon", "footer-menu", "elementor-location-footer"}
SIDEBAR_TOKENS = {"sidebar", "site-sidebar", "widget-area", "side-bar"}
BREADCRUMB_TOKENS = {"breadcrumb", "breadcrumbs", "breadcrumb-trail"}
RELATED_TOKENS = {"related-posts", "related-articles", "related-content", "recommended-posts", "you-may-also-like"}
OTHER_TOKENS = {"social-share", "social-links", "cookie-banner", "cookie-notice", "toc", "table-of-contents", "ez-toc-container", "author-bio", "author-box", "comments", "comment-list", "newsletter", "pagination", "post-navigation", "nav-links", "post-tags", "tag-list"}
# Builder class names such as footer4_component, section_footer or navbar_wrapper.
# Only used outside a real <main> element, where content cards cannot be confused with chrome.
CHROME_PART = re.compile(r"(?:^|[-_])(footer|navbar|navigation|nav|menu|header|masthead|megamenu)\d*(?:$|[-_])")
BLOCK_TAGS = ["p", "li", "dd", "blockquote", "td"]
SKIP_TEXT_TAGS = {"script", "style", "noscript", "template", "svg"}
SEPARATOR_TAGS = {"br", "div", "p", "li", "ul", "ol", "table", "tr", "td", "th", "section", "article", "h1", "h2", "h3", "h4", "h5", "h6",
                  "dd", "dt", "dl", "blockquote", "figure", "figcaption", "hr", "header", "footer", "aside", "nav", "main", "form", "button"}
DOCUMENT_TAGS = {"body", "html", "[document]"}
ELEMENTOR_CONTENT = re.compile(r"^(?:wp-page|wp-post|single|single-page|single-post|product|archive)$")


def select_main(soup, selector=""):
    """Return (main element, selector_missed)."""
    if selector:
        try:
            found = soup.select_one(selector)
        except Exception:
            found = None
        if found is not None:
            return found, False
    found = soup.find("main") or soup.find(attrs={"role": "main"})
    if found is None:
        found = soup.find(attrs={"data-elementor-type": ELEMENTOR_CONTENT})
    if found is None:
        articles = soup.find_all("article")
        if len(articles) == 1:
            found = articles[0]
    if found is None:
        for css in ("#content", ".site-main", "#main-content", ".main-content", ".entry-content"):
            found = soup.select_one(css)
            if found is not None:
                break
    return (found if found is not None else (soup.body or soup)), bool(selector)


def main_element(soup, selector=""):
    return select_main(soup, selector)[0]


class RegionResolver:
    """Memoised page-region classification; each element is examined once."""

    def __init__(self, main):
        self.main = main
        self.real_main = main is not None and main.name not in DOCUMENT_TAGS
        self._inside, self._decision = {}, {}

    def inside(self, node):
        """True when main is this node or one of its ancestors."""
        if self.main is None:
            return False
        chain, current, result = [], node, False
        while current is not None:
            key = id(current)
            if key in self._inside:
                result = self._inside[key]
                break
            if current is self.main:
                result = True
                break
            chain.append(key)
            current = current.parent
        for key in chain:
            self._inside[key] = result
        return result

    def _decide(self, node):
        tokens = {str(c).lower() for c in node.get("class", [])}
        node_id = str(node.get("id", "")).lower()
        if node_id:
            tokens.add(node_id)
        role = str(node.get("role", "")).lower()
        builder = str(node.get("data-elementor-type", "")).lower()
        strictly_in_main = self.real_main and node is not self.main and node.parent is not None and self.inside(node.parent)
        # Specific non-editorial widgets before a surrounding navigation.
        if tokens & BREADCRUMB_TOKENS or str(node.get("aria-label", "")).lower() in {"breadcrumb", "breadcrumbs"}:
            return "Breadcrumb"
        if tokens & RELATED_TOKENS:
            return "Related posts"
        # <header>/<footer> inside an article hold dates, categories and tags, not site menus.
        if strictly_in_main and node.name in {"header", "footer"}:
            return "Other"
        if builder == "footer" or node.name == "footer" or role == "contentinfo" or tokens & FOOTER_TOKENS:
            return "Footer"
        if builder == "header" or node.name in {"nav", "header"} or role in {"navigation", "menubar", "banner"} or tokens & (NAV_TOKENS | HEADER_TOKENS):
            return "Navigation"
        if node.name == "aside" or role == "complementary" or tokens & SIDEBAR_TOKENS:
            return "Sidebar"
        if (node.name in {"script", "style", "noscript", "svg", "template", "iframe", "form", "button", "select", "textarea"}
                or role in {"search", "dialog"} or node.has_attr("hidden") or str(node.get("aria-hidden", "")).lower() == "true"
                or tokens & OTHER_TOKENS or builder == "popup"):
            return "Other"
        if not strictly_in_main:
            for token in tokens:
                match = CHROME_PART.search(token)
                if match:
                    return "Footer" if match.group(1) == "footer" else "Navigation"
        return ""

    def region(self, element):
        chain, current, found = [], element, ""
        while current is not None and current.name not in DOCUMENT_TAGS:
            key = id(current)
            if key in self._decision:
                found = self._decision[key]
                break
            chain.append(key)
            found = self._decide(current)
            if found:
                break
            current = current.parent
        for key in chain:
            self._decision[key] = found
        if found:
            return found
        return "Content" if self.inside(element) else "Other"


def region_of(element, main):
    """Compatibility wrapper; prefer one RegionResolver per page."""
    return RegionResolver(main).region(element)


def collect_text(root, resolver, segments=None):
    """Visible editorial text of root. Inline markup does not add spaces; block tags do.

    When segments is a list, text outside links is appended as separate segments
    split at every link, so anchors are only ever chosen from unlinked text.
    """
    from bs4 import NavigableString, Comment, Tag
    visible, current = [], []

    def flush():
        if segments is not None:
            value = text_norm("".join(current))
            if value:
                segments.append(value)
        current.clear()

    def walk(node, in_link):
        for child in node.children:
            if isinstance(child, Comment):
                continue
            if isinstance(child, NavigableString):
                value = str(child)
                visible.append(value)
                if not in_link:
                    current.append(value)
                continue
            if not isinstance(child, Tag) or child.name in SKIP_TEXT_TAGS:
                continue
            if resolver.region(child) != "Content":
                continue
            separate = child.name in SEPARATOR_TAGS
            if separate:
                visible.append(" ")
                current.append(" ")
            if child.name == "a":
                flush()
                walk(child, True)
                flush()
            else:
                walk(child, in_link)
            if separate:
                visible.append(" ")
                current.append(" ")

    walk(root, False)
    flush()
    return text_norm("".join(visible))


def extract_content(html, url, selector="", soup=None, resolver=None, main=None):
    """Read the original DOM without deleting siblings or reparsing paragraphs."""
    from bs4 import BeautifulSoup
    soup = soup if soup is not None else BeautifulSoup(html, "lxml")
    title = text_norm(soup.title.get_text(" ", strip=True)) if soup.title else ""
    h1 = text_norm(soup.h1.get_text(" ", strip=True)) if soup.h1 else ""
    canonical_tag = soup.find("link", rel=lambda value: value and "canonical" in value)
    canonical = url_key(urljoin(url, canonical_tag.get("href", ""))) if canonical_tag else ""
    robots = " ".join(t.get("content", "") for t in soup.find_all("meta", attrs={"name": re.compile(r"^(robots|googlebot)$", re.I)}))
    selector_missed = False
    if main is None:
        main, selector_missed = select_main(soup, selector)
    resolver = resolver or RegionResolver(main)
    if main is None:
        return {"success": False, "error": "No page body was found.", "paragraphs": [], "text": "", "title": title, "h1": h1, "canonical": canonical,
                "noindex": bool(re.search(r"\b(?:noindex|none)\b", robots, re.I))}
    headings = [text_norm(x.get_text(" ", strip=True)) for x in main.find_all(["h1", "h2", "h3"]) if resolver.region(x) == "Content"]
    outgoing = [url_key(urljoin(url, a.get("href", ""))) for a in main.find_all("a", href=True) if resolver.region(a) == "Content"]
    paragraphs = []
    for block in main.find_all(BLOCK_TAGS):
        if block.find(BLOCK_TAGS) or block.find_parent("a") is not None or resolver.region(block) != "Content":
            continue
        segments = []
        paragraph = collect_text(block, resolver, segments)
        if len(paragraph.split()) < 7:
            continue
        paragraphs.append({"text": paragraph, "unlinked": segments, "locator": css_path(block), "block": len(paragraphs) + 1})
    # Retain editorial prose/headings for topic inference, excluding page chrome.
    body = collect_text(main, resolver)
    return {"success": bool(body), "error": "" if body else "No extractable body text.", "title": title, "h1": h1,
            "headings": headings, "text": body, "paragraphs": paragraphs, "outgoing_content": sorted(set(filter(None, outgoing))),
            "canonical": canonical, "noindex": bool(re.search(r"\b(?:noindex|none)\b", robots, re.I)), "selector_missed": selector_missed}


def fetch_content(profile, options, log, check_cancel):
    pages = dataset(profile, "pages")["rows"]
    if not pages:
        raise ValueError("Run or import a crawl first. Content fetching does not launch a crawl automatically.")
    eligible = [p["url"] for p in pages if p.get("status") == 200 and p.get("html") and p.get("indexable") and not excluded(p["url"], profile)]
    core = {url_key(c["url"]) for c in profile.get("core_pages", [])}
    if not options.get("all_content"):
        eligible = [u for u in eligible if is_blog(u, profile) or u in core]
    eligible.sort(key=lambda u: (u not in core, u))
    cap = int(options.get("content_cap", 1500))
    if len(eligible) > cap:
        log(f"Content fetch capped at {cap:,} of {len(eligible):,} eligible pages. Results will be partial.")
    selected = eligible[:cap]
    old = {r["url"]: r for r in dataset(profile, "content")["rows"]}
    selector = profile.get("main_selector", "")
    extraction_key = digest({"selector": selector, "version": APP_VERSION})
    cache_hours = float(options.get("cache_hours", 24))
    fresh = {}
    for u, row in old.items():
        try:
            age = (datetime.now(timezone.utc) - datetime.fromisoformat(row.get("fetched_at", ""))).total_seconds() / 3600
        except ValueError:
            age = float("inf")
        if row.get("success") and age < cache_hours and row.get("extraction_key") == extraction_key and not options.get("refresh_content"):
            fresh[u] = row
    pending = [u for u in selected if u not in fresh]
    robots_by_origin = {}
    for u in pending:
        origin = urlunsplit((*urlsplit(u)[:2], "", "", ""))
        if origin in robots_by_origin:
            continue
        parser = RobotFileParser(origin + "/robots.txt")
        try:
            code, _, _, body = get_bytes(origin + "/robots.txt", 1_000_000)
            if code in {404, 410}:
                parser.parse(["User-agent: *", "Disallow:"])
            elif code == 200:
                parser.parse(body.decode("utf-8", errors="replace").splitlines())
            else:
                parser.parse(["User-agent: *", "Disallow: /"])
                log(f"Content requests paused for {origin}: robots.txt returned {code}.")
        except Cancelled:
            raise
        except Exception as exc:
            parser.parse(["User-agent: *", "Disallow: /"])
            log(f"Content requests paused for {origin}: robots.txt could not be read ({exc}).")
        robots_by_origin[origin] = parser
    lock, last_request = threading.Lock(), [0.0]

    def fetch_one(u):
        check_cancel()
        origin = urlunsplit((*urlsplit(u)[:2], "", "", ""))
        parser = robots_by_origin[origin]
        if not parser.can_fetch(UA, u):
            return {"url": u, "success": False, "error": "Blocked by robots.txt or robots.txt unavailable.", "fetched_at": utc_now(), "extraction_key": extraction_key}
        delay = max(float(options.get("request_delay", .6)), float(parser.crawl_delay(UA) or parser.crawl_delay("*") or 0))
        with lock:
            while time.monotonic() < last_request[0] + delay:
                check_cancel()
                time.sleep(.1)
            last_request[0] = time.monotonic()
        try:
            status, headers, final_url, html = get_bytes(u)
            if status != 200 or "html" not in headers.get("Content-Type", headers.get("content-type", "")).lower():
                raise ValueError(f"HTTP {status}, non-HTML or unavailable content.")
            if not same_site(final_url, profile):
                raise ValueError("Response redirected outside the configured client hosts.")
            row = extract_content(html, final_url, selector)
            header_robots = headers.get("X-Robots-Tag", headers.get("x-robots-tag", ""))
            row["noindex"] = row.get("noindex", False) or bool(re.search(r"\bnoindex\b", header_robots, re.I))
            row.update(url=u, status=status, final_url=url_key(final_url), fetched_at=utc_now(), extraction_key=extraction_key)
            return row
        except Cancelled:
            raise
        except Exception as exc:
            return {"url": u, "success": False, "error": str(exc), "fetched_at": utc_now(), "extraction_key": extraction_key}

    output = {u: fresh[u] for u in selected if u in fresh}
    progress_update(log, len(output), len(selected), f"Reading content from {len(selected):,} blog and core pages.")
    with ThreadPoolExecutor(max_workers=int(options.get("fetch_workers", 3))) as executor:
        futures = {executor.submit(fetch_one, u): u for u in pending}
        for i, future in enumerate(as_completed(futures), 1):
            check_cancel()
            row = future.result()
            output[row["url"]] = row
            progress_update(log, len(output), len(selected), f"Read content from {len(output):,}/{len(selected):,} pages.")
    save_dataset(profile, "content", list(output.values()), scope="all eligible" if options.get("all_content") else "blogs + approved core pages",
                 eligible=len(eligible), selected=len(selected), partial=len(eligible) > cap,
                 failed=sum(not r.get("success") for r in output.values()), extraction_key=extraction_key)
    log(f"Saved content for {sum(r.get('success', False) for r in output.values()):,}/{len(selected):,} pages.")


def discover_sitemaps(profile, options, log, check_cancel):
    from lxml import etree
    root = profile["root_url"]
    origin = urlunsplit((*urlsplit(root)[:2], "", "", ""))
    urls = list(profile.get("sitemap_urls", []))
    if not urls:
        try:
            code, _, _, raw = get_bytes(origin + "/robots.txt", 1_000_000)
            if code == 200:
                urls += re.findall(r"^\s*Sitemap:\s*(\S+)", raw.decode("utf-8", errors="replace"), re.I | re.M)
        except Cancelled:
            raise
        except Exception as exc:
            log(f"Could not discover sitemaps from robots.txt: {exc}")
        urls += [origin + "/sitemap.xml", origin + "/sitemap_index.xml"]
    pending, seen, found, errors = deque(dict.fromkeys(urls)), set(), set(), []
    cap = int(options.get("sitemap_cap", 50))
    while pending and len(seen) < cap:
        check_cancel()
        u = url_key(pending.popleft())
        map_host = (urlsplit(u).hostname or "").lower()
        site_base = (urlsplit(profile["root_url"]).hostname or "").lower().removeprefix("www.")
        allowed_map = same_site(u, profile) or map_host.endswith("." + site_base)
        if not u or u in seen or not allowed_map:
            continue
        seen.add(u)
        try:
            code, _, _, raw = get_bytes(u, 10_000_000)
            if code != 200:
                raise ValueError(f"HTTP {code}")
            if raw[:2] == b"\x1f\x8b":
                with gzip.GzipFile(fileobj=io.BytesIO(raw)) as compressed:
                    raw = compressed.read(20_000_001)
                if len(raw) > 20_000_000:
                    raise ValueError("Decompressed sitemap is too large.")
            tree = etree.fromstring(raw, parser=etree.XMLParser(resolve_entities=False, no_network=True))
            if etree.QName(tree).localname not in {"sitemapindex", "urlset"}:
                raise ValueError("This URL returned a page rather than an XML sitemap.")
            locations = [str(x).strip() for x in tree.xpath("//*[local-name()='loc']/text()")]
            if etree.QName(tree).localname == "sitemapindex":
                pending.extend(locations)
            else:
                found.update(url_key(x) for x in locations if same_site(x, profile))
            if len(found) > 100_000:
                raise ValueError("Sitemap inventory exceeded 100,000 URLs. Split the scope before continuing.")
        except Cancelled:
            raise
        except Exception as exc:
            errors.append(f"{u}: {exc}")
    if not found and errors:
        raise ValueError("No sitemap URLs could be loaded. " + "; ".join(errors[:3]))
    save_dataset(profile, "sitemaps", [{"url": u} for u in sorted(found)], partial=bool(pending), sitemaps_checked=len(seen), warnings=errors)
    log(f"Discovered {len(found):,} URLs from {len(seen):,} sitemap requests.")


# Utility, legal, archive and conversion pages are never proposed as core pages
# automatically. You can still add any of them by hand or with a URL pattern.
CORE_SKIP = re.compile(
    r"^/(?:about(?:-us)?|our-company|our-team|company|team|contact(?:-us|-sales)?|support|help(?:-center)?|faqs?|careers?|jobs?|work-for-us|"
    r"privacy[a-z-]*|terms[a-z-]*|legal|cookies?[a-z-]*|gdpr|disclaimer|accessibility|sitemap|table-of-processors|"
    r"login|log-in|logout|sign-in|sign-up|signup|register|account|my-account|cart|checkout|search|"
    r"tag|tags|authors?|category|categories|product-category|"
    r"blog(?:-category|-categories)?|blogs|articles|insights|news|newsroom|press|resources|events|webinars|case-studies|customer-stories|testimonials|"
    r"docs|documentation|developers|api-status|status|pricing|partners?|become-a-partner|request(?:-a)?-demo|book-a-demo|get-a-demo|demo)(?:/|$)", re.I)
BINARY_PATH = re.compile(r"\.(?:jpe?g|png|webp|gif|svg|ico|css|js|map|pdf|zip|gz|xml|mp4|mov|mp3|woff2?|ttf|eot|xlsx?|docx?|csv)(?:$|\?)", re.I)
ARTICLE_SCHEMA = re.compile(r'"(?:BlogPosting|NewsArticle|Article)"')


def page_from_html(raw, url, profile, headers=None):
    """One parse supplies article detection, crawl edges and source text."""
    from bs4 import BeautifulSoup
    soup = BeautifulSoup(raw, "lxml")
    headers = headers or {}
    main, selector_missed = select_main(soup, profile.get("main_selector", ""))
    resolver = RegionResolver(main)
    extracted = extract_content(raw, url, profile.get("main_selector", ""), soup=soup, resolver=resolver, main=main)
    extracted["selector_missed"] = selector_missed
    robots = " ".join(t.get("content", "") for t in soup.find_all("meta", attrs={"name": re.compile(r"^(robots|googlebot)$", re.I)}))
    robots_all = robots + " " + headers.get("x-robots-tag", "")
    noindex = extracted.get("noindex", False) or bool(re.search(r"\b(?:noindex|none)\b", headers.get("x-robots-tag", ""), re.I))
    canonical = extracted.get("canonical") or url
    # http/https, www and trailing-slash differences are the same page.
    same_canonical = loose_key(canonical) == loose_key(url)
    page = {"url": url, "status": 200, "html": True, "content_type": "text/html", "title": extracted.get("title", ""),
            "h1": extracted.get("h1", ""), "canonical": canonical, "redirect": "", "noindex": noindex,
            "source_nofollow": bool(re.search(r"\b(?:nofollow|none)\b", robots_all, re.I)),
            "indexable": not noindex and same_canonical, "selector_missed": selector_missed,
            "indexability_status": "noindex" if noindex else "" if same_canonical else "Canonicalised"}
    # Yoast and similar plugins put og:type=article on ordinary pages. Count a page
    # as an article only with article schema, a publication date, or a blog URL.
    ogtype = soup.find("meta", attrs={"property": "og:type"})
    published = soup.find("meta", attrs={"property": "article:published_time"})
    schema_text = " ".join(t.get_text() for t in soup.find_all("script", attrs={"type": "application/ld+json"}))
    article = bool(ARTICLE_SCHEMA.search(schema_text)) or bool(ogtype and ogtype.get("content", "").lower() == "article" and published)
    page["article"] = article or blog_by_path(url, profile)
    edges = []
    for anchor in soup.find_all("a", href=True):
        destination = url_key(urljoin(url, anchor["href"]))
        if not same_site(destination, profile):
            continue
        position = resolver.region(anchor)
        image = anchor.find("img")
        rel = {str(value).lower() for value in (anchor.get("rel") or [])}
        edges.append({"source": url, "destination": destination, "anchor": text_norm(anchor.get_text(" ", strip=True)),
                      "alt": image.get("alt", "") if image else "", "position": position, "position_known": True,
                      "contextual": position == "Content", "type": "Hyperlink", "locator": css_path(anchor) if position == "Content" else "",
                      "followable": "nofollow" not in rel and not page["source_nofollow"]})
    org_names = []
    site_name = soup.find("meta", attrs={"property": "og:site_name"})
    if site_name and 1 <= len(text_norm(site_name.get("content", "")).split()) <= 5:
        org_names.append(text_norm(site_name["content"]))
    for script in soup.find_all("script", attrs={"type": "application/ld+json"}):
        try:
            stack = [json.loads(script.get_text())]
            while stack:
                value = stack.pop()
                if isinstance(value, list):
                    stack.extend(value)
                elif isinstance(value, dict):
                    kinds = value.get("@type", [])
                    if isinstance(kinds, str):
                        kinds = [kinds]
                    if set(kinds) & {"Organization", "Corporation"} and isinstance(value.get("name"), str):
                        org_names.append(text_norm(value["name"]))
                    stack.extend(v for v in value.values() if isinstance(v, (dict, list)))
        except (ValueError, TypeError):
            continue
    extracted.update(url=url, final_url=url, status=200, fetched_at=utc_now(), noindex=noindex,
                     extraction_key=digest({"selector": profile.get("main_selector", ""), "version": APP_VERSION}))
    return page, edges, extracted, org_names


def automatic_brand_terms(profile, names=()):
    host = (urlsplit(profile["root_url"]).hostname or "").removeprefix("www.")
    first_label = host.split(".")[0]
    terms = list(profile.get("brand_terms", [])) + [first_label]
    clean_name = text_norm(profile.get("name", ""))
    if clean_name and "." not in clean_name and "synthetic" not in clean_name:
        terms.append(clean_name)
    terms.extend(n for n in names if 1 <= len(n.split()) <= 6 and n.lower() not in {"home", "website", "blog", "organization"})
    profile["brand_terms"] = sorted({text_norm(t).lower() for t in terms if len(text_norm(t)) >= 2})
    profile["automatic_setup"] = True


def detect_proprietary_product_brands(profile, rows):
    """Only add product names when the page explicitly identifies an own source."""
    terms = []
    for row in rows:
        source = re.search(r"\bSource\s+(.{0,90}?)\bproprietary\b", row.get("text", ""), re.I)
        name = text_norm(row.get("h1", "")).strip("®™ ")
        if source and brand_pattern(profile).search(source.group(1)) and len(name) > 4 and (re.fullmatch(r"[A-Z][a-z]+(?:[A-Z][A-Za-z]+)+", name) or re.fullmatch(r"[A-Z][A-Z0-9]+", name)):
            terms.extend([name, re.sub(r"(?<=[a-z])(?=[A-Z])", " ", name)])
    if terms:
        automatic_brand_terms(profile, terms)


CORE_SIGNAL_PRIORITY = {"Main navigation": 5, "Footer": 4, "URL pattern": 4, "Linked site-wide": 3}


def _clean_label(text, profile):
    """Remove the brand unless that leaves nothing meaningful ('Why Total Synergy?' stays as is)."""
    cleaned = without_brand(text, profile).strip(" -|:–—?")
    return cleaned if meaningful_tokens(cleaned) else text_norm(text)


def core_topic(url, page, anchors, profile):
    """Short menu labels ('Manage Projects') describe a page better than long H1 slogans.
    The most frequent label wins; ties go to the shorter label, so a footer's 'Manage Projects'
    beats a mega-menu's 'Manage Projects On time and on budget.'"""
    labels = [(count, -len(text.split()), text) for text, count in anchors.items()
              if 1 <= len(text.split()) <= 6 and text.casefold() not in GENERIC_ANCHORS]
    if labels:
        return _clean_label(max(labels)[2], profile)
    if page and (page.get("h1") or page.get("title")):
        return _clean_label(page.get("h1") or page.get("title"), profile)
    return _clean_label(urlsplit(url).path.strip("/").split("/")[-1].replace("-", " "), profile)


def infer_core_pages(profile, pages, links, strict=True):
    """Core pages = main-navigation links + footer links + links repeated on most pages,
    plus your URL patterns and additions, minus pages you removed."""
    page_map = {p["url"]: p for p in pages}
    aliases = aliases_for(pages, profile)
    html_sources = {p["url"] for p in pages if p.get("status") == 200 and p.get("html")}
    total_sources = max(1, len(html_sources))
    menu, footer, chrome, anchors = defaultdict(set), defaultdict(set), defaultdict(set), defaultdict(Counter)
    for link in links:
        target, source = resolve_alias(link["destination"], aliases), link["source"]
        if not target or target == resolve_alias(source, aliases):
            continue
        position = str(link.get("position", "")).lower()
        if any(term in position for term in ("nav", "header", "menu")):
            menu[target].add(source)
        elif "footer" in position:
            footer[target].add(source)
        # Template links whose markup was not recognised still repeat on most pages.
        if not link.get("contextual") and position not in {"breadcrumb", "related posts", "sidebar"}:
            chrome[target].add(source)
        anchor = text_norm(link.get("anchor", ""))
        if anchor and not link.get("contextual"):
            anchors[target][anchor] += 1
    removed = {url_key(u) for u in profile.get("core_excluded", [])}
    sitewide_minimum = max(3, math.ceil(.3 * total_sources)) if total_sources >= 5 else 1

    def eligible(u, explicit=False):
        if not u or not same_site(u, profile) or is_home(u, profile) or BINARY_PATH.search(u):
            return False
        page = page_map.get(u)
        if strict and not (page and page.get("indexable") and page.get("status") == 200 and page.get("html")):
            return False
        if explicit:
            return True
        path = urlsplit(u).path or "/"
        return not (u in removed or excluded(u, profile) or CORE_SKIP.search(path) or is_blog(u, profile) or is_archive(u))

    candidates = {}
    for u in set(menu) | set(footer) | set(chrome):
        if menu[u]:
            detected = "Main navigation"
        elif footer[u]:
            detected = "Footer"
        elif len(chrome[u]) >= sitewide_minimum:
            detected = "Linked site-wide"
        else:
            continue
        if not eligible(u):
            continue
        sources = menu[u] | footer[u] | chrome[u]
        candidates[u] = {"url": u, "topic": core_topic(u, page_map.get(u), anchors[u], profile), "priority": CORE_SIGNAL_PRIORITY[detected],
                         "detected_from": detected, "origin": "auto", "linked_from_pages": len(sources),
                         "sitewide_share": round(len(sources) / total_sources, 3)}
    patterns = []
    for pattern in profile.get("core_patterns", []):
        try:
            patterns.append(re.compile(pattern, re.I))
        except re.error:
            continue
    if patterns:
        for p in pages:
            u = resolve_alias(p["url"], aliases)
            if u in candidates or u in removed or not any(rx.search(urlsplit(u).path or "/") for rx in patterns):
                continue
            target = page_map.get(u)
            if target and eligible(u, explicit=True):
                candidates[u] = {"url": u, "topic": core_topic(u, target, anchors[u], profile), "priority": CORE_SIGNAL_PRIORITY["URL pattern"],
                                 "detected_from": "URL pattern", "origin": "pattern", "linked_from_pages": len(menu[u] | footer[u] | chrome[u]),
                                 "sitewide_share": round(len(menu[u] | footer[u] | chrome[u]) / total_sources, 3)}
    # Pages you added are always kept, even when this crawl did not reach them.
    for core in profile.get("core_pages", []):
        if core.get("origin") != "manual":
            continue
        u = resolve_alias(core["url"], aliases) or url_key(core["url"])
        if not u or u in removed:
            continue
        verified = eligible(u, explicit=True)
        detected = candidates.get(u, {})
        label = "Confirmed by you" + (f" ({core['signal']})" if core.get("signal") else "")
        candidates[u] = {**core, "url": u, "origin": "manual", "priority": max(4, int(core.get("priority", 4))),
                         "detected_from": label if verified or not strict else label + " — not reached in this crawl",
                         "linked_from_pages": detected.get("linked_from_pages", core.get("linked_from_pages")),
                         "sitewide_share": detected.get("sitewide_share", core.get("sitewide_share")),
                         "topic": core.get("topic") or core_topic(u, page_map.get(u), anchors[u], profile)}
    profile["core_pages"] = sorted(candidates.values(), key=lambda c: (-c["priority"], -c.get("linked_from_pages", 0), c["url"]))
    return profile["core_pages"]


def fallback_core_pages(profile, pages, links, limit=15):
    """Most-linked non-blog pages, used only when no menu, footer or pattern signal exists."""
    aliases = aliases_for(pages, profile)
    page_map = {p["url"]: p for p in pages}
    removed = {url_key(u) for u in profile.get("core_excluded", [])}
    sources = defaultdict(set)
    for link in links:
        target = resolve_alias(link["destination"], aliases)
        if target and target != link["source"]:
            sources[target].add(link["source"])
    ranked = []
    for u, linked in sources.items():
        p = page_map.get(u, {})
        if (p.get("indexable") and p.get("status") == 200 and p.get("html") and same_site(u, profile) and not is_home(u, profile)
                and not is_blog(u, profile) and not is_archive(u) and u not in removed and not CORE_SKIP.search(urlsplit(u).path or "/")):
            ranked.append((len(linked), u))
    ranked.sort(reverse=True)
    return [{"url": u, "topic": core_topic(u, page_map[u], Counter(), profile), "priority": 2, "origin": "auto",
             "detected_from": "Most-linked page (please review)", "linked_from_pages": n,
             "sitewide_share": round(n / max(1, len(pages)), 3)} for n, u in ranked[:limit]]


def built_in_crawl(profile, options, log, check_cancel, homepage=None):
    """Bounded HTML crawl for hosted Streamlit; robots rules are respected."""
    limit = int(options.get("crawl_limit", 2000))
    heap, scheduled = [], set()
    queue_priority, in_flight = {}, set()
    pages, links, content, article_urls = {}, [], {}, set()
    import heapq
    robot_cache = {}
    rate_lock, last_request = threading.Lock(), [0.0]
    counters = Counter()

    def enqueue(u, priority=3):
        u = url_key(u)
        if u and same_site(u, profile) and u not in pages and u not in in_flight and not BINARY_PATH.search(u) and not excluded(u, profile):
            # Tracking params are removed by url_key; avoid faceted URL explosions.
            params = parse_qsl(urlsplit(u).query)
            if params and not all((k in {"page", "paged", "p", "offset"} or k.endswith("_page")) and v.isdigit() and 0 < int(v) <= 10000 for k, v in params):
                return
            if u in queue_priority and priority >= queue_priority[u]:
                return
            scheduled.add(u)
            queue_priority[u] = priority
            heapq.heappush(heap, (priority, u))

    def robots_for(u):
        origin = urlunsplit((*urlsplit(u)[:2], "", "", ""))
        if origin not in robot_cache:
            parser = RobotFileParser(origin + "/robots.txt")
            try:
                code, _, _, body = get_bytes(origin + "/robots.txt", 1_000_000)
                parser.parse(body.decode("utf-8", errors="replace").splitlines() if code == 200 else ["User-agent: *", "Disallow:" if code in {404, 410} else "Disallow: /"])
            except Cancelled:
                raise
            except Exception:
                parser.parse(["User-agent: *", "Disallow: /"])
            robot_cache[origin] = parser
        return robot_cache[origin]

    def fetch(u, parser):
        check_cancel()
        if not parser.can_fetch(UA, u):
            return u, None, "Blocked by robots.txt (or robots.txt unavailable)."
        delay = max(.35, float(parser.crawl_delay(UA) or parser.crawl_delay("*") or 0))
        with rate_lock:
            while time.monotonic() < last_request[0] + delay:
                check_cancel()
                time.sleep(.1)
            last_request[0] = time.monotonic()
        try:
            return u, get_bytes(u), ""
        except Cancelled:
            raise
        except Exception as exc:
            return u, None, str(exc)

    def consume(u, response, error=""):
        check_cancel()
        counters["checked"] += 1
        empty = {"title": "", "h1": "", "canonical": "", "redirect": ""}
        if error or response is None:
            blocked = error.startswith("Blocked by robots")
            pages[u] = {**empty, "url": u, "status": 0, "html": False, "indexable": False, "indexability_status": error, "robots_blocked": blocked}
            counters["robots_blocked" if blocked else "failed"] += 1
            return
        status, headers, final, raw = response
        final = url_key(final)
        if not same_site(final, profile):
            # An off-site redirect is a site fact, not a crawler failure.
            pages[u] = {**empty, "url": u, "status": int(headers.get("__redirect_status__") or 0), "html": False, "indexable": False,
                        "indexability_status": "Redirects outside the configured website", "redirect": final, "external_redirect": True}
            return
        if u != final:
            pages[u] = {**empty, "url": u, "status": int(headers.get("__redirect_status__") or 0), "html": True, "indexable": False,
                        "indexability_status": "Redirected (chain not recorded)", "redirect": final}
            if final in pages or final in in_flight:
                return
        if status != 200 or "html" not in headers.get("content-type", "").lower():
            if status in {401, 403, 429} or status >= 500:
                counters["failed"] += 1
            elif status >= 400:
                counters["client_errors"] += 1
            pages[final] = {**empty, "url": final, "status": status, "html": "html" in headers.get("content-type", ""), "indexable": False,
                            "indexability_status": f"HTTP {status}"}
            return
        page, edges, body, _ = page_from_html(raw, final, profile, headers)
        pages[final] = page
        if page.get("selector_missed"):
            counters["selector_missed"] += 1
        canonical = page.get("canonical", "")
        if canonical and loose_key(canonical) != loose_key(final) and same_site(canonical, profile):
            enqueue(canonical, 0)  # Verify the canonical target before trusting it.
        links.extend(edges)
        content[final] = body
        if page.get("article"):
            article_urls.add(final)
        for edge in edges:
            if edge.get("followable"):
                d = edge["destination"]
                structural = edge["position"] in {"Navigation", "Footer"}
                blog_section = bool(re.search(profile.get("blog_pattern", r"/blog/"), urlsplit(d).path.rstrip("/") + "/", re.I))
                enqueue(d, 1 if structural and not CORE_SKIP.search(urlsplit(d).path) else 2 if is_blog(d, profile) or blog_section else 4)

    if homepage:
        consume(profile["root_url"], homepage)
        scheduled.add(profile["root_url"])
    else:
        enqueue(profile["root_url"], 0)
    for c in profile.get("core_pages", []):
        enqueue(c["url"], 0)
    try:
        discover_sitemaps(profile, {"sitemap_cap": 40}, log, check_cancel)
    except Cancelled:
        raise
    except Exception as exc:
        log(f"Sitemap discovery unavailable; continuing through site links: {exc}")
    for r in dataset(profile, "sitemaps")["rows"]:
        enqueue(r["url"], 2 if is_blog(r["url"], profile) else 4)
    for r in dataset(profile, "gsc_total_pages")["rows"]:
        enqueue(r["page"], 2 if is_blog(r["page"], profile) else 4)
    with ThreadPoolExecutor(max_workers=3) as executor:
        futures = {}
        while heap or futures:
            check_cancel()
            while heap and len(futures) < 3 and counters["checked"] + len(futures) < limit:
                priority, u = heapq.heappop(heap)
                if u in pages or u in in_flight or priority != queue_priority.get(u):
                    continue
                parser = robots_for(u)
                in_flight.add(u)
                futures[executor.submit(fetch, u, parser)] = u
            if not futures:
                break
            finished, _ = wait(list(futures), timeout=1, return_when=FIRST_COMPLETED)
            for future in finished:
                in_flight.discard(futures.pop(future))
                u, response, error = future.result()
                consume(u, response, error)
                progress_update(log, counters["checked"], min(limit, len(scheduled)), f"Crawled {counters['checked']:,} pages · {len(heap) + len(futures):,} queued · {len(article_urls):,} blog pages found")
    page_list = list(pages.values())
    invalid_canonicals = normalize_canonicals(page_list, profile)
    profile["blog_urls"] = sorted(article_urls)
    generation = uuid.uuid4().hex
    remaining = {u for _, u in heap if u not in pages}
    partial = bool(remaining)
    metadata = dict(source="Built-in HTML crawl", generation=generation, partial=partial, crawl_limit=limit,
                    checked=counters["checked"], failed=counters["failed"], robots_blocked=counters["robots_blocked"],
                    client_errors=counters["client_errors"], invalid_canonicals=invalid_canonicals,
                    selector_missed=counters["selector_missed"], remaining=len(remaining), root=profile["root_url"],
                    crawl_schema=CRAWL_SCHEMA, classifier_version=CRAWL_SCHEMA,
                    failure_ratio=counters["failed"] / max(1, counters["checked"] - counters["robots_blocked"]))
    save_dataset(profile, "pages", page_list, **metadata)
    save_dataset(profile, "links", links, links_verified=True, position_available=True, warnings=[], **metadata)
    save_dataset(profile, "content", list(content.values()), **metadata)
    if partial:
        log(f"Crawl stopped at {limit:,} pages. {len(remaining):,} URLs remain; coverage is marked partial.")
    if invalid_canonicals:
        log(f"{invalid_canonicals} page(s) have canonical tags pointing to broken or redirecting URLs; they are kept as indexable.")
    if not any(r.get("success") for r in content.values()):
        raise ValueError("The site returned no usable HTML. It may block automated access or require JavaScript. You can use Screaming Frog exports under Connection & crawl options.")
    return counters


def google_service(interactive=False, credentials_info=None, client_config=None, return_credentials=False, timeout=GOOGLE_DATA_TIMEOUT):
    """Credentials stay in memory. Workers receive them through a stdin pipe."""
    global GOOGLE_CREDENTIALS_INFO
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from google_auth_oauthlib.flow import InstalledAppFlow
    from googleapiclient.discovery import build
    import google_auth_httplib2
    import httplib2
    credentials = None
    info = credentials_info if credentials_info is not None else (GOOGLE_CREDENTIALS_INFO if IS_WORKER and not client_config else None)
    if info:
        credentials = Credentials.from_authorized_user_info(info, SCOPES)
        if not credentials.valid and credentials.refresh_token:
            request = Request()

            def bounded_request(*args, **kwargs):
                kwargs["timeout"] = GOOGLE_HTTP_TIMEOUT
                return request(*args, **kwargs)
            credentials.refresh(bounded_request)
    if not credentials or not credentials.valid:
        if not interactive:
            raise ValueError("Connect Google under Connection & crawl options, or configure gsc_token_json in Streamlit Secrets.")
        if not client_config:
            raise ValueError("Provide a Desktop OAuth client configuration for local sign-in.")
        flow = InstalledAppFlow.from_client_config(client_config, SCOPES)
        credentials = flow.run_local_server(host="localhost", port=0, open_browser=True, timeout_seconds=180)
    updated = json.loads(credentials.to_json())
    if IS_WORKER:
        GOOGLE_CREDENTIALS_INFO = updated
    http = google_auth_httplib2.AuthorizedHttp(credentials, http=httplib2.Http(timeout=timeout), max_refresh_attempts=1)
    service = build("searchconsole", "v1", http=http, cache_discovery=False, static_discovery=True)
    return (service, updated) if return_credentials else service


def execute_google(request_factory, check_cancel=lambda: None, max_attempts=5):
    for attempt in range(max_attempts):
        check_cancel()
        try:
            return request_factory().execute()
        except Cancelled:
            raise
        except Exception as exc:
            status = getattr(getattr(exc, "resp", None), "status", None)
            transient = isinstance(exc, (TimeoutError, OSError)) or type(exc).__name__ in {"TransportError", "ReadTimeout", "ConnectTimeout", "Timeout", "ServerNotFoundError", "IncompleteRead", "RemoteDisconnected"}
            if (status not in {429, 500, 502, 503, 504} and not transient) or attempt == max_attempts - 1:
                raise
            until = time.monotonic() + min(30, 2 ** attempt)
            while time.monotonic() < until:
                check_cancel()
                time.sleep(.2)


def brand_api_filter(profile):
    terms = [text_norm(t) for t in profile.get("brand_terms", []) if text_norm(t)]
    if not terms:
        raise ValueError("Local non-brand filtering requires brand terms in the client profile.")
    body = "|".join(r"\s+".join(re.escape(w) for w in term.split()) for term in terms)
    expression = r"(?i)(?:^|\W)(?:" + body + r")(?:$|\W)"
    if len(expression) > 4096:
        raise ValueError("Brand regex exceeds GSC's 4096-character filter limit. Shorten the brand list.")
    return {"dimension": "query", "operator": "excludingRegex", "expression": expression}


def gsc_rows(service, prop, start, end, dimensions, filters, check_cancel, cap=100_000):
    rows, offset = [], 0
    while offset < cap:
        check_cancel()
        body = {"startDate": str(start), "endDate": str(end), "type": "web", "dataState": "final",
                "dimensions": dimensions, "rowLimit": 25000, "startRow": offset, "aggregationType": "auto"}
        if filters:
            body["dimensionFilterGroups"] = [{"groupType": "and", "filters": filters}]
        response = execute_google(lambda: service.searchanalytics().query(siteUrl=prop, body=body), check_cancel)
        part = response.get("rows", [])
        for row in part:
            keys = row.get("keys", [])
            if len(keys) != len(dimensions):
                continue
            item = dict(zip(dimensions, keys))
            item.update({k: float(row.get(k, 0)) for k in ["clicks", "impressions", "position"]})
            rows.append(item)
        if len(part) < 25000:
            return rows, False
        offset += 25000
    return rows, True


def aggregate_gsc(rows, keys):
    if not rows:
        return []
    df = pd.DataFrame(rows)
    for k in keys:
        if k == "page":
            df[k] = df[k].map(url_key)
        elif k == "query":
            df[k] = df[k].map(text_norm).str.lower()
    df = df[df["page"] != ""].copy() if "page" in keys else df.copy()
    df["weighted_position"] = df["position"] * df["impressions"]
    grouped = df.groupby(keys, as_index=False).agg(clicks=("clicks", "sum"), impressions=("impressions", "sum"), weighted_position=("weighted_position", "sum"))
    grouped["position"] = grouped["weighted_position"] / grouped["impressions"].replace(0, np.nan)
    grouped["ctr"] = grouped["clicks"] / grouped["impressions"].replace(0, np.nan)
    return frame_rows(grouped.drop(columns="weighted_position"))


def download_gsc(profile, options, log, check_cancel, service=None):
    if profile.get("demo"):
        raise ValueError("Demo metrics are synthetic. Select a real client for GSC requests.")
    prop = profile.get("gsc_property", "")
    if not prop:
        raise ValueError("Set this client's GSC property first.")
    if service is None:
        service = google_service()
        try:
            return download_gsc(profile, options, log, check_cancel, service=service)
        finally:
            service.close()
    start, end = date.fromisoformat(options["start_date"]), date.fromisoformat(options["end_date"])
    if start > end:
        raise ValueError("Start date must be on or before the end date.")
    mode = options.get("brand_mode", "auto")
    native, warning = False, []
    if mode != "local":
        try:
            probe, _ = gsc_rows(service, prop, start, end, ["brandedClassification"], [], check_cancel)
            native = any(r.get("brandedClassification") in {"BRANDED", "NON_BRANDED"} for r in probe)
            if not native:
                warning.append("No brand-classification rows for this property/date range; eligibility is not assumed.")
        except Exception as exc:
            if getattr(getattr(exc, "resp", None), "status", None) != 400:
                raise
            warning.append("The API rejected brandedClassification for this property/date range.")
        if mode == "native" and not native:
            raise ValueError("Native branded classification is unavailable. Choose Auto or Local brand rules.")
    filters = [{"dimension": "brandedClassification", "operator": "equals", "expression": "NON_BRANDED"}] if native else [brand_api_filter(profile)]
    method = "Google NON_BRANDED + local query/anchor safety checks" if native else "Local brand regex"
    # Separate page totals from query rows. Never label a query-row sum as page totals.
    all_pages, capped = gsc_rows(service, prop, start, end, ["page"], [], check_cancel)
    nonbrand_pages, page_cap = gsc_rows(service, prop, start, end, ["page"], filters, check_cancel)
    if capped or page_cap:
        warning.append("A page download reached the configured extraction cap.")
    chunk_days = 1 if options.get("daily_gsc") else 7
    queries, cursor = [], start
    while cursor <= end:
        check_cancel()
        chunk_end = min(end, cursor + timedelta(days=chunk_days - 1))
        chunk, truncated = gsc_rows(service, prop, cursor, chunk_end, ["page", "query"], filters, check_cancel)
        queries.extend(chunk)
        if truncated:
            warning.append(f"Query extraction cap reached for {cursor}–{chunk_end}.")
        progress_update(log, (chunk_end - start).days + 1, (end - start).days + 1,
                        f"Search Console: {cursor} to {chunk_end}; {len(chunk):,} query/page rows.")
        cursor = chunk_end + timedelta(days=1)
    pattern = brand_pattern(profile)
    queries = [r for r in queries if same_site(r.get("page", ""), profile) and not pattern.search(text_norm(r.get("query", "")))]
    nonbrand_pages = [r for r in nonbrand_pages if same_site(r.get("page", ""), profile)]
    all_pages = [r for r in all_pages if same_site(r.get("page", ""), profile)]
    meta = {"start_date": str(start), "end_date": str(end), "gsc_property": prop, "brand_method": method,
            "native_branding": native, "warnings": warning,
            "metric_basis": "Google-classified non-brand page totals; additional local exclusions apply to query themes and anchors only." if native else "Page totals requested using a query exclusion regex; hidden/anonymized queries are not included.",
            "query_coverage": "API top rows only; privacy filtering and internal GSC limits still apply.",
            "daily_query_chunks": bool(options.get("daily_gsc")), "brand_rules_hash": digest(profile.get("brand_terms", []))}
    generation = uuid.uuid4().hex
    for name, rows, keys in [("gsc_pages", nonbrand_pages, ["page"]), ("gsc_total_pages", all_pages, ["page"]), ("gsc_queries", queries, ["page", "query"])]:
        save_dataset(profile, name, aggregate_gsc(rows, keys), generation=generation, **meta)
    log(f"Saved {len(queries):,} visible non-brand query/page observations using {method}.")


def load_verified_graph(profile):
    pages_doc, links_doc = dataset(profile, "pages"), dataset(profile, "links")
    if not pages_doc["rows"] or not links_doc["meta"].get("links_verified"):
        raise ValueError("Run or import both Internal:All and All Inlinks first. Existing-link checks are required.")
    if pages_doc["meta"].get("generation") != links_doc["meta"].get("generation"):
        raise ValueError("Page and link datasets are from different imports. Import both exports together.")
    return pages_doc, links_doc


def graph_state(profile):
    profile = PreparedProfile(profile)
    import networkx as nx
    pages_doc, links_doc = load_verified_graph(profile)
    pages = {p["url"]: p for p in pages_doc["rows"]}
    aliases = aliases_for(pages_doc["rows"], profile)
    graph, content_graph = nx.DiGraph(), nx.DiGraph()
    inventory = set(pages)
    for name in ["sitemaps", "gsc_total_pages", "gsc_pages"]:
        inventory.update(r.get("url", r.get("page", "")) for r in dataset(profile, name)["rows"])
    inventory = {resolve_alias(u, aliases) for u in inventory if same_site(u, profile)}
    graph.add_nodes_from(inventory)
    content_graph.add_nodes_from(inventory)
    in_sources, contextual_sources, all_pairs, blocked_pairs = defaultdict(set), defaultdict(set), set(), set()
    for link in links_doc["rows"]:
        s, d = resolve_alias(link["source"], aliases), resolve_alias(link["destination"], aliases)
        all_pairs.add((s, d))
        if s != d:
            in_sources[d].add(s)
        if link.get("contextual") or not link.get("position_known"):
            blocked_pairs.add((s, d))
        if link.get("contextual") and s != d:
            contextual_sources[d].add(s)
        # A redirect's destination may be reached through its original href, but a
        # non-HTML/error/non-200 source cannot serve as a crawl path in this snapshot.
        source_page = pages.get(link["source"], {})
        if link.get("followable") and source_page.get("status") == 200 and source_page.get("html") and s != d:
            graph.add_edge(s, d)
            if link.get("contextual"):
                content_graph.add_edge(s, d)
    home = resolve_alias(profile["root_url"], aliases)
    depths = dict(nx.single_source_shortest_path_length(graph, home)) if home in graph else {}
    # Site-only model. This is NOT Google's PageRank and does not model external equity.
    rank = nx.pagerank(graph, alpha=.85, max_iter=300, tol=1e-7) if len(graph) else {}
    return {"pages": pages, "aliases": aliases, "graph": graph, "content_graph": content_graph, "home": home,
            "depths": depths, "rank": rank, "in_sources": in_sources, "contextual_sources": contextual_sources,
            "all_pairs": all_pairs, "blocked_pairs": blocked_pairs, "position_available": links_doc["meta"].get("position_available", False)}


def core_mapping(profile, aliases):
    return {resolve_alias(c["url"], aliases): c for c in profile.get("core_pages", [])}


def metric_maps(profile, aliases):
    def remap(name, query=False):
        rows = []
        for row in dataset(profile, name)["rows"]:
            row = dict(row)
            row["page"] = resolve_alias(row["page"], aliases)
            rows.append(row)
        return aggregate_gsc(rows, ["page", "query"] if query else ["page"])
    metrics = {r["page"]: r for r in remap("gsc_pages")}
    queries = defaultdict(list)
    brand = brand_pattern(profile)
    for row in remap("gsc_queries", True):
        if not brand.search(row["query"]):
            queries[row["page"]].append(row)
    for values in queries.values():
        values.sort(key=lambda r: r.get("impressions", 0), reverse=True)
    return metrics, queries


@lru_cache(maxsize=50000)
def stem(token):
    token = token.lower().strip("’'")
    if len(token) > 5 and token.endswith("ies"):
        return token[:-3] + "y"
    if len(token) > 4 and token.endswith("s") and not token.endswith(("ss", "us", "is")):
        return token[:-1]
    return token


def meaningful_tokens(value):
    """Two-letter acronyms such as AP, AI and HR are kept; stop words and generic words are not."""
    tokens = []
    for match in TOKEN_RE.finditer(value.lower()):
        word = match.group()
        if len(word) < 2 or word.isdigit() or word in ENGLISH_STOP_WORDS or word in GENERIC:
            continue
        tokens.append(stem(word))
    return tokens


def anchor_candidates(paragraph, dest, query_rows, profile):
    """Yield spans from unlinked text. No anchor or sentence is ever generated."""
    pattern = brand_pattern(profile)
    headings = " ".join([dest.get("topic", ""), dest.get("h1", ""), dest.get("title", "")])
    keyword_text = headings + " " + " ".join(q["query"] for q in query_rows[:25])
    weights = Counter(meaningful_tokens(keyword_text))
    # No GSC data is required: title/H1/topic remain eligible evidence.
    if not weights:
        return []
    head_terms = set(meaningful_tokens(headings))
    intent_terms = head_terms - set("data api financial market real time real-time realtime historical complete comprehensive guide access technology platform business innovative modern build best high quality global industry leading".split())
    seeds = [q["query"] for q in query_rows[:35] if 2 <= len(q["query"].split()) <= 8]
    for heading in [dest.get("topic", ""), dest.get("h1", ""), dest.get("title", "")]:
        heading = without_brand(heading, profile)
        seeds += [x.strip(" -|:–—") for x in re.split(r"[|:–—]", heading) if 2 <= len(x.split()) <= 8]
    candidates = {}
    for segment in paragraph.get("unlinked", []):
        spans = []
        for seed in dict.fromkeys(seeds):
            spans += [(m.start(), m.end(), True) for m in phrase_pattern(seed).finditer(segment)]
        tokens = list(TOKEN_RE.finditer(segment))
        for n in range(2, 7):
            for i in range(len(tokens) - n + 1):
                spans.append((tokens[i].start(), tokens[i + n - 1].end(), False))
        for start, end, seeded in spans:
            anchor = segment[start:end]
            if re.search(r"[,;:!?()\[\]{}]", anchor):
                continue
            words = [m.group().lower() for m in TOKEN_RE.finditer(anchor)]
            terms = meaningful_tokens(anchor)
            if not 2 <= len(words) <= 8 or len(anchor) > 100 or not terms or words[0] in BAD_EDGE or words[-1] in BAD_EDGE:
                continue
            if pattern.search(anchor) or text_norm(anchor).lower() in GENERIC_ANCHORS:
                continue
            overlap = set(terms) & set(weights)
            if intent_terms and not (set(terms) & intent_terms):
                continue
            precision = len(overlap) / len(set(terms))
            if len(overlap) < 2 or precision < .75 or not (overlap & head_terms):
                continue
            strength = sum(min(weights[t], 4) for t in overlap)
            score = .45 * precision + .25 * min(1, len(overlap) / 3) + .15 * (1 if seeded else 0) + .15 * min(1, strength / 10)
            # Favor compact phrases without rewarding extra non-descriptive words.
            score -= .025 * max(0, len(words) - len(terms) - 1)
            key = anchor.casefold()
            candidate = {"anchor": anchor, "anchor_score": max(0, min(1, score)), "segment": segment, "start": start, "end": end}
            if key not in candidates or candidates[key]["anchor_score"] < score:
                candidates[key] = candidate
    return sorted(candidates.values(), key=lambda c: (c["anchor_score"], -len(c["anchor"])), reverse=True)


def rank_paragraphs(documents, paragraphs, mode, allow_download=False, check_cancel=lambda: None):
    if mode == "semantic":
        try:
            from sentence_transformers import SentenceTransformer
        except ImportError as exc:
            raise ValueError("Semantic mode requires sentence-transformers. Add sentence-transformers>=3.3,<6 to requirements.txt and redeploy, or install it locally with pip.") from exc
        model = SentenceTransformer(MODEL, device="cpu", local_files_only=not allow_download)
        vectors = []
        for items in [documents, paragraphs]:
            blocks = []
            for offset in range(0, len(items), 64):
                check_cancel()
                blocks.append(model.encode(items[offset:offset + 64], normalize_embeddings=True, convert_to_numpy=True, show_progress_bar=False))
            vectors.append(np.vstack(blocks))
        return vectors[0], vectors[1], "semantic"
    from sklearn.feature_extraction.text import TfidfVectorizer
    vectorizer = TfidfVectorizer(tokenizer=meaningful_tokens, token_pattern=None, ngram_range=(1, 2), sublinear_tf=True, max_features=50000, dtype=np.float32)
    matrix = vectorizer.fit_transform(documents + paragraphs)
    return matrix[:len(documents)], matrix[len(documents):], "lexical"


REC_INPUTS = ["pages", "links", "content", "gsc_pages", "gsc_queries"]
AUDIT_INPUTS = ["pages", "links", "sitemaps", "gsc_pages", "gsc_total_pages"]
VAGUE_TOPIC_WORDS = set("data api financial market real time real-time realtime historical delayed delay minute minutes min complete comprehensive guide access technology platform business innovative modern build best high quality global industry leading software total basic bring package packages".split())


def distinctive_topic_terms(dest, profile):
    identity = without_brand(dest.get("topic", "") + " " + dest.get("h1", ""), profile)
    terms = {t for t in meaningful_tokens(identity) if t not in VAGUE_TOPIC_WORDS and not any(c.isdigit() for c in t)}
    if not terms:
        identity = without_brand(urlsplit(dest["url"]).path.replace("-", " ").replace("/", " "), profile)
        terms = {t for t in meaningful_tokens(identity) if t not in VAGUE_TOPIC_WORDS and not any(c.isdigit() for c in t)}
    return terms


def recommend(profile, options, log, check_cancel, state=None, metric_data=None):
    if options.get("query_driven") and not text_norm(options.get("anchor_text", "")):
        return recommend_from_queries(profile, options, log, check_cancel, state=state, metric_data=metric_data)
    if (not profile.get("brands_confirmed") and not options.get("automatic_setup")) or not profile.get("brand_terms"):
        raise ValueError("Review and confirm this client's brand exclusions before generating recommendations.")
    profile = PreparedProfile(profile)
    state = state if state is not None else graph_state(profile)
    pages, aliases = state["pages"], state["aliases"]
    core = core_mapping(profile, aliases)
    if not core and not options.get("blog_to_blog"):
        raise ValueError("Add approved core pages, or explicitly enable blog-to-blog opportunities.")
    content = {r["url"]: r for r in dataset(profile, "content")["rows"] if r.get("success") and not r.get("noindex")}
    if not content:
        raise ValueError("Fetch page content first. Recommendation analysis never starts a content fetch automatically.")
    metrics, queries = metric_data if metric_data is not None else metric_maps(profile, aliases)
    eligible = {u for u, p in pages.items() if p.get("status") == 200 and p.get("html") and p.get("indexable") and not excluded(u, profile)
                and u in content and url_key(content[u].get("final_url", u)) == u
                and (not content[u].get("canonical") or loose_key(content[u]["canonical"]) == loose_key(u) or p.get("invalid_canonical"))}
    sources = [u for u in eligible if (is_blog(u, profile) or options.get("all_sources")) and not is_home(u, profile) and not is_archive(u)]
    targets = [u for u in eligible if not is_home(u, profile) and (resolve_alias(u, aliases) in core or (options.get("blog_to_blog") and is_blog(u, profile)))]
    if options.get("destination_url"):
        selected_target = resolve_alias(options["destination_url"], aliases)
        targets = [u for u in targets if resolve_alias(u, aliases) == selected_target]
    requested_anchor = text_norm(options.get("anchor_text", ""))
    if requested_anchor:
        if brand_pattern(profile).search(requested_anchor):
            raise ValueError("The anchor contains this client's brand name. Enter a descriptive non-brand phrase.")
        if requested_anchor.casefold() in GENERIC_ANCHORS or len(requested_anchor) > 120:
            raise ValueError("Enter a short descriptive anchor, such as 'options data API'.")
    # Destinations are prioritized before paragraph retrieval; this cap is explicit in the UI.
    targets.sort(key=lambda u: (core.get(resolve_alias(u, aliases), {}).get("priority", 1), metrics.get(u, {}).get("impressions", 0)), reverse=True)
    target_total = len(targets)
    targets = targets[:int(options.get("target_cap", 250))]
    paragraphs = []
    for u in sorted(sources):
        for paragraph in content[u].get("paragraphs", []):
            if paragraph.get("unlinked"):
                paragraphs.append({"url": u, **paragraph})
    paragraph_total = len(paragraphs)
    paragraph_cap = int(options.get("paragraph_cap", 30000))
    paragraphs = paragraphs[:paragraph_cap]
    if not targets or not paragraphs:
        raise ValueError("No eligible source paragraphs or destinations. Check blog rules, core URLs, canonical URLs and fetched content.")
    documents, dests = [], []
    for u in targets:
        c = core.get(resolve_alias(u, aliases), {})
        dest = {"url": u, "title": content[u].get("title", pages[u].get("title", "")), "h1": content[u].get("h1", pages[u].get("h1", "")), "topic": c.get("topic", "")}
        dests.append(dest)
        # Keep target representations focused. Broad body copy must not drown out intent.
        doc = " ".join([dest["topic"]] * 3 + [dest["title"], dest["h1"]] * 2 + [" ".join(q["query"] for q in queries.get(u, [])[:20]), " ".join(content[u].get("text", "").split()[:100])])
        documents.append(without_brand(doc, profile))
    mode = options.get("matching_mode", "lexical")
    topic_frequency = Counter(t for d in dests for t in distinctive_topic_terms(d, profile))
    for dest in dests:
        terms = distinctive_topic_terms(dest, profile)
        least_common = min((topic_frequency[t] for t in terms), default=0)
        dest["signature_terms"] = {t for t in terms if topic_frequency[t] == least_common}
    threshold = float(options.get("semantic_threshold", .45) if mode == "semantic" else options.get("lexical_threshold", .10))
    if requested_anchor and options.get("destination_url"):
        threshold = 0
    log(f"Matching {len(paragraphs):,} existing paragraphs against {len(targets):,} destinations ({mode}).")
    dest_vectors, para_vectors, _ = rank_paragraphs(documents, [without_brand(p["text"], profile) for p in paragraphs], mode, options.get("allow_model_download", False), check_cancel)
    max_rank = max(state["rank"].values(), default=1)
    demand_max = max([float(m.get("impressions", 0)) for m in metrics.values()] + [1])
    rows, ambiguity, candidates_by_slot = [], 0, defaultdict(list)
    reviews = read_json(client_dir(profile) / "reviews.json", {})
    gsc_meta = dataset(profile, "gsc_pages")["meta"]
    for idx, dest in enumerate(dests):
        check_cancel()
        target = dest["url"]
        vector = dest_vectors[idx]
        scores = np.asarray(para_vectors @ vector).reshape(-1) if mode == "semantic" else (para_vectors @ vector.T).toarray().ravel()
        order = np.argsort(scores)[::-1]
        qrows = queries.get(resolve_alias(target, aliases), [])
        page_metric = metrics.get(resolve_alias(target, aliases))
        priority = int(core.get(resolve_alias(target, aliases), {}).get("priority", 1))
        contextual_count = len(state["contextual_sources"].get(target, set()))
        demand = math.log1p(float(page_metric.get("impressions", 0))) / math.log1p(demand_max) if page_metric else .25
        position = page_metric.get("position") if page_metric else None
        near_query = next((q for q in qrows if q.get("position") and 4 <= q["position"] <= 20), None)
        need = .45 * priority / 5 + .25 / (1 + contextual_count) + .2 * demand + .1 * (1 if near_query else .25)
        per_source = set()
        examined = 0
        for para_idx in order:
            relevance = float(scores[para_idx])
            if relevance < threshold or examined >= int(options.get("paragraphs_per_target", 120)):
                break
            examined += 1
            paragraph = paragraphs[int(para_idx)]
            source = paragraph["url"]
            # Prevent generic overlap (e.g. delayed stock data -> options feed)
            # from overpowering the destination's distinctive topic.
            if not options.get("destination_url") and dest["signature_terms"] and not (set(meaningful_tokens(paragraph["text"])) & dest["signature_terms"]):
                continue
            pair = (resolve_alias(source, aliases), resolve_alias(target, aliases))
            existing_body = {resolve_alias(u, aliases) for u in content[source].get("outgoing_content", [])}
            if source == target or pair in state["blocked_pairs"] or pair[1] in existing_body or source in per_source:
                continue
            if requested_anchor:
                anchors = []
                for segment in paragraph.get("unlinked", []):
                    match = phrase_pattern(requested_anchor).search(segment)
                    if match:
                        anchors.append({"anchor": match.group(), "anchor_score": .85, "segment": segment, "start": match.start(), "end": match.end()})
                # Explicitly entered anchors still need a destination that describes them.
                anchor_terms = set(meaningful_tokens(requested_anchor))
                target_terms = set(meaningful_tokens(" ".join([dest['topic'], dest['h1'], dest['title']])))
                if not options.get("destination_url") and (not anchor_terms or not (anchor_terms & target_terms)):
                    anchors = []
            else:
                anchors = anchor_candidates(paragraph, dest, qrows, profile)
            if not anchors:
                continue
            a = anchors[0]
            exact_query = next((q for q in qrows if phrase_pattern(q["query"]).fullmatch(a["anchor"])), None)
            rec_id = digest([source, target, a["anchor"].casefold(), paragraph["locator"]])[:24]
            review = reviews.get(rec_id, {})
            if review.get("status") in {"Dismissed", "Implemented"}:
                continue
            per_source.add(source)
            source_strength = state["rank"].get(source, 0) / max_rank
            normalized_relevance = min(1, relevance / (.75 if mode == "semantic" else .4))
            score = 100 * (.55 * normalized_relevance + .15 * a["anchor_score"] + .2 * need + .1 * source_strength)
            reason = f"{'Core' if target in core else 'Blog'} priority {priority}/5; {contextual_count} known contextual source(s); related paragraph; descriptive existing phrase."
            row = {"id": rec_id, "client": profile["name"], "source_url": source, "destination_url": target, "anchor_text": a["anchor"],
                   "context": paragraph["text"], "unlinked_segment": a["segment"], "source_locator": paragraph["locator"],
                   "source_block": paragraph["block"], "anchor_start_in_segment": a["start"], "anchor_end_in_segment": a["end"],
                   "action": "Add contextual link", "priority": "High" if score >= 75 else "Medium" if score >= 55 else "Low",
                   "heuristic_score": round(score, 1), "paragraph_similarity": round(relevance, 4), "matching_mode": mode,
                   "reason": reason, "destination_topic": dest["topic"] or dest["h1"], "destination_business_priority": priority,
                   "destination_nonbrand_impressions": page_metric.get("impressions") if page_metric else None,
                   "destination_nonbrand_position": position, "supporting_query": exact_query["query"] if exact_query else "",
                   "query_impressions": exact_query["impressions"] if exact_query else None,
                   "query_position": exact_query["position"] if exact_query else None,
                   "query_clicks": exact_query.get("clicks") if exact_query else None, "query_ctr": exact_query.get("ctr") if exact_query else None,
                   "evidence_type": "GSC exact query" if exact_query else "Manual anchor" if requested_anchor else "Content matching",
                   "destination_contextual_sources": contextual_count if state["position_available"] else None,
                   "source_internal_rank_model": round(state["rank"].get(source, 0), 8),
                   "gsc_period_start": gsc_meta.get("start_date", ""), "gsc_period_end": gsc_meta.get("end_date", ""),
                   "gsc_classification_method": gsc_meta.get("brand_method", "No GSC data"),
                   "source_content_fetched_at": content[source].get("fetched_at", ""),
                   "existing_other_link": pair in state["all_pairs"], "status": review.get("status", "Proposed"), "notes": review.get("notes", "")}
            rows.append(row)
            candidates_by_slot[(source, paragraph["locator"], a["anchor"].casefold())].append(row)
        progress_update(log, idx + 1, len(targets), f"Matched blog paragraphs against {idx + 1:,}/{len(targets):,} core pages.")
    ambiguous_ids = set()
    for group in candidates_by_slot.values():
        group.sort(key=lambda r: r["paragraph_similarity"], reverse=True)
        if len(group) > 1 and group[0]["paragraph_similarity"] - group[1]["paragraph_similarity"] < float(options.get("ambiguity_margin", .04)):
            ambiguous_ids.update(r["id"] for r in group)
            ambiguity += 1
    rows.sort(key=lambda r: (r["paragraph_similarity"], r["heuristic_score"]), reverse=True)
    final, counts_source, counts_target, used_blocks = [], Counter(), Counter(), set()
    for row in rows:
        s, d = row["source_url"], row["destination_url"]
        slot = (s, row["source_locator"])
        if row["id"] in ambiguous_ids or slot in used_blocks:
            continue
        if counts_source[s] >= int(options.get("links_per_source", 3)) or counts_target[d] >= int(options.get("links_per_target", 5)):
            continue
        final.append(row)
        counts_source[s] += 1
        counts_target[d] += 1
        used_blocks.add(slot)
        if len(final) >= int(options.get("recommendation_cap", 300)):
            break
    final.sort(key=lambda r: r["heuristic_score"], reverse=True)
    warnings = ["Similarity, modeled internal rank and priority are heuristics, not predicted Google ranking gains.", "One recommendation per source paragraph; caps control review workload, not SEO rules."]
    if gsc_meta.get("brand_rules_hash") and gsc_meta["brand_rules_hash"] != digest(profile.get("brand_terms", [])):
        warnings.append("Brand rules changed after the saved GSC download. Refresh GSC data to update its metric classification.")
    if not state["position_available"]:
        warnings.append("Link Position is missing. Contextual counts are unknown; existing hyperlink pairs were excluded conservatively.")
    save_dataset(profile, "recommendations", final, input_signature=input_signature(profile, REC_INPUTS),
                 settings=options, ambiguous_slots_skipped=ambiguity, candidate_links=len(rows),
                 eligible_targets=target_total, targets_checked=len(targets), paragraphs_checked=len(paragraphs),
                 partial=target_total > len(targets) or paragraph_total > len(paragraphs) or dataset(profile, "content")["meta"].get("partial", False),
                 warnings=warnings)
    log(f"Saved {len(final):,} recommendations; skipped {ambiguity:,} ambiguous placements.")


def recommend_from_queries(profile, options, log, check_cancel, state=None, metric_data=None):
    """Destination GSC query -> exact existing unlinked phrase -> source link."""
    profile = PreparedProfile(profile)
    state = state if state is not None else graph_state(profile)
    pages, aliases = state["pages"], state["aliases"]
    core = core_mapping(profile, aliases)
    query_doc = dataset(profile, "gsc_queries")
    metrics, queries = metric_data if metric_data is not None else metric_maps(profile, aliases)
    content = {r["url"]: r for r in dataset(profile, "content")["rows"] if r.get("success") and not r.get("noindex")}
    eligible = {u for u, p in pages.items() if p.get("status") == 200 and p.get("html") and p.get("indexable")
                and not excluded(u, profile) and u in content and url_key(content[u].get("final_url", u)) == u
                and (not content[u].get("canonical") or loose_key(content[u]["canonical"]) == loose_key(u) or p.get("invalid_canonical"))}
    sources = sorted((u for u in eligible if not is_home(u, profile) and not is_archive(u) and (is_blog(u, profile) or options.get("all_sources"))),
                     key=lambda u: (not is_blog(u, profile), u))
    targets = {u for u in eligible if not is_home(u, profile) and (u in core or (options.get("blog_to_blog") and is_blog(u, profile)))}
    if options.get("destination_url"):
        targets &= {resolve_alias(options["destination_url"], aliases)}
    minimum_words = max(1, int(options.get("min_query_words", 2)))
    warnings = ["Priority is a review heuristic, not a prediction of ranking gains.",
                "Exact matches ignore capitalization and repeated whitespace; word order and wording must match.",
                "One new placement per source paragraph; existing contextual source/destination pairs are excluded.",
                query_doc["meta"].get("query_coverage", "GSC exposes visible top query rows, not every search query.")]
    warnings.extend(query_doc["meta"].get("warnings", []))
    if not query_doc["rows"]:
        warnings.append("No page/query GSC data is available. Automatic query-based recommendations require GSC; use a manual anchor to search content without GSC.")
    if query_doc["meta"].get("brand_rules_hash") and query_doc["meta"]["brand_rules_hash"] != digest(profile.get("brand_terms", [])):
        warnings.append("Brand exclusions changed after the GSC download. Query anchors use current exclusions; refresh GSC to update all page totals.")
    if core and not targets:
        warnings.append("None of the core pages could be read as indexable HTML in this crawl, so no destinations were available.")
    inventory = []
    for target in sorted(targets):
        for query in queries.get(target, []):
            phrase = text_norm(query["query"])
            words = re.findall(r"\w+", phrase.casefold())
            if (len(words) < minimum_words or len(words) > 12 or len(phrase) > 120 or not meaningful_tokens(phrase)
                    or phrase.casefold() in GENERIC_ANCHORS or brand_pattern(profile).search(phrase)
                    or re.search(r"[,;:!?()\[\]{}]", phrase)
                    or (len(words) == 1 and words[0] in (GENERIC | BAD_EDGE | VAGUE_TOPIC_WORDS))
                    or float(query.get("impressions") or 0) <= 0 or float(query.get("position") or 0) <= 0):
                continue
            inventory.append({**query, "page": target})
    demand_max = max([float(q["impressions"]) for q in inventory] + [1])

    def query_need(q):
        position = float(q["position"])
        position_weight = 1 if 8 <= position <= 20 else .8 if 4 <= position <= 30 else .45 if position > 30 else .2
        demand = math.log1p(float(q["impressions"])) / math.log1p(demand_max)
        return .65 * demand + .35 * position_weight
    inventory.sort(key=lambda q: query_need(q), reverse=True)
    blocks, token_index = [], defaultdict(set)
    paragraph_count, total_paragraphs = 0, 0
    paragraph_cap = int(options.get("paragraph_cap", 30000))
    for source in sources:
        for paragraph in content[source].get("paragraphs", []):
            if not paragraph.get("unlinked"):
                continue
            total_paragraphs += 1
            if paragraph_count >= paragraph_cap:
                continue
            check_cancel()
            paragraph_count += 1
            for segment in paragraph["unlinked"]:
                block_id = len(blocks)
                blocks.append({**paragraph, "url": source, "segment": segment})
                for token in set(re.findall(r"\w+", segment.casefold())):
                    token_index[token].add(block_id)
    reviews = read_json(client_dir(profile) / "reviews.json", {})
    target_terms = {u: set(meaningful_tokens(" ".join([core.get(u, {}).get("topic", ""), content[u].get("title", ""),
                                                    content[u].get("h1", ""), " ".join(content[u].get("text", "").split()[:250])]))) for u in targets}
    rows, candidate_cap = [], int(options.get("query_candidate_cap", 20000))
    seen, truncated, checked = set(), False, 0
    max_rank = max(state["rank"].values(), default=1) or 1
    brand = brand_pattern(profile)
    progress_update(log, 0, len(inventory), f"Checking {len(inventory):,} non-brand query/page pairs against {len(blocks):,} unlinked content blocks.")
    for q in inventory:
        check_cancel()
        checked += 1
        target, phrase = q["page"], q["query"]
        tokens = sorted(set(re.findall(r"\w+", phrase.casefold())), key=lambda t: len(token_index.get(t, ())))
        hits = set(token_index.get(tokens[0], ()))
        for token in tokens[1:]:
            hits.intersection_update(token_index.get(token, ()))
            if not hits:
                break
        matcher = phrase_pattern(phrase)
        for block_id in sorted(hits):
            check_cancel()
            block = blocks[block_id]
            source = block["url"]
            pair = (resolve_alias(source, aliases), target)
            if (pair[0] == target or pair in state["blocked_pairs"]
                    or target in {resolve_alias(u, aliases) for u in content[source].get("outgoing_content", [])}):
                continue
            match = matcher.search(block["segment"])
            if not match:
                continue
            anchor = match.group()
            # Never use a branded occurrence such as "BrandCo document scanning"
            # as the anchor; the query text itself must already be non-branded.
            if brand.search(anchor):
                continue
            key = (source, target, block["locator"], phrase.casefold())
            if key in seen:
                continue
            seen.add(key)
            rec_id = digest([source, target, anchor.casefold(), block["locator"]])[:24]
            review = reviews.get(rec_id, {})
            if review.get("status") in {"Dismissed", "Implemented"}:
                continue
            query_terms = set(meaningful_tokens(phrase))
            context_terms = set(meaningful_tokens(block["text"])) - query_terms
            destination_terms = target_terms[target] - query_terms
            relevance = len(context_terms & destination_terms) / math.sqrt(max(1, len(context_terms) * len(destination_terms)))
            support = len(state["contextual_sources"].get(target, set()))
            priority = int(core.get(target, {}).get("priority", 1))
            score = 100 * (.6 * query_need(q) + .15 / (1 + support) + .1 * min(1, priority / 5)
                           + .05 * min(1, state["rank"].get(source, 0) / max_rank) + .05 * min(1, relevance * 4) + .05 * is_blog(source, profile))
            page_metric = metrics.get(target, {})
            rows.append({"id": rec_id, "client": profile["name"], "source_url": source, "destination_url": target,
                         "anchor_text": anchor, "supporting_query": phrase, "query_impressions": q["impressions"],
                         "query_position": q["position"], "query_clicks": q.get("clicks"), "query_ctr": q.get("ctr"),
                         "evidence_type": "GSC exact query", "matching_mode": "gsc_exact_query",
                         "context": block["text"], "unlinked_segment": block["segment"], "source_locator": block["locator"],
                         "source_block": block["block"], "anchor_start_in_segment": match.start(), "anchor_end_in_segment": match.end(),
                         "action": "Add contextual link", "priority": "High" if score >= 75 else "Medium" if score >= 55 else "Low",
                         "heuristic_score": round(score, 1), "paragraph_similarity": round(relevance, 4),
                         "reason": f"Exact GSC query on this destination: {q['impressions']:,.0f} impressions, average position {q['position']:.1f}; phrase already exists unlinked in this source; {support} known contextual source(s).",
                         "destination_topic": core.get(target, {}).get("topic", "") or content[target].get("h1", ""),
                         "destination_business_priority": priority, "destination_nonbrand_impressions": page_metric.get("impressions"),
                         "destination_nonbrand_position": page_metric.get("position"),
                         "destination_contextual_sources": support if state["position_available"] else None,
                         "source_internal_rank_model": round(state["rank"].get(source, 0), 8),
                         "source_page_type": "Blog" if is_blog(source, profile) else "Other content page",
                         "gsc_period_start": query_doc["meta"].get("start_date", ""), "gsc_period_end": query_doc["meta"].get("end_date", ""),
                         "gsc_classification_method": query_doc["meta"].get("brand_method", ""),
                         "source_content_fetched_at": content[source].get("fetched_at", ""), "existing_other_link": pair in state["all_pairs"],
                         "status": review.get("status", "Proposed"), "notes": review.get("notes", "")})
            if len(rows) >= candidate_cap:
                truncated = True
                break
        if checked % 20 == 0 or checked == len(inventory) or truncated:
            progress_update(log, checked, len(inventory), f"Checked {checked:,}/{len(inventory):,} GSC query/page pairs; found {len(rows):,} exact unlinked placements.")
        if truncated:
            break
    # A query shared by several target pages needs a clear contextual winner.
    groups, ambiguous_ids = defaultdict(list), set()
    for row in rows:
        groups[(row["source_url"], row["source_locator"], row["supporting_query"])].append(row)
    for group in groups.values():
        group.sort(key=lambda r: r["paragraph_similarity"], reverse=True)
        if len(group) > 1:
            if group[0]["paragraph_similarity"] - group[1]["paragraph_similarity"] < float(options.get("ambiguity_margin", .04)):
                ambiguous_ids.update(r["id"] for r in group)
            else:
                ambiguous_ids.update(r["id"] for r in group[1:])
    rows.sort(key=lambda r: r["heuristic_score"], reverse=True)
    final, source_counts, target_counts, used_blocks, used_pairs = [], Counter(), Counter(), set(), set()
    for row in rows:
        source, target = row["source_url"], row["destination_url"]
        block = (source, row["source_locator"])
        if row["id"] in ambiguous_ids or block in used_blocks or (source, target) in used_pairs:
            continue
        if source_counts[source] >= int(options.get("links_per_source", 3)) or target_counts[target] >= int(options.get("links_per_target", 5)):
            continue
        final.append(row)
        used_blocks.add(block)
        used_pairs.add((source, target))
        source_counts[source] += 1
        target_counts[target] += 1
        if len(final) >= int(options.get("recommendation_cap", 300)):
            break
    if ambiguous_ids:
        warnings.append("Some exact query placements matched competing destination pages and were omitted when context could not clearly select one.")
    if truncated:
        warnings.append("The exact-match candidate limit was reached. Query coverage is partial for this run.")
    save_dataset(profile, "recommendations", final, input_signature=input_signature(profile, REC_INPUTS), settings=options,
                 matching_strategy="gsc_exact_queries", query_data_available=bool(query_doc["rows"]), query_rows_loaded=len(query_doc["rows"]),
                 query_pairs_eligible=len(inventory), query_pairs_checked=checked, candidate_links=len(rows), ambiguous_placements_skipped=len(ambiguous_ids),
                 eligible_targets=len(targets), targets_checked=len(targets), paragraphs_checked=paragraph_count,
                 partial=truncated or total_paragraphs > paragraph_count or dataset(profile, "pages")["meta"].get("partial", False)
                         or dataset(profile, "content")["meta"].get("partial", False), warnings=list(dict.fromkeys(warnings)))
    log(f"Saved {len(final):,} GSC query-based recommendations from {checked:,} query/page pairs.")


def page_summary(profile, state=None, metric_data=None):
    profile = PreparedProfile(profile)
    state = state if state is not None else graph_state(profile)
    metrics, _ = metric_data if metric_data is not None else metric_maps(profile, state["aliases"])
    core = core_mapping(profile, state["aliases"])
    rows = []
    for u in sorted(state["graph"].nodes):
        p = state["pages"].get(u, {})
        m = metrics.get(u)
        rows.append({"client": profile["name"], "url": u, "title": p.get("title", ""), "h1": p.get("h1", ""),
                     "page_type": "Homepage" if is_home(u, profile) else "Core" if u in core else "Blog" if is_blog(u, profile) else "Other",
                     "topic": core.get(u, {}).get("topic", ""), "business_priority": core.get(u, {}).get("priority", 1),
                     "status_code": p.get("status") or None, "indexable": p.get("indexable") if p else None,
                     "crawl_depth_from_home": state["depths"].get(u), "reachable_from_home": u in state["depths"],
                     "unique_inlink_sources": len(state["in_sources"].get(u, set())),
                     "unique_contextual_sources": len(state["contextual_sources"].get(u, set())) if state["position_available"] else None,
                     "internal_rank_model": round(state["rank"].get(u, 0), 8),
                     "nonbrand_impressions": m.get("impressions") if m else None, "nonbrand_clicks": m.get("clicks") if m else None,
                     "nonbrand_position": m.get("position") if m else None, "gsc_data_available": m is not None,
                     "invalid_canonical": p.get("invalid_canonical", ""),
                     "validation": "Crawled" if p else "Known URL; not validated in crawl"})
    return rows


def audit_links(profile, options, log, check_cancel, state=None, metric_data=None):
    profile = PreparedProfile(profile)
    state = state if state is not None else graph_state(profile)
    core = core_mapping(profile, state["aliases"])
    selected = set(options.get("audit_checks", list(AUDITS)))
    rows = []

    def issue(kind, destination, detail, action, severity="Review", source="", anchor="", **extra):
        rows.append({"client": profile["name"], "issue": kind, "priority": severity, "source_url": source,
                     "destination_url": destination, "anchor_text": anchor, "evidence": detail, "recommended_action": action, **extra})

    summary = page_summary(profile, state, metric_data)
    home_page = state["pages"].get(state["home"], {})
    reachability_known = home_page.get("status") == 200 and bool(home_page.get("html"))
    for row in summary:
        check_cancel()
        u = row["url"]
        if is_home(u, profile) or excluded(u, profile):
            continue
        p = state["pages"].get(u, {})
        if reachability_known and "orphans" in selected and not row["reachable_from_home"] and (not p or (p.get("html") and p.get("indexable") and p.get("status") == 200)):
            issue("Potential orphan", u, f"No observed followed HTML path from the homepage; {row['unique_inlink_sources']} incoming source(s) may belong to an isolated group. " + row["validation"],
                  "Validate the page and crawl coverage; add a relevant contextual or hub link if the page should be discoverable.", "High" if u in core else "Review")
        if reachability_known and u in core and "buried" in selected:
            depth = row["crawl_depth_from_home"]
            if depth is None or depth >= int(options.get("depth_threshold", 4)):
                issue("Core page unreachable from home" if depth is None else "Buried core page", u,
                      f"Shortest followed HTML hyperlink path from configured homepage: {depth if depth is not None else 'not found'}. Imported/sitemap seeds do not count as paths.",
                      "Review navigation and relevant hub pages, then add a shorter useful path.", "High", depth=depth)
        if u in core and "support" in selected and row["unique_contextual_sources"] is not None and row["unique_contextual_sources"] < int(options.get("minimum_contextual_sources", 2)):
            issue("Weak contextual support", u, f"{row['unique_contextual_sources']} unique contextual source pages; {row['unique_inlink_sources']} total source pages.",
                  "Review related blog paragraphs and hub copy for useful contextual links.", "High" if core[u].get("priority", 1) >= 4 else "Medium")
    if "canonicals" in selected:
        for p in state["pages"].values():
            if p.get("invalid_canonical"):
                reason = str(p.get("indexability_status", "")).replace("Invalid canonical: target ", "")
                issue("Invalid canonical tag", p["url"], f"The canonical tag points to {p['invalid_canonical']}, which {reason}. The tool treats this page as indexable; search engines may not.",
                      "Change the canonical tag to this page's own URL (or to the correct live page).", "High" if p["url"] in core else "Review")
    robots_skipped = 0
    for link in dataset(profile, "links")["rows"]:
        check_cancel()
        d = link["destination"]
        p = state["pages"].get(d, {})
        anchor = text_norm(link.get("anchor") or link.get("alt"))
        if "anchors" in selected and (link.get("contextual") or not link.get("position_known")):
            if not anchor or anchor.casefold() in GENERIC_ANCHORS or re.match(r"^(?:https?://|www\.)", anchor, re.I):
                issue("Potentially vague / missing contextual anchor", d,
                      f"Anchor: {anchor or '(empty, no alt text)'}; position: {link.get('position') or 'unknown'}. Evaluate CTA labels separately.",
                      "Review the sentence and use an accurate descriptive phrase where appropriate.", "Review", link["source"], anchor,
                      link_position=link.get("position", ""), locator=link.get("locator", ""))
        if "destinations" in selected and p:
            if p.get("robots_blocked"):
                robots_skipped += 1
                continue
            status = p.get("status", 0)
            kind = "Could not verify destination" if status in {0, 401, 403, 429} else "Broken destination" if status >= 400 else "Redirected destination" if 300 <= status < 400 else "Non-indexable HTML destination" if p.get("html") and not p.get("indexable") else ""
            if kind:
                issue(kind, d, f"{'No HTTP response' if status == 0 else f'HTTP {status}'}; {p.get('indexability_status', '')}",
                      "Retry or verify manually before changing this link." if status in {0, 401, 403, 429} else "Review the intended destination; update the href to the valid preferred URL when appropriate.",
                      "High" if status in {404, 410} else "Review" if status in {401, 403, 429} else "High" if status >= 400 else "Review", link["source"], anchor,
                      preferred_url=resolve_alias(d, state["aliases"]), link_position=link.get("position", ""))
    # Core URLs absent from every discovery source remain visible for investigation.
    known = {r["url"] for r in summary}
    for u in core:
        if u not in known:
            issue("Approved core page absent from inventory", u, "The approved URL is absent from crawl, sitemap and available GSC page inventory.",
                  "Check the URL, crawl scope, redirects and sitemap inclusion before recommending links.", "High")
    warnings = list(dataset(profile, "links")["meta"].get("warnings", []))
    if robots_skipped:
        warnings.append(f"{robots_skipped:,} link(s) point to URLs that robots.txt asks crawlers to skip; they were not checked and are not reported as broken.")
    if not reachability_known:
        warnings.append("The homepage was not verified as readable HTML. Orphan and buried-page findings are withheld until reachability can be measured.")
    if not dataset(profile, "sitemaps")["meta"]:
        warnings.append("Sitemap discovery has not been run. Orphan coverage is limited to the available crawl/GSC inventory.")
    save_dataset(profile, "audit", rows, input_signature=input_signature(profile, AUDIT_INPUTS), settings=options, warnings=warnings,
                 coverage="Findings describe this configured crawl and known URL inventory, not proof of a complete website crawl.")
    save_dataset(profile, "page_summary", summary, input_signature=input_signature(profile, AUDIT_INPUTS))
    log(f"Saved {len(rows):,} audit findings and {len(summary):,} page summaries.")


INSIGHT_BASE_INPUTS = ["pages", "links", "content", "gsc_pages", "gsc_total_pages", "gsc_queries", "sitemaps"]
INSIGHT_INPUTS = INSIGHT_BASE_INPUTS + ["recommendations"]
INSIGHT_FILTERS = ["Under-supported core", "No contextual inlinks", "Navigation/footer only", "Potential orphan",
                   "Isolated group", "Buried core", "Missing hub link", "Invalid canonical", "Cross-topic link review",
                   "Link concentration", "Unassigned topic"]
EMERGENT_SIMILARITY = .25


def insight_settings(profile):
    value = copy.deepcopy(read_json(client_dir(profile) / "topic_settings.json", {}) or {})
    return {"names": value.get("names", {}), "assignments": value.get("assignments", {}),
            "hubs": value.get("hubs", {}), "custom_clusters": value.get("custom_clusters", [])}


def _file_stamps(profile, names):
    stamps = {}
    for name in names:
        path = client_dir(profile) / f"{name}.json"
        try:
            stat = path.stat()
            stamps[name] = (stat.st_mtime_ns, stat.st_size)
        except FileNotFoundError:
            stamps[name] = None
    return stamps


def insight_base_signature(profile):
    """Crawl-derived inputs only; cluster edits and reviews do not invalidate the base."""
    return digest({"version": INSIGHT_VERSION, "profile": dict(profile), "files": _file_stamps(profile, INSIGHT_BASE_INPUTS)})


def insight_signature(profile):
    # File stamps keep view changes cheap; no corpus hashing or network requests.
    return digest({"version": INSIGHT_VERSION, "profile": dict(profile), "files": _file_stamps(profile, INSIGHT_INPUTS + ["topic_settings", "reviews"])})


def finite_number(value, default=None):
    try:
        number = float(value)
        return number if math.isfinite(number) else default
    except (TypeError, ValueError):
        return default


def insight_documents(profile, summary, content, queries):
    documents = []
    for row in summary:
        body = content.get(row["url"], {})
        headings = " ".join([row.get("topic", ""), body.get("title", row.get("title", "")), body.get("h1", row.get("h1", ""))])
        query_text = " ".join(q["query"] for q in queries.get(row["url"], [])[:20])
        text = " ".join(body.get("text", "").split()[:600])
        path = urlsplit(row["url"]).path.replace("-", " ").replace("/", " ")
        documents.append(without_brand(" ".join([headings] * 3 + [query_text] * 2 + [text, path]), profile))
    return documents


def build_explorer_base(profile, log=lambda *_: None, check_cancel=lambda: None, state=None, metric_data=None):
    """Expensive, crawl-derived structures: link graph, page vectors, edges, paths."""
    import networkx as nx
    from sklearn.feature_extraction.text import TfidfVectorizer
    signature = insight_base_signature(profile)
    profile = PreparedProfile(profile)
    state = state if state is not None else graph_state(profile)
    metrics, queries = metric_data if metric_data is not None else metric_maps(profile, state["aliases"])
    root_page = state["pages"].get(state["home"], {})
    reachability_known = root_page.get("status") == 200 and bool(root_page.get("html"))
    summary = page_summary(profile, state, (metrics, queries))
    by_url = {r["url"]: r for r in summary}
    content = {resolve_alias(r["url"], state["aliases"]): r for r in dataset(profile, "content")["rows"] if r.get("success")}
    log(f"Reading {len(summary):,} known pages for topics: body content, headings and visible GSC query themes.")
    documents = insight_documents(profile, summary, content, queries)
    url_indices = {r["url"]: i for i, r in enumerate(summary)}
    vectorizer, vectors = None, None
    if summary:
        try:
            vectorizer = TfidfVectorizer(tokenizer=meaningful_tokens, token_pattern=None, ngram_range=(1, 2),
                                         max_features=40000, sublinear_tf=True, dtype=np.float32)
            vectors = vectorizer.fit_transform(documents)
        except ValueError:
            vectorizer, vectors = None, None
    valid = {u: r["status_code"] == 200 and bool(r["indexable"]) and bool(state["pages"].get(u, {}).get("html")) for u, r in by_url.items()}
    # Aggregate raw links by source/destination, retaining link-position evidence.
    edge_map, unknown_in, templates_in = {}, defaultdict(set), defaultdict(set)
    for link in dataset(profile, "links")["rows"]:
        check_cancel()
        source, target = resolve_alias(link["source"], state["aliases"]), resolve_alias(link["destination"], state["aliases"])
        if target in by_url and not link.get("position_known"):
            unknown_in[target].add(source)
        if source == target or source not in by_url or target not in by_url:
            continue
        pair = source, target
        edge = edge_map.setdefault(pair, {"source": source, "destination": target, "contextual": False, "template": False, "unknown_position": False, "followable": False, "anchors": []})
        edge["contextual"] |= bool(link.get("contextual"))
        edge["followable"] |= bool(link.get("followable")) and valid[source]
        position = str(link.get("position", "")).lower()
        template = any(word in position for word in ("navigation", "footer", "header", "menu")) and not link.get("contextual")
        edge["template"] |= template
        if template:
            templates_in[target].add(source)
        if not link.get("position_known"):
            edge["unknown_position"] = True
            unknown_in[target].add(source)
        anchor = text_norm(link.get("anchor", ""))
        if anchor and anchor not in edge["anchors"] and len(edge["anchors"]) < 5:
            edge["anchors"].append(anchor)
    edges = list(edge_map.values())
    incoming_context, outgoing_context = defaultdict(set), defaultdict(set)
    for edge in edges:
        if edge["contextual"]:
            incoming_context[edge["destination"]].add(edge["source"])
            outgoing_context[edge["source"]].add(edge["destination"])
    unreachable = set(state["graph"]) - set(state["depths"])
    isolated_groups = {}
    for index, group in enumerate(nx.weakly_connected_components(state["graph"].subgraph(unreachable)), 1):
        for url in group:
            isolated_groups[url] = (index, len(group))
    parent = {v: u for u, v in nx.bfs_edges(state["graph"], state["home"])} if state["home"] in state["graph"] else {}
    return {"signature": signature, "state": state, "metrics": metrics, "queries": queries, "summary": summary,
            "content_urls": set(content), "content_words": {u: len(r.get("text", "").split()) for u, r in content.items()},
            "documents": documents, "vectorizer": vectorizer, "vectors": vectors, "url_indices": url_indices, "valid": valid,
            "edges": edges, "unknown_in": unknown_in, "templates_in": templates_in, "incoming_context": incoming_context,
            "outgoing_context": outgoing_context, "isolated_groups": isolated_groups, "parent": parent,
            "reachability_known": reachability_known}


def emergent_label(url, by_url, queries, profile):
    top = next((q for q in queries.get(url, []) if finite_number(q.get("impressions"), 0) >= 10), None)
    if top:
        return top["query"]
    row = by_url.get(url, {})
    label = without_brand(row.get("h1") or row.get("title") or "", profile)
    if label:
        return label[:60]
    return urlsplit(url).path.strip("/").split("/")[-1].replace("-", " ") or url


def emergent_topics(pool, vectors, url_indices, by_url, queries, profile, threshold=EMERGENT_SIMILARITY, cap=3000):
    """Group pages that fit no core page with each other. The most-visible page leads each group."""
    if vectors is None or len(pool) < 2:
        return {}
    pool = sorted(pool, key=lambda u: (finite_number(by_url[u]["nonbrand_impressions"], 0), by_url[u]["unique_inlink_sources"], u), reverse=True)[:cap]
    matrix = vectors[[url_indices[u] for u in pool]]
    similarities = (matrix @ matrix.T).toarray()
    leaders, owner = [], {}
    for i in range(len(pool)):
        if leaders:
            row = similarities[i, leaders]
            best = int(np.argmax(row))
            if row[best] >= threshold:
                owner[i] = leaders[best]
                continue
        leaders.append(i)
        owner[i] = i
    groups = defaultdict(list)
    for i, lead in owner.items():
        groups[lead].append(pool[i])
    topics = {}
    for lead, members in groups.items():
        if len(members) >= 2:
            leader = pool[lead]
            topics["topic_" + digest(leader)[:12]] = {"leader": leader, "members": members, "label": emergent_label(leader, by_url, queries, profile)}
    return topics


def build_explorer_data(profile, log=lambda *_: None, check_cancel=lambda: None, state=None, metric_data=None, base=None):
    """Cluster assignments, page decisions and cluster health. Cheap when a base is supplied."""
    signature = insight_signature(profile)
    profile = PreparedProfile(profile)
    base = base if base is not None else build_explorer_base(profile, log, check_cancel, state, metric_data)
    state, queries = base["state"], base["queries"]
    summary = [dict(r) for r in base["summary"]]
    by_url = {r["url"]: r for r in summary}
    reachability_known = base["reachability_known"]
    settings = insight_settings(profile)
    core = core_mapping(profile, state["aliases"])
    definitions = {}
    for url, entry in core.items():
        if url not in by_url or is_home(url, profile):
            continue
        cid = "core_" + digest(url)[:12]
        label = entry.get("topic") or by_url[url].get("h1") or urlsplit(url).path.strip("/").replace("-", " ")
        definitions[cid] = {"id": cid, "name": settings["names"].get(cid, label), "default_hub": url, "type": "Core page"}
    for entry in settings["custom_clusters"]:
        if entry.get("id") and text_norm(entry.get("name", "")):
            cid = entry["id"]
            definitions[cid] = {"id": cid, "name": settings["names"].get(cid, entry["name"]), "default_hub": entry.get("hub", ""), "type": "Custom"}
    url_indices, vectors, vectorizer = base["url_indices"], base["vectors"], base["vectorizer"]
    topic_ids = list(definitions)
    primary, secondary, confidence = {}, {}, {}
    if summary and topic_ids and vectors is not None:
        topic_documents = []
        for cid in topic_ids:
            definition = definitions[cid]
            hub = settings["hubs"].get(cid, definition["default_hub"])
            topic_documents.append(" ".join([without_brand(definition["name"], profile)] * 6 +
                                            ([base["documents"][url_indices[hub]]] if hub in url_indices else [])))
        centers = vectorizer.transform(topic_documents)
        for start in range(0, len(summary), 128):
            check_cancel()
            scores = (vectors[start:start + 128] @ centers.T).toarray()
            for offset, score in enumerate(scores):
                url = summary[start + offset]["url"]
                best = np.argsort(score)[::-1][:2]
                first = float(score[best[0]])
                primary[url] = topic_ids[int(best[0])] if first >= .12 else "unassigned"
                confidence[url] = "High" if first >= .35 and (len(best) == 1 or first - float(score[best[1]]) >= .06) else "Review" if first >= .12 else "Unassigned"
                if len(best) > 1 and float(score[best[1]]) >= max(.12, first * .75):
                    secondary[url] = topic_ids[int(best[1])]
    # Core pages start as explicit hubs; users can correct memberships and hubs.
    for cid, definition in definitions.items():
        hub = definition["default_hub"]
        if hub in by_url:
            primary[hub], confidence[hub] = cid, "Core hub"
    manual = {resolve_alias(url_key(u), state["aliases"]): cid for u, cid in settings["assignments"].items()}
    # Topics without a core page: group the remaining pages with each other.
    pool = [r["url"] for r in summary if primary.get(r["url"], "unassigned") == "unassigned" and r["url"] not in manual
            and base["valid"].get(r["url"]) and r["page_type"] != "Homepage" and r["url"] in base["content_urls"]
            and not excluded(r["url"], profile) and not is_archive(r["url"])]
    for cid, topic in emergent_topics(pool, vectors, url_indices, by_url, queries, profile).items():
        definitions[cid] = {"id": cid, "name": settings["names"].get(cid, topic["label"]), "default_hub": topic["leader"], "type": "Inferred topic"}
        for url in topic["members"]:
            primary[url], confidence[url] = cid, "Inferred topic"
    for url, cid in manual.items():
        if url in by_url and (cid in definitions or cid == "unassigned"):
            primary[url], confidence[url] = cid, "Reviewed"
            secondary.pop(url, None)
    for cid, url in settings["hubs"].items():
        url = resolve_alias(url_key(url), state["aliases"])
        if cid in definitions and url in by_url:
            primary[url], confidence[url] = cid, "Reviewed hub"
    content_words, content_urls = base["content_words"], base["content_urls"]
    for row in summary:
        url = row["url"]
        row["cluster_id"] = primary.get(url, "unassigned")
        row["cluster"] = definitions.get(row["cluster_id"], {}).get("name", "Unassigned")
        row["secondary_cluster_id"] = secondary.get(url, "")
        row["cluster_confidence"] = confidence.get(url, "Unassigned")
        row["content_available"] = url in content_urls
        if url not in content_urls and row["cluster_confidence"] in {"High", "Review"}:
            row["cluster_confidence"] = "Limited: title/URL only"
        row["valid_html"] = base["valid"].get(url, False)
        row["word_count"] = content_words.get(url, 0)
        row["active"] = not is_home(url, profile) and not excluded(url, profile) and (row["valid_html"] or row["status_code"] is None)
        row["query_opportunities"] = sum(1 for q in queries.get(url, []) if 4 <= finite_number(q.get("position"), 0) <= 30 and finite_number(q.get("impressions"), 0) > 0)
        row["query_opportunity_impressions"] = sum(float(q["impressions"]) for q in queries.get(url, []) if 4 <= finite_number(q.get("position"), 0) <= 30)
        row["top_queries"] = queries.get(url, [])[:10]
    edges, unknown_in, templates_in = base["edges"], base["unknown_in"], base["templates_in"]
    incoming_context, outgoing_context, isolated_groups = base["incoming_context"], base["outgoing_context"], base["isolated_groups"]
    review_state = read_json(client_dir(profile) / "reviews.json", {})
    recommendations = [{**r, **review_state.get(r["id"], {})} for r in dataset(profile, "recommendations")["rows"]]
    recommendations = [r for r in recommendations if r.get("status") not in {"Dismissed", "Implemented"}]
    proposed = defaultdict(list)
    for rec in recommendations:
        proposed[resolve_alias(rec["destination_url"], state["aliases"])].append(rec)
    hubs = {}
    for cid, definition in definitions.items():
        requested = settings["hubs"].get(cid, definition["default_hub"])
        if cid in settings["hubs"] and not requested:
            hubs[cid] = ""
        elif requested in by_url and by_url[requested]["valid_html"] and primary.get(requested) == cid:
            hubs[cid] = requested
        else:
            alternatives = [r for r in summary if r["cluster_id"] == cid and r["page_type"] == "Core" and r["valid_html"]]
            hubs[cid] = max(alternatives, key=lambda r: r["business_priority"])["url"] if alternatives else ""
    related_members, primary_members = defaultdict(set), defaultdict(list)
    for member in summary:
        primary_members[member["cluster_id"]].append(member)
        if member["valid_html"] and member["page_type"] != "Homepage":
            for cid in {member["cluster_id"], member["secondary_cluster_id"]} - {"", "unassigned"}:
                related_members[cid].add(member["url"])
    for row in summary:
        check_cancel()
        url, cid = row["url"], row["cluster_id"]
        context_known = bool(state["position_available"]) and not unknown_in[url]
        row.update(context_evidence="Complete in snapshot" if context_known else "Unknown/partial", hub_url=hubs.get(cid, ""),
                   contextual_outlinks=len(outgoing_context[url]) if state["position_available"] else None,
                   navigation_footer_sources=len(templates_in[url]), proposed_links=len(proposed[url]),
                   orphan_group=isolated_groups.get(url, (None, 0))[0], orphan_group_size=isolated_groups.get(url, (None, 0))[1])
        row["is_hub"] = bool(row["hub_url"] == url)
        members = related_members[cid] - {url} if cid != "unassigned" else set()
        row["related_pages"] = len(members)
        row["missing_related_sources"] = sum(1 for source in members if (source, url) not in state["blocked_pairs"])
        flags = []
        contextual = row["unique_contextual_sources"]
        if row["active"]:
            if reachability_known and not row["reachable_from_home"]:
                flags.append("Potential orphan")
                if row["orphan_group_size"] > 1:
                    flags.append("Isolated group")
            if context_known and contextual == 0:
                flags.append("No contextual inlinks")
                if row["unique_inlink_sources"] > 0 and len(templates_in[url]) == row["unique_inlink_sources"]:
                    flags.append("Navigation/footer only")
            threshold = max(2, math.ceil(.2 * len(members)))
            row["context_review_threshold"] = threshold
            if row["page_type"] == "Core" and context_known and contextual < threshold:
                flags.append("Under-supported core")
            if row["page_type"] == "Core" and row["crawl_depth_from_home"] is not None and row["crawl_depth_from_home"] >= 4:
                flags.append("Buried core")
            hub = row["hub_url"]
            if hub and hub != url and row["valid_html"] and (url, hub) not in state["blocked_pairs"]:
                flags.append("Missing hub link")
            if row.get("invalid_canonical"):
                flags.append("Invalid canonical")
            if cid == "unassigned":
                flags.append("Unassigned topic")
        row["flags"] = flags
        row["link_density"] = 1000 * len(outgoing_context[url]) / row["word_count"] if row["word_count"] >= 100 else None
    # Relative outliers are review signals, never an automatic "too many links" rule.
    for role in {r["page_type"] for r in summary}:
        peers = [r for r in summary if r["active"] and r["valid_html"] and r["page_type"] == role and r["context_evidence"] == "Complete in snapshot"]
        for field in ["unique_contextual_sources", "link_density"]:
            values = [float(r[field]) for r in peers if r.get(field) is not None]
            if len(values) < 5:
                continue
            q1, median, q3 = np.percentile(values, [25, 50, 75])
            threshold = max(q3 + 1.5 * (q3 - q1), median * 3, 10 if field == "unique_contextual_sources" else 5)
            for row in peers:
                if row.get(field) is not None and row[field] > threshold:
                    if "Link concentration" not in row["flags"]:
                        row["flags"].append("Link concentration")
                    row.setdefault("concentration_evidence", []).append(f"{field}: {row[field]:.1f}; peer review threshold: {threshold:.1f}.")
    cross_reviews = []
    for edge in edges:
        source, target = edge["source"], edge["destination"]
        left, right = by_url[source], by_url[target]
        if not edge["contextual"] or not left["valid_html"] or not right["valid_html"]:
            continue
        memberships_left = {left["cluster_id"], left["secondary_cluster_id"]} - {"", "unassigned"}
        memberships_right = {right["cluster_id"], right["secondary_cluster_id"]} - {"", "unassigned"}
        if not memberships_left or not memberships_right or memberships_left & memberships_right or vectors is None:
            continue
        similarity = float(vectors[url_indices[source]].multiply(vectors[url_indices[target]]).sum())
        if similarity < .06 and len(cross_reviews) < 5000:
            cross_reviews.append({"source_url": source, "destination_url": target, "source_cluster": left["cluster"], "destination_cluster": right["cluster"],
                                  "anchors": edge["anchors"], "content_similarity": round(similarity, 4),
                                  "action": "Review the linking sentence. Cross-cluster links can be useful; do not remove based on this signal alone."})
            if left["active"] and "Cross-topic link review" not in left["flags"]:
                left["flags"].append("Cross-topic link review")
    for row in summary:
        flags = row["flags"]
        score = (30 * ("Under-supported core" in flags) + 20 * ("Potential orphan" in flags) + 15 * ("Invalid canonical" in flags)
                 + 12 * ("Navigation/footer only" in flags) + 10 * ("Buried core" in flags) + 8 * ("Missing hub link" in flags)
                 + 5 * min(5, row["proposed_links"]) + 5 * min(4, row["query_opportunities"]) + 2 * row["business_priority"])
        row["review_priority"] = round(min(100, score), 1) if flags else 0
        if not row["active"]:
            row["next_action"] = "Validate status/indexability before considering internal-link changes."
        elif row["status_code"] is None:
            row["next_action"] = "Validate this known URL and crawl coverage before confirming it is orphaned."
        elif "Invalid canonical" in flags:
            row["next_action"] = "Fix the canonical tag first: it points to a URL that is broken, redirects or is noindex."
        elif row["proposed_links"]:
            row["next_action"] = f"Review {row['proposed_links']} verified source/anchor placement(s) for this page."
        elif "Potential orphan" in flags:
            row["next_action"] = "Review the isolated page/group and add a useful path from a reachable relevant page."
        elif "Missing hub link" in flags:
            row["next_action"] = "Review this page's body content for a useful link to its cluster hub."
        elif "Under-supported core" in flags or "No contextual inlinks" in flags:
            row["next_action"] = "Review relevant supporting pages for contextual links; an existing exact anchor is still required for an automatic placement."
        elif "Link concentration" in flags:
            row["next_action"] = "Review link relevance and distribution against comparable pages; high counts alone are not a fault."
        elif "Unassigned topic" in flags:
            row["next_action"] = "Check the page's topic and assign a cluster if a useful fit exists."
        else:
            row["next_action"] = "Review the flagged links and their surrounding text."
    clusters = []
    for cid, definition in definitions.items():
        members = [r for r in primary_members[cid] if r["active"]]
        hub = hubs.get(cid, "")
        support = [r for r in members if r["url"] != hub and r["valid_html"]]
        linked_to = sum((r["url"], hub) in state["blocked_pairs"] and r["url"] in incoming_context[hub] for r in support) if hub else 0
        linked_from = sum(r["url"] in outgoing_context[hub] for r in support) if hub else 0
        unknown_support = sum(r["url"] in unknown_in[hub] for r in support) if hub else 0
        known_metrics = [r for r in members if r["gsc_data_available"]]
        issues = []
        if definition["type"] == "Inferred topic":
            issues.append("No core page leads this topic")
        if not hub:
            issues.append("No confirmed main page")
        if not support:
            issues.append("No validated supporting pages assigned")
        if support and hub and state["position_available"] and not unknown_support and linked_to / len(support) < .5:
            issues.append("Most supporting pages have no observed contextual hub link")
        if unknown_support:
            issues.append("Some hub link positions need review")
        if not state["position_available"]:
            issues.append("Contextual link positions unavailable")
        if any("Potential orphan" in r["flags"] for r in members):
            issues.append("Contains unreachable pages")
        if definition["type"] == "Inferred topic":
            next_action = "Decide whether this topic needs a core page, or link these pages to the closest existing core page."
        elif not hub:
            next_action = "Choose and validate the appropriate main page."
        elif issues:
            next_action = "Review missing support links and the hub's useful onward links."
        else:
            next_action = "Review specific query opportunities; no broad cluster-structure issue was observed."
        clusters.append({"cluster_id": cid, "cluster": definition["name"], "type": definition["type"], "hub_url": hub, "pages": len(members), "support_pages": len(support),
                         "support_linking_to_hub": linked_to if state["position_available"] else None,
                         "hub_linking_to_support": linked_from if state["position_available"] else None,
                         "hub_support_percent": round(100 * linked_to / len(support), 1) if support and hub and state["position_available"] and not unknown_support else None,
                         "link_position_uncertain_pages": unknown_support, "gsc_pages_with_data": len(known_metrics),
                         "page_impressions_sum": sum(r["nonbrand_impressions"] for r in known_metrics) if known_metrics else None,
                         "query_opportunities": sum(r["query_opportunities"] for r in members),
                         "verified_link_opportunities": sum(r["proposed_links"] for r in members),
                         "unreachable_pages": sum("Potential orphan" in r["flags"] for r in members),
                         "zero_context_pages": sum("No contextual inlinks" in r["flags"] for r in members),
                         "needs_attention": bool(issues), "issues": issues, "next_action": next_action})
    warnings = ["Clusters are inferred from available content, headings and visible GSC queries; review memberships and main pages.",
                "Inferred topics group pages that fit no core page; each may need a core page or links to an existing one.",
                "Coverage and contextual connectivity are measured separately. No Google topical-authority score is estimated.",
                "Orphan/unreachable flags describe the available crawl and known URL inventory; isolated pages can link to one another.",
                "Link concentration and cross-topic flags require human review; they are not instructions to remove links."]
    partial = bool(dataset(profile, "pages")["meta"].get("partial") or dataset(profile, "content")["meta"].get("partial"))
    if partial:
        warnings.append("Crawl coverage is partial. Missing pages or links can change the findings.")
    if not state["position_available"]:
        warnings.append("Link-position evidence is unavailable. Zero-context and navigation-only claims are withheld.")
    if not reachability_known:
        warnings.append("The homepage was not validated as accessible HTML. Orphan classification is withheld until the root crawl is checked.")
    result = {"meta": {"signature": signature, "created_at": utc_now(), "version": INSIGHT_VERSION, "partial": partial, "warnings": warnings,
                       "home": state["home"], "reachability_known": reachability_known, "known_pages": len(summary), "validated_pages": sum(r["valid_html"] for r in summary)},
              "pages": summary, "clusters": clusters, "links": edges, "cross_reviews": cross_reviews,
              "recommendations": recommendations, "parents": base["parent"]}
    for name, rows in [("insight_pages", summary), ("insight_clusters", clusters), ("insight_reviews", cross_reviews)]:
        save_dataset(profile, name, rows, insight_signature=signature, partial=partial, warnings=warnings)
    atomic_json(client_dir(profile) / "explorer_snapshot.json", result)
    atomic_json(client_dir(profile) / "explorer_manifest.json", result["meta"])
    log(f"Prepared {len(clusters):,} topic clusters and {len(summary):,} page decisions from the full available snapshot.")
    return result


def filter_insight_pages(snapshot, issues=None, page_type="All", clusters=None, search=""):
    return [r for r in snapshot["pages"] if r["active"] and (not issues or set(issues) & set(r["flags"]))
            and (page_type == "All" or r["page_type"] == page_type)
            and (not clusters or r["cluster_id"] in clusters or r["secondary_cluster_id"] in clusters)
            and (not search or search.casefold() in (r["url"] + " " + r["title"] + " " + r["cluster"]).casefold())]


def seed_cluster_check(profile, seeds, snapshot):
    """Explore supplied topics in saved content. No crawl or keyword-volume API."""
    from sklearn.feature_extraction.text import TfidfVectorizer
    seeds = list(dict.fromkeys(text_norm(s) for s in seeds if text_norm(s)))[:20]
    pages = [r for r in snapshot["pages"] if r["active"] and r["valid_html"]]
    aliases = aliases_for(dataset(profile, "pages")["rows"], profile)
    content = {resolve_alias(r["url"], aliases): r for r in dataset(profile, "content")["rows"] if r.get("success")}
    _, queries = metric_maps(profile, aliases)
    docs = insight_documents(profile, pages, content, queries)
    results, details = [], []
    scores = np.zeros((len(seeds), len(pages)))
    if seeds and pages:
        try:
            matrix = TfidfVectorizer(tokenizer=meaningful_tokens, token_pattern=None, ngram_range=(1, 2), max_features=40000).fit_transform(docs + seeds)
            scores = (matrix[len(docs):] @ matrix[:len(docs)].T).toarray()
        except ValueError:
            pass
    for i, seed in enumerate(seeds):
        hits = []
        pattern = phrase_pattern(seed)
        for j, page in enumerate(pages):
            exact = bool(pattern.search(content.get(page["url"], {}).get("text", "") + " " + page["title"] + " " + page["h1"]))
            matching_queries = [q for q in queries.get(page["url"], []) if pattern.search(q["query"])]
            score = float(scores[i, j])
            if score >= .12 or exact or matching_queries:
                hits.append({**page, "seed": seed, "topic_similarity": round(score, 4), "exact_phrase_in_content": exact,
                             "visible_matching_queries": len(matching_queries), "matching_query_impressions": sum(q["impressions"] for q in matching_queries),
                             "match_evidence": "GSC query" if matching_queries else "Existing phrase" if exact else "Inferred content similarity"})
        hits.sort(key=lambda r: (r["visible_matching_queries"] > 0, r["topic_similarity"]), reverse=True)
        hubs = [r for r in hits if r["page_type"] == "Core" or r["is_hub"]]
        hub = hubs[0] if hubs else None
        status = "Main page and supporting content found" if hub and len(hits) > 1 else "Main page found; little supporting content matched" if hub else "Related content found; review whether a main page is missing" if hits else "No suitable page found in available content"
        results.append({"seed": seed, "finding": status, "candidate_main_page": hub["url"] if hub else "", "related_pages": len(hits),
                        "visible_matching_query_rows": sum(r["visible_matching_queries"] for r in hits),
                        "next_action": "Review the related pages and their connections to the candidate main page." if hub else "Review page intent and business relevance before selecting or creating a main page.",
                        "qualification": "This is a coverage candidate, not verified keyword demand. GSC cannot reveal every missing topic; crawl coverage may be partial."})
        details.extend(hits)
    save_dataset(profile, "seed_checks", results, insight_signature=snapshot["meta"]["signature"], seeds=seeds)
    save_dataset(profile, "seed_pages", details, insight_signature=snapshot["meta"]["signature"], seeds=seeds)
    return results, details


def focus_network(snapshot, focus_url, node_cap=25, include_template=False, show_proposed=True, cluster_ids=None, entire_cluster=False):
    """Bounded display, with all diagnostic counts taken from the full snapshot."""
    import plotly.graph_objects as go
    by_url = {r["url"]: r for r in snapshot["pages"]}
    if focus_url not in by_url:
        raise ValueError("Select a known page to inspect.")
    node_cap = max(2, min(75, int(node_cap)))
    focus = by_url[focus_url]
    allowed = {u for u, r in by_url.items() if r["active"] and (not cluster_ids or r["cluster_id"] in cluster_ids or r["secondary_cluster_id"] in cluster_ids)}
    allowed.add(focus_url)
    home = snapshot["meta"]["home"]
    if home in by_url and any(e["source"] == home and e["destination"] == focus_url and (e["contextual"] or include_template) for e in snapshot["links"]):
        allowed.add(home)
    existing = [e for e in snapshot["links"] if (e["contextual"] or (include_template and (e["template"] or e["unknown_position"])))
                and (entire_cluster or focus_url in {e["source"], e["destination"]}) and e["source"] in allowed and e["destination"] in allowed]
    recs = [r for r in snapshot["recommendations"] if show_proposed and r["source_url"] in allowed and r["destination_url"] in allowed
            and (entire_cluster or focus_url in {r["source_url"], r["destination_url"]})]
    related = {u for u in allowed if focus["cluster_id"] != "unassigned" and (by_url[u]["cluster_id"] == focus["cluster_id"] or by_url[u]["secondary_cluster_id"] == focus["cluster_id"])}
    candidates = set(allowed) if entire_cluster else related | {focus_url}
    for edge in existing:
        candidates.update([edge["source"], edge["destination"]])
    proposed_nodes = set()
    for rec in recs:
        candidates.update([rec["source_url"], rec["destination_url"]])
        proposed_nodes.update([rec["source_url"], rec["destination_url"]])
    contextual_nodes = {u for e in existing if e["contextual"] for u in [e["source"], e["destination"]]}
    order = sorted(candidates - {focus_url}, key=lambda u: (u in proposed_nodes, u in contextual_nodes, by_url[u]["review_priority"], finite_number(by_url[u]["nonbrand_impressions"], 0)), reverse=True)
    shown = [focus_url] + order[:node_cap - 1]
    nodes = set(shown)
    incoming = {e["source"] for e in existing if e["destination"] == focus_url} | {r["source_url"] for r in recs if r["destination_url"] == focus_url}
    left = [u for u in shown[1:] if u in incoming or u in related]
    right = [u for u in shown[1:] if u not in left]
    positions = {focus_url: (0, 0)}
    for group, x in [(left, -1.4), (right, 1.4)]:
        for index, url in enumerate(group):
            positions[url] = (x, (len(group) - 1) / 2 - index)
    figure = go.Figure()
    display_edges = []
    for edge in existing:
        if edge["source"] in nodes and edge["destination"] in nodes:
            display_edges.append({**edge, "kind": "Existing body link" if edge["contextual"] else "Navigation/footer or unknown position"})
    for rec in recs:
        if rec["source_url"] in nodes and rec["destination_url"] in nodes:
            display_edges.append({"source": rec["source_url"], "destination": rec["destination_url"], "kind": "Proposed link", "evidence": rec.get("evidence_type", "Existing phrase"), "anchors": [rec["anchor_text"]], "query_position": rec.get("query_position"), "query_impressions": rec.get("query_impressions")})
    total_visible_edges = len(display_edges)
    display_edges = display_edges[:150]
    styles = {"Existing body link": ("#64748b", "solid"), "Navigation/footer or unknown position": ("#cbd5e1", "dot"), "Proposed link": ("#059669", "dash")}
    for kind, (color, dash) in styles.items():
        values = [e for e in display_edges if e["kind"] == kind]
        if not values:
            continue
        xs, ys = [], []
        for edge in values:
            source, target = positions[edge["source"]], positions[edge["destination"]]
            xs.extend([source[0], target[0], None])
            ys.extend([source[1], target[1], None])
            figure.add_annotation(x=target[0], y=target[1], ax=source[0], ay=source[1], xref="x", yref="y", axref="x", ayref="y",
                                  showarrow=True, arrowhead=2, arrowsize=.7, arrowwidth=1, arrowcolor=color, opacity=.65, standoff=15, startstandoff=13, text="")
        figure.add_trace(go.Scatter(x=xs, y=ys, mode="lines", line=dict(color=color, dash=dash, width=1.3), hoverinfo="skip", name=kind))
    colors = ["#1d4ed8" if u == focus_url else "#dc2626" if "Potential orphan" in by_url[u]["flags"] else "#059669" if u in proposed_nodes else "#d97706" if "Missing hub link" in by_url[u]["flags"] else "#94a3b8" for u in shown]
    labels, hovers = [], []
    for i, url in enumerate(shown):
        row = by_url[url]
        label = row["h1"] or row["title"] or urlsplit(url).path
        labels.append(html_escape(label[:42]) if i < 12 else "")
        hovers.append(f"{html_escape(url)}<br>{html_escape(row['cluster'])}<br>Observed sources: {row['unique_inlink_sources']}<br>Contextual sources: {row['unique_contextual_sources'] if row['unique_contextual_sources'] is not None else 'Unknown'}<br>Queries at positions 4–30: {row['query_opportunities']}<br>Verified placements: {row['proposed_links']}<br>{html_escape('; '.join(row['flags']) or 'No selected issue')}")
    figure.add_trace(go.Scatter(x=[positions[u][0] for u in shown], y=[positions[u][1] for u in shown], mode="markers+text", text=labels,
                               textposition="middle right", textfont=dict(size=11), hovertext=hovers, hoverinfo="text", customdata=shown, name="Pages", showlegend=False,
                               marker=dict(size=[24 if u == focus_url else 14 for u in shown], color=colors,
                                           symbol=["diamond" if u == focus_url else "square" if by_url[u]["page_type"] == "Core" else "circle" for u in shown], line=dict(color="white", width=1.5))))
    figure.update_layout(height=max(430, min(850, 130 + 25 * max(len(left), len(right)))), xaxis=dict(visible=False, range=[-1.8, 2.3]),
                         yaxis=dict(visible=False), margin=dict(l=12, r=20, t=20, b=60), legend=dict(orientation="h", y=-.08),
                         plot_bgcolor="rgba(0,0,0,0)", paper_bgcolor="rgba(0,0,0,0)", hovermode="closest")
    return figure, {"shown_pages": len(shown), "related_pages": len(candidates), "hidden_pages": len(candidates) - len(shown),
                    "hidden_edges": total_visible_edges - len(display_edges), "displayed_links": display_edges, "shown_urls": shown}


def homepage_path(snapshot, focus_url):
    path, seen, url = [], set(), focus_url
    home = snapshot["meta"]["home"]
    while url and url not in seen:
        path.append(url)
        seen.add(url)
        if url == home:
            return list(reversed(path))
        url = snapshot["parents"].get(url)
    return []


def cluster_support_chart(clusters):
    import plotly.express as px
    frame = pd.DataFrame([r for r in clusters if r["hub_support_percent"] is not None])
    if frame.empty:
        return None
    frame = frame.sort_values(["hub_support_percent", "support_pages"], ascending=[True, False]).head(15)
    frame["Review"] = frame["needs_attention"].map({True: "Needs review", False: "No broad issue observed"})
    figure = px.bar(frame, x="hub_support_percent", y="cluster", color="Review", orientation="h",
                    color_discrete_map={"Needs review": "#d97706", "No broad issue observed": "#059669"},
                    hover_data=["support_pages", "support_linking_to_hub", "verified_link_opportunities"],
                    labels={"hub_support_percent": "Supporting pages with observed contextual hub links (%)", "cluster": ""})
    figure.update_layout(height=max(300, 45 * len(frame)), xaxis=dict(range=[0, 100]), yaxis=dict(categoryorder="total ascending"), legend=dict(orientation="h"))
    return figure


def safe_excel(value):
    if isinstance(value, (list, dict)):
        value = json.dumps(value, ensure_ascii=False)
    if isinstance(value, str):
        value = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", value)[:32760]
    return value


def workbook_bytes(profiles, sheets):
    from openpyxl.styles import Font, PatternFill, Alignment
    from openpyxl.utils import get_column_letter
    if not sheets:
        raise ValueError("Select at least one workbook sheet.")
    collected = defaultdict(list)
    for profile in profiles:
        for name in sheets:
            if name == "Run summary":
                for stage in ["pages", "links", "sitemaps", "gsc_pages", "gsc_queries", "content", "recommendations", "audit", "insight_pages", "insight_clusters", "insight_reviews", "seed_checks"]:
                    doc = dataset(profile, stage)
                    if not doc["meta"]:
                        continue
                    stale = stage == "recommendations" and doc["meta"].get("input_signature") != input_signature(profile, REC_INPUTS)
                    stale = stale or (stage == "audit" and doc["meta"].get("input_signature") != input_signature(profile, AUDIT_INPUTS))
                    collected[name].append({"client": profile["name"], "dataset": stage, "rows": len(doc["rows"]), "stale": stale,
                                             "created_at": doc["meta"].get("created_at"), "metadata": doc["meta"]})
                continue
            if name == "Core pages":
                for core in profile.get("core_pages", []):
                    collected[name].append({"client": profile["name"], "url": core["url"], "topic": core.get("topic", ""),
                                            "found_in": core.get("detected_from", ""), "origin": core.get("origin", ""),
                                            "linked_from_pages": core.get("linked_from_pages"), "sitewide_share": core.get("sitewide_share")})
                continue
            key = {"Recommendations": "recommendations", "Existing-link issues": "audit", "Page summary": "page_summary", "GSC pages": "gsc_pages", "GSC queries": "gsc_queries", "Content diagnostics": "content", "Existing links": "links",
                   "Priority pages": "insight_pages", "Topic clusters": "insight_clusters", "Cluster link reviews": "insight_reviews", "Seed checks": "seed_checks"}[name]
            doc = dataset(profile, key)
            values = doc["rows"]
            reviews = read_json(client_dir(profile) / "reviews.json", {}) if key == "recommendations" else {}
            stale = None
            if key in {"recommendations", "audit", "page_summary"}:
                inputs = REC_INPUTS if key == "recommendations" else AUDIT_INPUTS
                stale = doc["meta"].get("input_signature") != input_signature(profile, inputs)
            if key in {"insight_pages", "insight_clusters", "insight_reviews", "seed_checks"}:
                stale = doc["meta"].get("insight_signature") != insight_signature(profile)
            for raw in values:
                row = dict(raw)
                row["client"] = profile["name"]
                if key in {"recommendations", "audit", "page_summary"}:
                    row["analysis_stale"] = stale
                if key in {"insight_pages", "insight_clusters", "insight_reviews", "seed_checks"}:
                    row["analysis_stale"] = stale
                if key == "insight_pages":
                    row = {k: row.get(k) for k in ["client", "url", "page_type", "cluster", "cluster_confidence", "hub_url", "flags", "review_priority", "next_action", "unique_inlink_sources", "unique_contextual_sources", "context_evidence", "navigation_footer_sources", "crawl_depth_from_home", "reachable_from_home", "orphan_group", "orphan_group_size", "related_pages", "proposed_links", "query_opportunities", "nonbrand_impressions", "invalid_canonical", "validation", "analysis_stale"]}
                if key in {"gsc_pages", "gsc_queries"}:
                    row.update(gsc_period_start=doc["meta"].get("start_date", ""), gsc_period_end=doc["meta"].get("end_date", ""),
                               gsc_classification_method=doc["meta"].get("brand_method", ""))
                if key == "recommendations":
                    row.update(reviews.get(row["id"], {}))
                if key == "content":
                    row = {k: row.get(k) for k in ["client", "url", "success", "error", "status", "final_url", "fetched_at", "noindex", "canonical"]}
                collected[name].append(row)
    buffer = io.BytesIO()
    with pd.ExcelWriter(buffer, engine="openpyxl") as writer:
        for sheet in sheets:
            values = collected.get(sheet, [])
            df = pd.DataFrame(values) if values else pd.DataFrame({"Note": ["This selected dataset has no saved rows."]})
            for col in df.select_dtypes(include=["object", "string"]).columns:
                df[col] = df[col].map(safe_excel)
            for part, start in enumerate(range(0, max(1, len(df)), 1_000_000)):
                name = sheet[:27] + (f" {part + 1}" if part else "")
                df.iloc[start:start + 1_000_000].to_excel(writer, sheet_name=name, index=False)
                ws = writer.sheets[name]
                ws.freeze_panes = "A2"
                ws.auto_filter.ref = ws.dimensions
                for cell in ws[1]:
                    cell.font = Font(bold=True, color="FFFFFF")
                    cell.fill = PatternFill("solid", fgColor="163D46")
                for i, column in enumerate(df.columns, 1):
                    ws.column_dimensions[get_column_letter(i)].width = 75 if column in {"context", "reason", "metadata", "evidence"} else 55 if "url" in column else 30
                wrap = len(df) <= 20_000
                for row in ws.iter_rows(min_row=2):
                    for cell in row:
                        if isinstance(cell.value, str):
                            cell.data_type = "s"
                            if wrap:
                                cell.alignment = Alignment(vertical="top", wrap_text=True)
    return buffer.getvalue()


def process_alive(record):
    import psutil
    try:
        process = psutil.Process(int(record["pid"]))
        return process.is_running() and process.status() != psutil.STATUS_ZOMBIE and abs(process.create_time() - float(record["create_time"])) < 2
    except (psutil.Error, KeyError, ValueError):
        return False


def acquire_job_lock(job_id):
    folder = DATA_DIR / "jobs"
    folder.mkdir(parents=True, exist_ok=True)
    lock = folder / "queue.lock"
    # The OS-backed guard is released automatically if a process dies. Metadata
    # appears atomically, so readers never see a newly created empty lock file.
    with FileLock(str(folder / "queue.guard"), timeout=10):
        if lock.exists():
            previous = read_job_lock()
            prior_folder = folder / previous.get("job_id", "unknown")
            status = read_json(prior_folder / "status.json", {})
            process = read_json(prior_folder / "process.json", {})
            age = time.time() - lock.stat().st_mtime
            stopped = process and not process_alive(process)
            finished = status.get("state") in {"completed", "completed_with_errors", "cancelled", "failed"}
            if not (finished or stopped or (not process and age > 30)):
                raise ValueError("A job is already active. Finish or cancel it before starting another run.")
            if status and not finished:
                status.update(state="failed", message="Previous worker stopped unexpectedly.", finished_at=utc_now())
                atomic_json(prior_folder / "status.json", status)
        atomic_json(lock, {"job_id": job_id, "created_at": utc_now()}, private=True)


def release_job_lock(job_id):
    folder = DATA_DIR / "jobs"
    folder.mkdir(parents=True, exist_ok=True)
    with FileLock(str(folder / "queue.guard"), timeout=10):
        if read_job_lock().get("job_id") == job_id:
            (folder / "queue.lock").unlink(missing_ok=True)


def create_job(profiles, stages, options, credentials_info=None, workflow="legacy"):
    import psutil
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    options = {**options, "runtime_mode": deployment_mode()}
    job_id = datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:6]
    acquire_job_lock(job_id)
    folder = DATA_DIR / "jobs" / job_id
    folder.mkdir(parents=True)
    job_path = folder / "job.json"
    atomic_json(job_path, {"id": job_id, "profiles": profiles, "stages": stages, "options": options, "data_dir": str(DATA_DIR), "workflow": workflow})
    atomic_json(folder / "status.json", {"state": "queued", "created_at": utc_now(), "job_id": job_id, "completed": [], "errors": []})
    flags = subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
    try:
        with (folder / "worker.log").open("w", encoding="utf-8") as log:
            process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--worker", str(job_path)],
                                       stdin=subprocess.PIPE, stdout=log, stderr=subprocess.STDOUT, cwd=str(APP_DIR), creationflags=flags,
                                       start_new_session=os.name != "nt", shell=False)
        try:
            process.stdin.write(json.dumps({"google_credentials": credentials_info}).encode("utf-8"))
            process.stdin.close()
        except BrokenPipeError:
            pass
        try:
            create_time = psutil.Process(process.pid).create_time()
        except psutil.NoSuchProcess:
            create_time = 0
        atomic_json(folder / "process.json", {"pid": process.pid, "create_time": create_time, "started_at": utc_now()})
        # Retain/reap the child without blocking the UI or restarting it on reruns.
        threading.Thread(target=process.wait, daemon=True).start()
    except BaseException:
        release_job_lock(job_id)
        raise
    return job_id


def worker_main(job_path):
    global DATA_DIR, GOOGLE_CREDENTIALS_INFO, IS_WORKER
    IS_WORKER = True
    job_path = Path(job_path)
    job = read_json(job_path)
    DATA_DIR = Path(job["data_dir"])
    try:
        GOOGLE_CREDENTIALS_INFO = json.loads(sys.stdin.read() or "{}").get("google_credentials")
    except (ValueError, OSError):
        GOOGLE_CREDENTIALS_INFO = None
    folder = job_path.parent
    status = read_json(folder / "status.json", {})
    status.update(state="running", started_at=utc_now(), completed=[], errors=[])

    def check_cancel():
        if (folder / "cancel").exists():
            raise Cancelled("Job cancelled by user.")

    def log(message):
        print(f"{utc_now()} {message}", flush=True)
        status.update(message=str(message), updated_at=utc_now())
        atomic_json(folder / "status.json", status)

    routines = {"crawl": run_sf, "sitemaps": discover_sitemaps, "gsc": download_gsc, "content": fetch_content, "recommendations": recommend, "audit": audit_links}
    try:
        if job.get("workflow") == "simple":
            simple_pipeline(job, status, log, check_cancel, folder)
            return
        for profile in job["profiles"]:
            validate_profile(profile)
            for stage in STAGES:
                if stage not in job["stages"]:
                    continue
                check_cancel()
                status.update(client=profile["name"], stage=STAGES[stage])
                log(f"Starting {STAGES[stage]} for {profile['name']}.")
                try:
                    routines[stage](profile, job["options"], log, check_cancel)
                    status["completed"].append({"client": profile["name"], "stage": stage})
                except Cancelled:
                    raise
                except Exception as exc:
                    status["errors"].append({"client": profile["name"], "stage": stage, "error": str(exc)})
                    log(f"Failed: {exc}")
                    # Stop later stages for this client: otherwise old snapshots
                    # could silently be used after a selected refresh failed.
                    break
        status.update(state="completed_with_errors" if status["errors"] else "completed", finished_at=utc_now())
    except Cancelled:
        status.update(state="cancelled", finished_at=utc_now())
    except BaseException as exc:
        status["errors"].append({"error": safe_error(exc)})
        status.update(state="failed", finished_at=utc_now())
    finally:
        atomic_json(folder / "status.json", status)
        release_job_lock(job["id"])
        GOOGLE_CREDENTIALS_INFO = None
        IS_WORKER = False


def install_demo():
    """Deterministic synthetic data; no live clients, credentials or requests."""
    p = default_profile("Demo — synthetic data", "https://demo.example/")
    p.update(id="demo", demo=True, brand_terms=["DemoCo", "DemoCapture"], brands_confirmed=True,
             blog_pattern=r"/blog/", core_pages=[
                 {"url": "https://demo.example/solutions/invoice-data-capture/", "topic": "Invoice data capture software", "priority": 5, "origin": "manual"},
                 {"url": "https://demo.example/solutions/document-scanning/", "topic": "Document scanning services", "priority": 4, "origin": "manual"}])
    root = p["root_url"]
    core1, core2 = [c["url"] for c in p["core_pages"]]
    blog1, blog2 = root + "blog/invoice-workflows/", root + "blog/scanning-records/"
    specs = [(root, "DemoCo", "Business document tools"), (core1, "Invoice data capture software", "Invoice data capture software"),
             (core2, "Document scanning services", "Document scanning services"),
             (blog1, "Improving invoice workflows", "Invoice processing workflows"), (blog2, "Scanning business records", "Document scanning for records")]
    specs += [(root + f"archive/level-{i}/", f"Archive level {i}", f"Archive level {i}") for i in range(1, 5)]
    htmls = {
        core1: "<p>Invoice data capture software extracts invoice data from business documents and supports invoice processing workflows.</p>",
        core2: "<p>Document scanning services convert paper records into searchable digital documents for records management teams.</p>",
        blog1: "<p>Finance teams use invoice data capture software to reduce manual entry when processing supplier invoices and reviewing invoice data.</p><p>DemoCapture invoice data capture software supports this workflow and is a branded phrase.</p>",
        blog2: "<p>Our records team evaluates document scanning services when converting paper archives into searchable digital documents for everyday business access.</p>",
    }
    pages, content = [], []
    for url, title, h1 in specs:
        pages.append({"url": url, "status": 200, "html": True, "content_type": "text/html", "indexable": True, "indexability_status": "", "title": title, "h1": h1, "canonical": url, "redirect": "", "source_nofollow": False})
        html = f"<html><head><title>{title}</title></head><body><main><h1>{h1}</h1>{htmls.get(url, '<p>This archive contains older business resources and links to additional useful pages.</p>')}</main></body></html>"
        row = extract_content(html, url)
        row.update(url=url, final_url=url, fetched_at=utc_now(), extraction_key=digest({"selector": "", "version": APP_VERSION}), status=200)
        content.append(row)
    broken = root + "retired-guide/"
    pages.append({"url": broken, "status": 404, "html": True, "indexable": False, "title": "", "h1": "", "canonical": "", "redirect": "", "indexability_status": "Client Error", "source_nofollow": False})
    links = []

    def link(s, d, anchor, position):
        links.append({"source": s, "destination": d, "anchor": anchor, "alt": "", "position": position, "position_known": True,
                      "contextual": position == "Content", "followable": True, "locator": "", "type": "Hyperlink"})
    link(root, core1, "Invoice products", "Navigation")
    link(root, blog1, "Invoice workflows", "Navigation")
    link(root, blog2, "Scanning records", "Navigation")
    previous = root
    for i in range(1, 5):
        u = root + f"archive/level-{i}/"
        link(previous, u, "Older resources", "Content")
        previous = u
    link(previous, core2, "click here", "Content")
    link(blog1, broken, "retired guide", "Content")
    gen = uuid.uuid4().hex
    save_dataset(p, "pages", pages, generation=gen, source="Synthetic demo", crawl_schema=CRAWL_SCHEMA)
    save_dataset(p, "links", links, generation=gen, links_verified=True, position_available=True, source="Synthetic demo", crawl_schema=CRAWL_SCHEMA)
    save_dataset(p, "content", content, source="Synthetic demo", failed=0, partial=False)
    save_dataset(p, "sitemaps", [{"url": root + "unlinked-resource/"}], source="Synthetic demo")
    metrics = [{"page": core1, "impressions": 14000, "clicks": 120, "position": 11.4, "ctr": 120 / 14000},
               {"page": core2, "impressions": 8200, "clicks": 100, "position": 8.2, "ctr": 100 / 8200}]
    meta = dict(source="Synthetic demo", start_date="2026-08-01", end_date="2026-10-29", brand_method="Synthetic NON_BRANDED", metric_basis="Synthetic data; not live GSC")
    save_dataset(p, "gsc_pages", metrics, **meta)
    save_dataset(p, "gsc_total_pages", metrics, **meta)
    save_dataset(p, "gsc_queries", [{**m, "query": "invoice data capture software" if m["page"] == core1 else "document scanning services"} for m in metrics], **meta)
    save_working_profile(p)
    return p


def recent_dataset(profile, name, hours=24):
    doc = dataset(profile, name)
    try:
        stamp = datetime.fromisoformat(doc["meta"]["created_at"])
        return bool(doc["rows"]) and (datetime.now(timezone.utc) - stamp).total_seconds() < hours * 3600
    except (KeyError, ValueError):
        return False


def save_working_profile(profile, fields=None):
    def merge(current):
        found = next((i for i, row in enumerate(current) if row["id"] == profile["id"]), None)
        if found is None:
            current.append(dict(profile))
        elif fields is None:
            current[found] = {**current[found], **profile}
        else:
            current[found] = {**current[found], **{key: profile[key] for key in fields if key in profile}}
    update_profiles(merge)


def crawl_quality(pages_doc):
    """Crawler failures only: robots exclusions, off-site redirects and real 404/410 pages are site facts."""
    rows = pages_doc.get("rows", [])
    checked = [p for p in rows if not (300 <= int(p.get("status") or 0) < 400) and not p.get("robots_blocked") and not p.get("external_redirect")]
    failed = sum(1 for p in checked if not p.get("status") or p.get("status") in {401, 403, 429} or int(p.get("status") or 0) >= 500)
    successful = sum(1 for p in checked if p.get("status") == 200 and p.get("html"))
    ratio = failed / max(1, len(checked))
    return {"checked": len(checked), "failed": failed, "successful_html": successful, "failure_ratio": ratio,
            "robots_blocked": sum(1 for p in rows if p.get("robots_blocked")), "cacheable": bool(successful) and ratio <= .20}


def cacheable_crawl(profile, pages_doc, links_doc):
    if profile.get("demo"):
        return True
    meta, link_meta = pages_doc.get("meta", {}), links_doc.get("meta", {})
    # Invalidate older built-in classifications/locators on upgrade.
    schema_ok = meta.get("source") != "Built-in HTML crawl" or meta.get("crawl_schema", 0) >= CRAWL_SCHEMA
    mapping = aliases_for(pages_doc.get("rows", []), profile)
    root = resolve_alias(profile["root_url"], mapping)
    home = next((p for p in pages_doc.get("rows", []) if p["url"] == root), {})
    return bool(schema_ok and home.get("status") == 200 and home.get("html") and crawl_quality(pages_doc)["cacheable"]
                and link_meta.get("links_verified") and meta.get("generation") == link_meta.get("generation"))


def upgrade_saved_crawl(profile):
    """Imported exports saved by older versions: apply the canonical check once."""
    pages_doc = dataset(profile, "pages")
    if not pages_doc["rows"] or pages_doc["meta"].get("crawl_schema", 0) >= CRAWL_SCHEMA:
        return 0
    rows = copy.deepcopy(pages_doc["rows"])
    invalid = normalize_canonicals(rows, profile)
    save_dataset(profile, "pages", rows, **{**{k: v for k, v in pages_doc["meta"].items() if k not in {"created_at", "app_version"}},
                                          "crawl_schema": CRAWL_SCHEMA, "invalid_canonicals": invalid})
    return invalid


def safe_error(exc):
    if type(exc).__name__ == "InvalidClientError" or getattr(exc, "error", None) == "invalid_client":
        return "Google rejected the OAuth client credentials (invalid_client). Use client_id and client_secret from the same Web application JSON in Streamlit Secrets, then restart Google sign-in."
    if type(exc).__name__ == "InvalidGrantError" or getattr(exc, "error", None) == "invalid_grant":
        return "The Google sign-in code expired or was already used. Click Restart Google sign-in and complete a fresh sign-in."
    current = exc
    seen = set()
    while current is not None and id(current) not in seen:
        seen.add(id(current))
        if isinstance(current, DownloadTimeout):
            return str(current)
        if isinstance(current, TimeoutError) or type(current).__name__ in {"Timeout", "ReadTimeout", "ConnectTimeout", "TimeoutError"}:
            return "Google took too long to respond. Retry this action. If authorization has expired, reconnect Google in the sidebar."
        current = current.__cause__ or current.__context__
    if type(exc).__name__ in {"RefreshError", "OAuthError", "TokenExpiredError"}:
        return "Google authorization expired or was revoked. Reconnect Google in Connection & crawl options."
    status = getattr(getattr(exc, "resp", None), "status", None)
    if status:
        return f"Google returned HTTP {status}. Check account access, API enablement or quota, then reconnect if needed."
    value = str(exc)
    value = re.sub(r'(?i)(access_token|refresh_token|client_secret|authorization)([\s\"\':=]+)[^\s,}\"]+', r'\1\2[redacted]', value)
    return value[:1000]


@dataset_snapshot()
def simple_pipeline(job, status, log, check_cancel, folder):
    """The one-click workflow; no credentials are written to any dataset."""
    profile = PreparedProfile(job["profiles"][0])
    validate_profile(profile)
    options = {**job["options"], "runtime_mode": deployment_mode()}
    options.update(automatic_setup=True, all_sources=True, blog_to_blog=False, query_driven=not bool(text_norm(options.get("anchor_text", ""))),
                   audit_checks=list(AUDITS), recommendation_cap=300,
                   links_per_target=30 if options.get("anchor_text") else 5,
                   paragraphs_per_target=500 if options.get("anchor_text") else 120,
                   content_cap=options.get("crawl_limit", 2000))
    phases = ["Discover pages & navigation", "Crawl blogs & core pages", "Load GSC page/query performance", "Find exact query mentions", "Analyze internal links", "Prepare insights & workbook"]
    weights = [.05, .50, .10, .20, .05, .10]
    warnings = []
    status.update(client=profile["name"], warnings=warnings, phase_count=len(phases), phase_index=0, overall_progress=0, phase_progress=0)

    def publish():
        status["updated_at"] = utc_now()
        atomic_json(folder / "status.json", status)

    def phase(index):
        check_cancel()
        status.update(phase_index=index, stage=phases[index], phase_progress=0, overall_progress=sum(weights[:index]), done=0, total=0)
        log(phases[index])
        publish()

    def progress(done, total, message):
        check_cancel()
        fraction = min(.99, done / total) if total else 0
        status.update(done=done, total=total, phase_progress=fraction, message=message,
                      overall_progress=min(.99, sum(weights[:status["phase_index"]]) + weights[status["phase_index"]] * fraction))
        publish()
    log.progress = progress
    phase(0)
    automatic_brand_terms(profile)
    upgrade_saved_crawl(profile)
    old_pages, old_links = dataset(profile, "pages"), dataset(profile, "links")
    cached = (cacheable_crawl(profile, old_pages, old_links) and (profile.get("demo") or (not options.get("refresh_crawl") and recent_dataset(profile, "pages"))))
    if old_pages["rows"] and not cached and not options.get("refresh_crawl"):
        log("Saved crawl needs refreshing because its coverage, extraction version, or age is unsuitable.")
    homepage = None
    if cached:
        infer_core_pages(profile, dataset(profile, "pages")["rows"], dataset(profile, "links")["rows"])
        progress(1, 1, "Using the saved crawl; reading navigation and footer links.")
    else:
        try:
            # Respect root robots directives before downloading the homepage.
            origin = urlunsplit((*urlsplit(profile["root_url"])[:2], "", "", ""))
            robot = RobotFileParser(origin + "/robots.txt")
            code, _, _, raw_robot = get_bytes(origin + "/robots.txt", 1_000_000)
            robot.parse(raw_robot.decode("utf-8", errors="replace").splitlines() if code == 200 else ["User-agent: *", "Disallow:" if code in {404, 410} else "Disallow: /"])
            if not robot.can_fetch(UA, profile["root_url"]):
                raise ValueError("Homepage access is blocked by robots.txt or robots.txt is unavailable.")
            homepage = get_bytes(profile["root_url"])
            code, headers, final_url, raw = homepage
            if code != 200 or not same_site(final_url, profile):
                raise ValueError(f"Homepage returned HTTP {code} or redirected outside the configured website.")
            profile["root_url"] = url_key(final_url)
            page, edges, _, names = page_from_html(raw, profile["root_url"], profile, headers)
            if page.get("selector_missed"):
                warnings.append(f"The main-content selector '{profile.get('main_selector')}' matched nothing on the homepage; automatic content detection was used where it did not match.")
            automatic_brand_terms(profile, names)
            infer_core_pages(profile, [page], edges, strict=False)
            progress(1, 1, f"Found {len(profile['core_pages'])} candidate core pages in the homepage navigation and footer.")
        except Cancelled:
            raise
        except Exception as exc:
            homepage = None
            if options.get("runtime_mode") != "local":
                raise ValueError(f"Could not read the website: {safe_error(exc)}") from exc
            warnings.append("Homepage HTML could not be read; using the local Screaming Frog crawl to identify navigation links.")
    if not profile.get("demo") and GOOGLE_CREDENTIALS_INFO and profile.get("gsc_property") and not recent_dataset(profile, "gsc_total_pages"):
        try:
            log("Loading known landing pages from Search Console for crawl discovery.")
            end = datetime.now(ZoneInfo("America/Los_Angeles")).date() - timedelta(days=3)
            start = end - timedelta(days=89)
            service = google_service()
            try:
                rows, capped = gsc_rows(service, profile["gsc_property"], start, end, ["page"], [], check_cancel)
            finally:
                service.close()
            rows = [r for r in rows if same_site(r.get("page", ""), profile)]
            save_dataset(profile, "gsc_total_pages", aggregate_gsc(rows, ["page"]), start_date=str(start), end_date=str(end),
                         gsc_property=profile["gsc_property"], source="GSC crawl discovery", partial=capped)
        except Cancelled:
            raise
        except Exception as exc:
            warnings.append("GSC URL discovery unavailable: " + safe_error(exc))
    phase(1)
    if cached:
        if profile.get("demo") or recent_dataset(profile, "content"):
            progress(len(dataset(profile, "pages")["rows"]), len(dataset(profile, "pages")["rows"]), "Reusing the saved crawl and extracted content.")
        else:
            fetch_content(profile, options, log, check_cancel)
    else:
        use_sf = False
        if options.get("runtime_mode") == "local":
            try:
                find_sf(options.get("sf_path", ""))
                use_sf = True
            except FileNotFoundError:
                pass
        if use_sf:
            run_sf(profile, options, log, check_cancel)
            infer_core_pages(profile, dataset(profile, "pages")["rows"], dataset(profile, "links")["rows"])
            fetch_content(profile, options, log, check_cancel)
        else:
            built_in_crawl(profile, options, log, check_cancel, homepage)
    pages_doc = dataset(profile, "pages")
    pages, links = pages_doc["rows"], dataset(profile, "links")["rows"]
    quality = crawl_quality(pages_doc)
    if not quality["cacheable"]:
        statuses = Counter(str(p.get("status", 0)) for p in pages if not p.get("robots_blocked") and (not p.get("status") or p.get("status") in {401, 403, 429} or p.get("status", 0) >= 500))
        warnings.append(f"Many requests failed ({quality['failed']} of {quality['checked']}: {dict(statuses)}). The site may be rate-limiting the crawler; results cover the pages that could be read.")
        if not quality["successful_html"]:
            raise ValueError(f"Crawl coverage is insufficient: no usable HTML pages; {quality['failed']} failed requests ({dict(statuses)}). Retry after checking access/rate limits, or import Screaming Frog exports.")
    infer_core_pages(profile, pages, links)
    detect_proprietary_product_brands(profile, dataset(profile, "content")["rows"])
    if not profile.get("core_pages"):
        profile["core_pages"] = fallback_core_pages(profile, pages, links)
        warnings.append("No navigation, footer or site-wide links to eligible pages were recognised. The most-linked pages were used as core pages; "
                        "review them under Core pages, or add a URL pattern such as ^/solutions/.")
    core_urls = {c["url"] for c in profile["core_pages"]}
    profile["blog_urls"] = [u for u in profile.get("blog_urls", []) if u not in core_urls]
    invalid_canonicals = [p for p in pages if p.get("invalid_canonical")]
    if invalid_canonicals:
        examples = ", ".join(urlsplit(p["url"]).path for p in invalid_canonicals[:3])
        warnings.append(f"{len(invalid_canonicals)} page(s) have canonical tags pointing to broken, redirecting or noindex URLs (for example {examples}). "
                        "They are analysed as indexable here, but search engines may not index them. See Existing-link issues.")
    save_working_profile(profile, fields=["root_url", "core_pages", "blog_urls", "brand_terms", "automatic_setup"])
    status["core_pages"] = len(profile["core_pages"])
    indexable_urls = {p["url"] for p in pages if p.get("indexable")}
    status["blogs"] = sum(is_blog(c["url"], profile) for c in dataset(profile, "content")["rows"] if c.get("success") and c["url"] in indexable_urls)
    phase(2)
    if profile.get("demo"):
        progress(1, 1, "Using synthetic demo metrics.")
    elif GOOGLE_CREDENTIALS_INFO and profile.get("gsc_property"):
        gsc_meta = dataset(profile, "gsc_pages")["meta"]
        query_meta = dataset(profile, "gsc_queries")["meta"]
        if (recent_dataset(profile, "gsc_pages") and recent_dataset(profile, "gsc_queries") and not options.get("refresh_crawl")
                and gsc_meta.get("generation") == query_meta.get("generation")
                and gsc_meta.get("brand_rules_hash") == digest(profile.get("brand_terms", []))):
            progress(1, 1, f"Using {len(dataset(profile, 'gsc_queries')['rows']):,} saved Search Console query/page pairs.")
        else:
            try:
                end = datetime.now(ZoneInfo("America/Los_Angeles")).date() - timedelta(days=3)
                download_gsc(profile, {**options, "start_date": str(end - timedelta(days=89)), "end_date": str(end), "brand_mode": "auto"}, log, check_cancel)
            except Cancelled:
                raise
            except Exception as exc:
                warnings.append("Search Console unavailable for this run: " + safe_error(exc) + " Any saved query data retains its original date range. Automatic suggestions require page/query evidence.")
    else:
        count = len(dataset(profile, "gsc_queries")["rows"])
        progress(1, 1, f"Using {count:,} saved query/page pairs." if count else "No GSC query/page data is available for this client.")
        if not count:
            warnings.append("Automatic exact-query recommendations need GSC page/query data. Audits and charts remain available; manual anchor searches can run without GSC.")
    phase(3)
    state = graph_state(profile)
    metric_data = metric_maps(profile, state["aliases"])
    if profile.get("core_pages") or options.get("query_driven"):
        recommend(profile, options, log, check_cancel, state=state, metric_data=metric_data)
    phase(4)
    audit_links(profile, options, log, check_cancel, state=state, metric_data=metric_data)
    phase(5)
    progress(0, 2, "Preparing page decisions and topic clusters from the saved crawl.")
    insights = build_explorer_data(profile, log, check_cancel, state=state, metric_data=metric_data)
    progress(1, 2, "Page decisions and cluster analysis are ready; maps render only when inspected.")
    save_dataset(profile, "visuals", [], rendering="On demand from saved explorer snapshot")
    workbook = workbook_bytes([profile], ["Recommendations", "Core pages", "Priority pages", "Topic clusters", "Cluster link reviews", "GSC queries", "GSC pages", "Existing-link issues", "Page summary", "Run summary"])
    output = client_dir(profile) / "exports" / f"internal_links_{job['id']}.xlsx"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(workbook)
    prune_files(output.parent, "internal_links_*.xlsx", keep=5)
    for name in ["pages", "recommendations"]:
        if dataset(profile, name)["meta"].get("partial"):
            warnings.append("This run covers a limited selection of pages. Coverage and limits are included in the workbook.")
    crawl_meta = dataset(profile, "pages")["meta"]
    if crawl_meta.get("failed"):
        warnings.append(f"{crawl_meta['failed']} page requests failed (timeouts, blocks or server errors). Results cover pages that could be read.")
    if crawl_meta.get("robots_blocked"):
        warnings.append(f"{crawl_meta['robots_blocked']} linked URL(s) are disallowed by robots.txt and were skipped; they are not counted as failures.")
    if crawl_meta.get("selector_missed"):
        warnings.append(f"The main-content selector matched nothing on {crawl_meta['selector_missed']} page(s); automatic content detection was used there.")
    warnings.extend(dataset(profile, "recommendations")["meta"].get("warnings", []))
    warnings.extend(insights["meta"]["warnings"])
    save_dataset(profile, "result", [], workbook=str(output), warnings=list(dict.fromkeys(warnings)), job_id=job["id"],
                 core_pages=status["core_pages"], blogs=status["blogs"], anchor_text=options.get("anchor_text", ""),
                 query_pairs=len(dataset(profile, "gsc_queries")["rows"]), matching_strategy=dataset(profile, "recommendations")["meta"].get("matching_strategy", "manual_anchor"),
                 opportunities=len(dataset(profile, "recommendations")["rows"]), crawl_source=crawl_meta.get("source"),
                 invalid_canonicals=len(invalid_canonicals))
    status.update(state="completed", overall_progress=1, phase_progress=1, done=2, total=2, warnings=list(dict.fromkeys(warnings)),
                  finished_at=utc_now(), message="Opportunities, analysis, charts and workbook are ready.")
    publish()


def register_google_properties(properties):
    """One preferred property per host; retain existing client identities."""
    def register(profiles):
        by_host = {(urlsplit(p["root_url"]).hostname or "").removeprefix("www."): p for p in profiles if not p.get("demo")}
        grouped = defaultdict(list)
        for row in properties:
            prop = row.get("siteUrl", "")
            if row.get("permissionLevel") == "siteUnverifiedUser":
                continue
            root = "https://" + prop.split(":", 1)[1] + "/" if prop.startswith("sc-domain:") else prop
            host = (urlsplit(root).hostname or "").removeprefix("www.")
            if host and (prop.startswith("sc-domain:") or urlsplit(root).path in {"", "/"}):
                grouped[host].append((prop, root))
        for host, choices in grouped.items():
            prop, root = sorted(choices, key=lambda x: (not x[0].startswith("sc-domain:"), not x[1].startswith("https://")))[0]
            if host in by_host:
                by_host[host]["gsc_property"] = prop
            else:
                profile = default_profile(host, root, prop)
                automatic_brand_terms(profile)
                profiles.append(profile)
    return update_profiles(register)


def secret_value(st, name, default=""):
    try:
        return st.secrets.get(name, default)
    except FileNotFoundError:
        return default


def validate_token_info(value):
    if isinstance(value, dict) and ("installed" in value or "web" in value):
        raise ValueError("This is Google's client configuration. Use Connect Google to sign in; it is not an authorized token yet.")
    if not isinstance(value, dict) or not all(value.get(k) for k in ["refresh_token", "client_id", "client_secret"]):
        raise ValueError("This file does not contain reusable Google authorization. Use your downloaded client configuration with Connect Google.")
    if value.get("token_uri") not in {None, "https://oauth2.googleapis.com/token", "https://accounts.google.com/o/oauth2/token"}:
        raise ValueError("The token JSON must use Google's token endpoint.")
    scopes = value.get("scopes", [])
    if isinstance(scopes, str):
        scopes = scopes.split()
    if scopes and not set(scopes).issubset(set(SCOPES)):
        raise ValueError("Use a token authorized only for Google Search Console read-only access.")
    return value


def validate_google_client_config(value):
    """Accept Google's download unchanged, but never trust arbitrary endpoints."""
    if not isinstance(value, dict):
        raise ValueError("Choose the JSON client configuration downloaded from Google Cloud.")
    kind = "web" if isinstance(value.get("web"), dict) else "installed" if isinstance(value.get("installed"), dict) else None
    if not kind:
        raise ValueError("The Google client JSON must contain a web or installed section.")
    config = dict(value[kind])
    if not all(isinstance(config.get(k), str) and config[k].strip() for k in ("client_id", "client_secret")):
        raise ValueError("The Google client configuration needs client_id and client_secret.")
    if not config["client_id"].endswith(".apps.googleusercontent.com"):
        raise ValueError("Use the OAuth client ID from your Google Cloud download.")
    if config.get("auth_uri") not in {None, "https://accounts.google.com/o/oauth2/auth", "https://accounts.google.com/o/oauth2/v2/auth"}:
        raise ValueError("The client configuration does not use Google's authorization endpoint.")
    if config.get("token_uri") not in {None, "https://oauth2.googleapis.com/token", "https://accounts.google.com/o/oauth2/token"}:
        raise ValueError("The client configuration does not use Google's token endpoint.")
    config.update(auth_uri="https://accounts.google.com/o/oauth2/v2/auth", token_uri="https://oauth2.googleapis.com/token")
    return {kind: config}


def load_google_client_config(st, runtime):
    value = secret_value(st, "google_client_secret_json")
    path = secret_value(st, "google_client_secret_path")
    if not value and not path:
        # Recognize a client download previously put in the old token setting.
        legacy = secret_value(st, "gsc_token_json")
        try:
            candidate = json.loads(legacy) if isinstance(legacy, str) and legacy else dict(legacy or {})
        except (TypeError, ValueError):
            candidate = {}
        if "web" in candidate or "installed" in candidate:
            value = candidate
    if value:
        try:
            value = json.loads(value) if isinstance(value, str) else dict(value)
        except (TypeError, ValueError):
            raise ValueError("google_client_secret_json must contain the downloaded JSON contents, rather than a file path.") from None
        return validate_google_client_config(value)
    if path:
        if runtime != "local":
            raise ValueError("Streamlit Cloud cannot open your laptop's C: drive. Put the file contents in google_client_secret_json in Secrets.")
        try:
            value = json.loads(Path(str(path)).expanduser().read_text(encoding="utf-8-sig"))
        except (OSError, ValueError):
            raise ValueError("Could not open the Google client JSON on this computer. Check google_client_secret_path.") from None
        return validate_google_client_config(value)
    return None


def google_redirect_uri(st, config, runtime):
    if "web" not in config:
        raise ValueError("This is a Desktop OAuth client. For Streamlit Cloud, create a Web application client in Google Cloud, register the return URL, then use its downloaded JSON.")
    redirect = str(secret_value(st, "google_redirect_uri")).strip()
    if not redirect:
        choices = [u for u in config["web"].get("redirect_uris", []) if isinstance(u, str) and urlsplit(u).path in GOOGLE_CALLBACK_PATHS]
        if len(choices) == 1:
            redirect = choices[0]
    parsed = urlsplit(redirect)
    local = parsed.hostname in {"localhost", "127.0.0.1", "[::1]", "::1"}
    if (not parsed.hostname or parsed.username or parsed.password or parsed.query or parsed.fragment
            or parsed.path not in GOOGLE_CALLBACK_PATHS or (parsed.scheme != "https" and not (runtime == "local" and local and parsed.scheme == "http"))
            or (runtime != "local" and local)):
        raise ValueError("Set google_redirect_uri to your app's HTTPS URL followed by " + GOOGLE_CALLBACK_PATH + ". Register the exact same URL in Google Cloud.")
    return redirect


def begin_google_authorization(config, redirect_uri):
    from google_auth_oauthlib.flow import Flow
    flow = Flow.from_client_config(validate_google_client_config(config), SCOPES, redirect_uri=redirect_uri,
                                   autogenerate_code_verifier=True)
    url, state = flow.authorization_url(access_type="offline", prompt="consent select_account", include_granted_scopes="false")
    return {"flow": flow, "authorization_url": url, "state": state, "created_at": time.monotonic(), "id": uuid.uuid4().hex}


def finish_google_authorization(pending, response):
    """Require this browser session's one-use state before exchanging a code."""
    if pending.get("used"):
        raise ValueError("This Google sign-in has already been used. Connect Google again.")
    pending["used"] = True
    if time.monotonic() - pending["created_at"] > 600:
        raise ValueError("Google sign-in timed out. Connect Google again.")
    if not isinstance(response, dict) or not isinstance(response.get("state"), str) or not hmac.compare_digest(response["state"].encode(), pending["state"].encode()):
        raise ValueError("The Google sign-in could not be verified. Connect Google again.")
    if response.get("error"):
        raise ValueError("Google access was not granted. Connect Google again and allow Search Console read-only access.")
    code = response.get("code")
    if not isinstance(code, str) or not code.strip():
        raise ValueError("Google did not return an authorization code. Connect Google again.")
    flow = pending["flow"]
    flow.fetch_token(code=code, timeout=GOOGLE_HTTP_TIMEOUT)
    token = validate_token_info(json.loads(flow.credentials.to_json()))
    return token


def google_authorize_button(pending):
    """Popup with canonical callback matching; no secret is sent to the UI."""
    # Keep the previously registered callback URL working. This import registers
    # the package's callback asset; our component handles the popup and return.
    import streamlit_oauth  # noqa: F401
    from streamlit.components.v1 import declare_component
    folder = DATA_DIR / "ui" / ("google-sign-in-" + hashlib.sha256(GOOGLE_POPUP_HTML.encode()).hexdigest()[:12])
    folder.mkdir(parents=True, exist_ok=True)
    target = folder / "index.html"
    if not target.is_file():
        temporary = folder / (uuid.uuid4().hex + ".tmp")
        temporary.write_text(GOOGLE_POPUP_HTML, encoding="utf-8")
        os.replace(temporary, target)
    popup = declare_component("google_connect", path=str(folder))
    return popup(authorization_url=pending["authorization_url"], name="Connect Google", key="google_" + pending["id"], default=None)


def google_popup_error(response):
    messages = {
        "popup_blocked": "Your browser blocked the Google sign-in popup. Allow popups for this app, then click Connect Google again.",
        "popup_closed": "The Google popup closed before the app received its response. Click Connect Google again.",
        "popup_timeout": "Google has not returned to this app. Close the previous popup and click Restart Google sign-in.",
        "popup_unavailable": "The browser could not return Google sign-in to this app. Click Restart Google sign-in.",
        "invalid_connection": "The Google sign-in could not start. Click Restart Google sign-in.",
    }
    return messages.get(response.get("_ui_error"), messages["invalid_connection"])


def render_google_connection(st, config, runtime, password, info, uploaded=None):
    st.markdown("**Google Search Console**")
    if runtime == "hosted" and not password:
        st.caption("Set app_password in Streamlit Secrets to enable Google access.")
        return
    notice = st.session_state.pop("google_notice", "")
    if notice:
        st.info(notice)
    if info:
        st.caption("Connected · Search Console read-only")
        if st.button("Refresh client list", key="google_refresh"):
            try:
                connected, properties = run_google_connection(st, info=info, reset_selection=False)
                st.session_state["google_notice"] = f"Loaded {len(properties)} Search Console properties."
                st.rerun()
            except Exception as exc:
                st.error(safe_error(exc))
        if st.button("Disconnect Google", key="google_disconnect"):
            st.session_state.pop("gsc_credentials", None)
            st.session_state.pop("_google_pending", None)
            st.session_state["skip_secret_token"] = True
            st.rerun()
        return
    if config and "installed" in config:
        if runtime != "local":
            st.info("Your JSON is a Desktop client. Streamlit Cloud needs a Web application client with your app's return URL. Put that download in google_client_secret_json in Secrets.")
            return
        if st.button("Connect Google", key="google_local"):
            try:
                run_google_connection(st, client_config=config)
                st.rerun()
            except Exception as exc:
                st.error(safe_error(exc))
        return
    if config:
        redirect = google_redirect_uri(st, config, runtime)
        identity = digest({"client_id": config["web"]["client_id"], "redirect": redirect})
        pending = st.session_state.get("_google_pending")
        if not pending or pending.get("identity") != identity or time.monotonic() - pending["created_at"] > 600:
            pending = begin_google_authorization(config, redirect)
            pending["identity"] = identity
            st.session_state["_google_pending"] = pending
        response = google_authorize_button(pending)
        st.caption("Waiting for Google sign-in. Keep this app tab open. Connecting only loads your client list; no crawl runs yet.")
        if st.button("Restart Google sign-in", key="google_restart"):
            st.session_state.pop("_google_pending", None)
            st.rerun()
        st.caption("If you already approved access but the popup stays open, close that popup and restart sign-in. The return URL in Google Cloud and Streamlit Secrets must match exactly.")
        if isinstance(response, dict) and response.get("_ui_error"):
            st.warning(google_popup_error(response))
            return
        if response:
            try:
                connected, properties = run_google_connection(st, pending=pending, response=response)
                st.session_state["google_notice"] = f"Loaded {len(properties)} Search Console properties."
            except Exception as exc:
                st.session_state["google_notice"] = safe_error(exc)
            finally:
                st.session_state.pop("_google_pending", None)
            st.rerun()
    elif uploaded:
        if st.button("Connect Google", key="google_token"):
            try:
                run_google_connection(st, info=validate_token_info(uploaded))
                st.rerun()
            except Exception as exc:
                st.error(safe_error(exc))
    else:
        st.caption("Add google_client_secret_json in Streamlit Secrets once, then use Connect Google here.")


def import_html_csv(profile, source):
    """Optional SF custom extraction: Address + HTML (or Rendered HTML)."""
    df = read_sf_csv(source)
    address = sf_column(df, "Address", "URL")
    html = sf_column(df, "HTML", "Rendered HTML", "Main HTML", "Page HTML")
    if not address or not html:
        raise ValueError("The optional content CSV needs Address and HTML (or Rendered HTML) columns.")
    rows, blog_urls = [], set(profile.get("blog_urls", []))
    for raw in df.to_dict("records"):
        u = url_key(raw.get(address, ""))
        if not same_site(u, profile) or not raw.get(html):
            continue
        page, _, body, _ = page_from_html(str(raw[html]), u, profile)
        rows.append(body)
        if page.get("article"):
            blog_urls.add(u)
    if not rows:
        raise ValueError("No usable HTML records were found for this website.")
    profile["blog_urls"] = sorted(blog_urls)
    save_dataset(profile, "content", rows, source="Imported HTML extraction", failed=sum(not r.get("success") for r in rows), partial=False)
    save_working_profile(profile)
    return len(rows)


def fetch_google_properties(info=None, client_config=None, on_credentials=lambda _: None):
    """Read-only network work. A late response must never save client profiles."""
    service, connected = google_service(credentials_info=info, interactive=bool(client_config), client_config=client_config,
                                        return_credentials=True, timeout=GOOGLE_HTTP_TIMEOUT)
    on_credentials(connected)
    try:
        properties = execute_google(lambda: service.sites().list(), max_attempts=1).get("siteEntry", [])
    finally:
        service.close()
    return connected, properties


def run_google_connection(st, info=None, client_config=None, pending=None, response=None, reset_selection=True):
    """Keep UI responsive, show actual stages, and bound the full connection."""
    st.session_state["auto_connection_attempted"] = True
    events = queue.Queue()
    done = threading.Event()
    cancelled = threading.Event()
    limit = 210 if client_config and "installed" in client_config else GOOGLE_CONNECT_TIMEOUT

    def emit(kind, value):
        if not cancelled.is_set():
            events.put((kind, value))

    def worker():
        try:
            token = info
            if pending is not None:
                emit("stage", "1/3 · Completing Google authorization")
                token = finish_google_authorization(pending, response)
                emit("credentials", token)
            else:
                emit("stage", "1/3 · Checking Google authorization")
            if cancelled.is_set():
                return
            emit("stage", "2/3 · Loading Search Console client list")
            result = fetch_google_properties(token, client_config, on_credentials=lambda value: emit("credentials", value))
            emit("result", result)
        except Exception as exc:
            emit("error", exc)
        finally:
            done.set()

    result, error = None, None
    started = time.monotonic()
    with st.status("Connecting Google…", expanded=True) as status:
        threading.Thread(target=worker, name="google-connect", daemon=True).start()
        try:
            while True:
                while True:
                    try:
                        kind, value = events.get_nowait()
                    except queue.Empty:
                        break
                    if kind == "stage":
                        status.update(label=value)
                        status.write(value)
                    elif kind == "credentials":
                        st.session_state["gsc_credentials"] = value
                    elif kind == "result":
                        result = value
                    elif kind == "error":
                        error = value
                if done.is_set() and events.empty():
                    break
                if time.monotonic() - started >= limit:
                    raise TimeoutError("Google connection exceeded its time limit.")
                done.wait(.1)
            if error is not None:
                raise error
            if result is None:
                raise TimeoutError("Google connection did not finish.")
            connected, properties = result
            status.update(label="3/3 · Preparing your client selector")
            status.write("3/3 · Preparing your client selector")
            register_google_properties(properties)
            st.session_state["gsc_credentials"] = connected
            if reset_selection:
                st.session_state["selected_client"] = None
            status.update(label=f"Connected · {len(properties)} Search Console properties", state="complete", expanded=False)
            return connected, properties
        except Exception:
            cancelled.set()
            status.update(label="Connection stopped · retry is available", state="error", expanded=True)
            raise
        finally:
            cancelled.set()


# ---- Read-only caches for the interface. Cached objects are shared; never mutate them. ----

def _load_json_file(path, mtime_ns, size):
    return read_json(path, {"meta": {}, "rows": []})


def cached_dataset(st, profile, name):
    path = client_dir(profile) / f"{name}.json"
    try:
        stat = path.stat()
    except FileNotFoundError:
        return {"meta": {}, "rows": []}
    loader = st.cache_resource(max_entries=24, show_spinner=False)(_load_json_file)
    return loader(str(path), stat.st_mtime_ns, stat.st_size)


def _snapshot_from_disk(path, mtime_ns):
    return read_json(path)


def _explorer_base_for_ui(profile_json, base_signature):
    return build_explorer_base(json.loads(profile_json))


def explorer_for_ui(st, profile, job_active=False):
    """Return (snapshot, is_previous). Never rebuilds while a run is writing this client's data."""
    path = client_dir(profile) / "explorer_snapshot.json"
    manifest = read_json(client_dir(profile) / "explorer_manifest.json", {}) or {}
    current = path.is_file() and manifest.get("signature") == insight_signature(profile)
    snapshot_loader = st.cache_resource(max_entries=3, show_spinner=False)(_snapshot_from_disk)
    if path.is_file() and (current or job_active):
        return snapshot_loader(str(path), path.stat().st_mtime_ns), not current
    if job_active:
        return None, True
    base_loader = st.cache_resource(max_entries=2, show_spinner=False)(_explorer_base_for_ui)
    with st.spinner("Updating clusters and page decisions from the saved crawl…"):
        base = base_loader(json.dumps(profile, sort_keys=True, default=str), insight_base_signature(profile))
        build_explorer_data(profile, base=base)
    return snapshot_loader(str(path), path.stat().st_mtime_ns), False


def save_core_selection(profile, chosen, patterns):
    """Pages you keep become confirmed; pages you remove are never auto-added again."""
    current = {c["url"]: c for c in profile.get("core_pages", [])}
    chosen = list(dict.fromkeys(url_key(u) for u in chosen if url_key(u)))
    removed = (set(profile.get("core_excluded", [])) | (set(current) - set(chosen))) - set(chosen)
    pages_doc = dataset(profile, "pages")
    page_map = {p["url"]: p for p in pages_doc["rows"]}
    entries = []
    for u in chosen:
        old, page = current.get(u, {}), page_map.get(u, {})
        entries.append({"url": u, "topic": old.get("topic") or without_brand(page.get("h1") or page.get("title") or urlsplit(u).path, profile),
                        "priority": max(4, int(old.get("priority", 4))), "origin": "manual",
                        "signal": old.get("signal") or ("" if old.get("origin") == "manual" else old.get("detected_from", "")),
                        "linked_from_pages": old.get("linked_from_pages"), "sitewide_share": old.get("sitewide_share")})
    profile["core_pages"] = entries
    profile["core_excluded"] = sorted(removed)
    profile["core_patterns"] = patterns
    if pages_doc["rows"]:
        infer_core_pages(profile, pages_doc["rows"], dataset(profile, "links")["rows"])
    save_working_profile(profile, fields=["core_pages", "core_excluded", "core_patterns"])


def render_core_editor(st, profile, job_active):
    core = profile.get("core_pages", [])
    with st.expander(f"Core pages ({len(core)}) — review and edit", expanded=not core):
        st.caption("Found in the main navigation, the footer, and links repeated on most pages. Keep, remove or add pages, or add URL "
                   "patterns. Your choices are saved for this client. Clusters update immediately; click Find opportunities to refresh "
                   "link suggestions (the saved crawl is reused).")
        if core:
            st.dataframe(pd.DataFrame([{"Page": c["url"], "Topic": c.get("topic", ""), "Found in": c.get("detected_from", ""),
                                        "Linked from pages": c.get("linked_from_pages"),
                                        "Share of pages linking": None if c.get("sitewide_share") is None else round(100 * c["sitewide_share"])}
                                       for c in core]),
                         hide_index=True, width="stretch", column_config={"Page": st.column_config.LinkColumn(),
                                                                          "Share of pages linking": st.column_config.NumberColumn(format="%d%%")})
        pages_doc = cached_dataset(st, profile, "pages")
        options = sorted({p["url"] for p in pages_doc["rows"] if p.get("status") == 200 and p.get("html") and p.get("indexable")} | {c["url"] for c in core})
        with st.form("core_edit_" + profile["id"]):
            chosen = st.multiselect("Core pages", options, default=[c["url"] for c in core],
                                    format_func=lambda u: urlsplit(u).path or "/", placeholder="Choose core pages")
            patterns_text = st.text_area("Also treat every page matching these URL patterns as core (one regular expression per line)",
                                         "\n".join(profile.get("core_patterns", [])), placeholder="^/solutions/\n^/use-cases/", height=90)
            submitted = st.form_submit_button("Save core pages", disabled=job_active)
        if job_active:
            st.caption("Editing is available when the current run finishes.")
        if submitted:
            patterns = [line.strip() for line in patterns_text.splitlines() if line.strip()]
            for pattern in patterns:
                try:
                    re.compile(pattern)
                except re.error as exc:
                    st.error(f"'{pattern}' is not a valid pattern: {exc}")
                    return
            save_core_selection(profile, chosen, patterns)
            st.rerun()


def insight_table(rows):
    values = []
    for row in rows:
        values.append({"Page": row["url"], "Role": "Cluster hub" if row["is_hub"] else row["page_type"], "Cluster": row["cluster"],
                       "Review priority": row["review_priority"], "Issues": "; ".join(row["flags"]) or "No selected issue",
                       "Observed sources": row["unique_inlink_sources"], "Body-link sources": row["unique_contextual_sources"],
                       "Verified opportunities": row["proposed_links"], "Queries at positions 4–30": row["query_opportunities"],
                       "Depth": row["crawl_depth_from_home"], "Next action": row["next_action"]})
    return pd.DataFrame(values)


def render_page_focus(st, profile, snapshot, focus_url, prefix, cluster_ids=None, entire_cluster=False):
    by_url = {r["url"]: r for r in snapshot["pages"]}
    row = by_url[focus_url]
    st.markdown("**Page focus**")
    st.link_button(row["title"] or row["h1"] or focus_url, focus_url)
    st.info(row["next_action"])
    if row.get("invalid_canonical"):
        st.warning(f"Canonical tag points to {row['invalid_canonical']}, which is broken, redirects or is noindex.")
    cols = st.columns(4)
    for column, label, value in zip(cols, ["All observed sources", "Contextual source pages", "Verified placements", "Depth from homepage"],
                                     [row["unique_inlink_sources"], row["unique_contextual_sources"], row["proposed_links"], row["crawl_depth_from_home"]]):
        column.metric(label, "Unknown" if value is None else value)
    st.caption(f"Cluster: {row['cluster']} · Assignment: {row['cluster_confidence']} · Link-position evidence: {row['context_evidence']}")
    with st.expander("Map controls", expanded=False):
        include_template = st.checkbox("Include navigation/footer and unknown-position links", key=prefix + "_template")
        show_proposed = st.checkbox("Show verified proposed links", value=True, key=prefix + "_proposed")
        limit = st.slider("Maximum pages shown", 10, 75, 25, 5, key=prefix + "_cap")
        wider_links = st.checkbox("Show links between supporting pages", key=prefix + "_wider") if entire_cluster else False
    figure, display = focus_network(snapshot, focus_url, limit, include_template, show_proposed, cluster_ids, entire_cluster and wider_links)
    st.plotly_chart(figure, width="stretch", key=prefix + "_graph")
    st.caption(f"Showing {display['shown_pages']} of {display['related_pages']} relevant pages; {display['hidden_pages']} hidden. Counts above use the full available crawl. Blue diamond = selected page; red = unreachable; green = proposed placement; amber = missing hub link. Arrows show link direction.")
    if "Under-supported core" in row["flags"]:
        st.caption(f"Support review rule: {row['unique_contextual_sources']} contextual source pages against a comparison threshold of {row['context_review_threshold']}. This threshold guides review; it is not a ranking requirement.")
    if display["hidden_edges"]:
        st.caption(f"{display['hidden_edges']} additional links between visible pages are omitted from the drawing for clarity.")
    panels = st.tabs(["Verified opportunities", "Existing incoming links", "Related pages", "Path from homepage"])
    with panels[0]:
        recs = [r for r in snapshot["recommendations"] if r["destination_url"] == focus_url]
        if recs:
            frame = pd.DataFrame(recs).reindex(columns=["source_url", "anchor_text", "supporting_query", "query_impressions", "query_position", "context"])
            st.dataframe(frame.rename(columns={"source_url": "Source", "anchor_text": "Existing anchor", "supporting_query": "GSC query", "query_impressions": "Query impressions", "query_position": "Query average position", "context": "Existing paragraph"}),
                         hide_index=True, width="stretch", column_config={"Source": st.column_config.LinkColumn()})
        else:
            st.caption("No verified exact-query placement is saved for this page. A structural issue alone does not establish a suitable anchor.")
        if row["top_queries"]:
            with st.expander("Queries this page receives impressions for"):
                st.dataframe(pd.DataFrame(row["top_queries"])[["query", "impressions", "position", "clicks"]], hide_index=True, width="stretch")
    with panels[1]:
        incoming = [{"Source": e["source"], "Body link": e["contextual"], "Navigation/footer": e["template"], "Position uncertain": e["unknown_position"], "Anchors": "; ".join(e["anchors"])}
                    for e in snapshot["links"] if e["destination"] == focus_url]
        if incoming:
            st.dataframe(pd.DataFrame(incoming), hide_index=True, width="stretch", column_config={"Source": st.column_config.LinkColumn()})
        else:
            st.caption("No incoming source is present in the available link inventory.")
        if row.get("concentration_evidence"):
            st.write("Peer outlier evidence: " + " ".join(row["concentration_evidence"]))
    with panels[2]:
        related = [r for r in snapshot["pages"] if r["active"] and r["url"] != focus_url and row["cluster_id"] != "unassigned"
                   and (r["cluster_id"] == row["cluster_id"] or r["secondary_cluster_id"] == row["cluster_id"])]
        if related:
            st.dataframe(insight_table(related), hide_index=True, width="stretch", column_config={"Page": st.column_config.LinkColumn()})
        else:
            st.caption("No related pages are confidently assigned to this topic in the saved content.")
    with panels[3]:
        path = homepage_path(snapshot, focus_url)
        if path:
            st.caption(f"One shortest followed HTML path: {len(path) - 1} link(s). This is a discovery path, not every internal link.")
            st.dataframe(pd.DataFrame([{"Step": i, "Page": url} for i, url in enumerate(path)]), hide_index=True, width="stretch", column_config={"Page": st.column_config.LinkColumn()})
        else:
            st.warning(f"No path from the homepage was observed. This page belongs to a group of {row['orphan_group_size']} known unreachable page(s); the group may contain links between its members." if snapshot["meta"].get("reachability_known") else "The homepage was not validated in this snapshot. Reachability cannot be established from the available root crawl.")
            isolated = [r for r in snapshot["pages"] if r["orphan_group"] == row["orphan_group"] and r["orphan_group"] is not None]
            if isolated:
                st.dataframe(insight_table(isolated), hide_index=True, width="stretch", column_config={"Page": st.column_config.LinkColumn()})


def render_priority_pages(st, profile, snapshot):
    st.caption(f"{snapshot['meta']['known_pages']:,} known URLs · {snapshot['meta']['validated_pages']:,} validated HTML pages. Filters change this view only; they do not crawl the site.")
    if snapshot["meta"]["partial"]:
        st.warning("Crawl coverage is partial. Orphan, cluster and missing-link findings describe the available inventory.")
    cols = st.columns(3)
    issues = cols[0].multiselect("Show issues", INSIGHT_FILTERS, placeholder="All issues / pages", key="issue_filter_" + profile["id"])
    role = cols[1].selectbox("Page type", ["All", "Core", "Blog", "Other"], key="role_filter_" + profile["id"])
    search = cols[2].text_input("Find a page or topic", key="insight_search_" + profile["id"])
    rows = filter_insight_pages(snapshot, issues, role, search=search.strip())
    rows.sort(key=lambda r: (r["review_priority"], r["proposed_links"], finite_number(r["nonbrand_impressions"], 0)), reverse=True)
    st.caption(f"{len(rows):,} matching pages. Review priority combines observed structure and available opportunities; it is not an authority score.")
    if not rows:
        st.info("No pages match these filters. Try a different issue, page type or search.")
        return
    visible = rows[:100]
    event = st.dataframe(insight_table(visible), hide_index=True, width="stretch", on_select="rerun", selection_mode="single-row",
                         key="priority_table_" + profile["id"] + digest([issues, role, search, snapshot["meta"]["signature"]])[:10],
                         column_config={"Page": st.column_config.LinkColumn(), "Next action": st.column_config.TextColumn(width="large")})
    if len(rows) > len(visible):
        st.caption("The table shows the first 100 matches. Narrow the filters or search to inspect another page.")
    focus_key = "insight_focus_" + profile["id"]
    selected_rows = event.selection.rows
    if selected_rows:
        signal = digest([issues, role, search, visible[selected_rows[0]]["url"]])
        if st.session_state.get(focus_key + "_signal") != signal:
            st.session_state[focus_key] = visible[selected_rows[0]]["url"]
            st.session_state[focus_key + "_signal"] = signal
    choices = [r["url"] for r in visible]
    if st.session_state.get(focus_key) not in choices:
        st.session_state[focus_key] = choices[0]
    focus = st.selectbox("Inspect a page", choices, key=focus_key)
    render_page_focus(st, profile, snapshot, focus, "priority_" + profile["id"])
    with st.expander("Crawl issues and interpretation"):
        for warning in snapshot["meta"]["warnings"]:
            st.write(warning)
        issues_frame = pd.DataFrame(cached_dataset(st, profile, "audit")["rows"])
        if not issues_frame.empty:
            st.dataframe(issues_frame, hide_index=True, width="stretch")


def render_cluster_editor(st, profile, snapshot):
    with st.expander("Correct clusters or main pages (optional)"):
        names = {c["cluster_id"]: c["cluster"] for c in snapshot["clusters"]}
        types = {c["cluster_id"]: c.get("type", "") for c in snapshot["clusters"]}
        urls = [r["url"] for r in snapshot["pages"] if r["active"] and r["valid_html"]]
        if names:
            cid = st.selectbox("Cluster to edit", list(names), format_func=lambda c: f"{names[c]} ({types[c]})", key="edit_cluster_" + profile["id"])
            cluster = next(c for c in snapshot["clusters"] if c["cluster_id"] == cid)
            with st.form("cluster_edit_" + profile["id"] + cid):
                label = st.text_input("Cluster name", cluster["cluster"])
                hub_choices = [""] + urls
                hub = st.selectbox("Main page", hub_choices, index=hub_choices.index(cluster["hub_url"]) if cluster["hub_url"] in hub_choices else 0,
                                   format_func=lambda u: u or "No confirmed main page", help="Choosing a page also assigns it to this cluster.")
                if st.form_submit_button("Save cluster"):
                    if not label.strip():
                        st.error("Enter a cluster name.")
                    else:
                        cfg = insight_settings(profile)
                        cfg["names"][cid], cfg["hubs"][cid] = label.strip(), hub
                        if hub:
                            cfg["assignments"][hub] = cid
                            for other in list(cfg["hubs"]):
                                if other != cid and cfg["hubs"][other] == hub:
                                    cfg["hubs"][other] = ""
                        atomic_json(client_dir(profile) / "topic_settings.json", cfg)
                        st.rerun()
            with st.form("page_assignment_" + profile["id"]):
                page = st.selectbox("Page to assign", urls)
                assignment = st.selectbox("Assign to", ["unassigned"] + list(names), format_func=lambda c: names.get(c, "Unassigned / no confident topic"))
                if st.form_submit_button("Save page assignment") and page:
                    cfg = insight_settings(profile)
                    cfg["assignments"][page] = assignment
                    for other in list(cfg["hubs"]):
                        if other != assignment and cfg["hubs"][other] == page:
                            cfg["hubs"][other] = ""
                    atomic_json(client_dir(profile) / "topic_settings.json", cfg)
                    st.rerun()
        with st.form("new_cluster_" + profile["id"]):
            name = st.text_input("Add a cluster / seed topic", placeholder="e.g. automated document scanning")
            hub = st.selectbox("Main page for new cluster (optional)", [""] + urls, format_func=lambda u: u or "No confirmed main page")
            if st.form_submit_button("Add cluster"):
                if not name.strip():
                    st.error("Enter a topic name.")
                else:
                    cfg = insight_settings(profile)
                    cid = "custom_" + uuid.uuid4().hex[:12]
                    cfg["custom_clusters"].append({"id": cid, "name": name.strip(), "hub": hub})
                    if hub:
                        cfg["assignments"][hub] = cid
                        cfg["hubs"][cid] = hub
                        for other in list(cfg["hubs"]):
                            if other != cid and cfg["hubs"][other] == hub:
                                cfg["hubs"][other] = ""
                    atomic_json(client_dir(profile) / "topic_settings.json", cfg)
                    st.rerun()


def render_cluster_explorer(st, profile, snapshot):
    st.caption("Topic coverage, contextual connections and GSC visibility are separate signals. Cluster assignments are editable estimates, not a Google topical-authority score. "
               "'Inferred topic' clusters group related pages that fit no core page.")
    names = {c["cluster_id"]: c["cluster"] for c in snapshot["clusters"]}
    types = {c["cluster_id"]: c.get("type", "") for c in snapshot["clusters"]}
    selected = st.multiselect("Explore clusters", list(names), format_func=lambda cid: f"{names[cid]} ({types[cid]})", placeholder="Overview of all clusters", key="cluster_filter_" + profile["id"])
    only_weak = st.checkbox("Only clusters needing review", value=True, key="weak_clusters_" + profile["id"])
    clusters = [c for c in snapshot["clusters"] if (not selected or c["cluster_id"] in selected) and (not only_weak or c["needs_attention"])]
    if clusters:
        frame = pd.DataFrame(clusters).rename(columns={"cluster": "Cluster", "type": "Type", "hub_url": "Main page", "support_pages": "Supporting pages", "support_linking_to_hub": "Support pages linking to hub",
                                                    "hub_linking_to_support": "Hub links to support", "hub_support_percent": "Hub support (%)", "verified_link_opportunities": "Verified opportunities",
                                                    "query_opportunities": "Query opportunities", "unreachable_pages": "Unreachable pages", "issues": "Review reasons"})
        st.dataframe(frame.reindex(columns=["Cluster", "Type", "Main page", "Supporting pages", "Support pages linking to hub", "Hub links to support", "Hub support (%)", "Verified opportunities", "Query opportunities", "Unreachable pages", "Review reasons"]),
                     hide_index=True, width="stretch", column_config={"Main page": st.column_config.LinkColumn()})
        chart = cluster_support_chart(clusters)
        if chart is not None:
            st.plotly_chart(chart, width="stretch", key="cluster_support_" + profile["id"])
            st.caption("Up to 15 clusters with the lowest observed hub support. Unknown link-position evidence is excluded from this percentage, not shown as zero.")
    else:
        st.info("No clusters match this selection. Clear the review-only filter to see other clusters.")
    if selected:
        members = filter_insight_pages(snapshot, clusters=selected)
        if members:
            members.sort(key=lambda r: (r["is_hub"], r["review_priority"]), reverse=True)
            st.dataframe(insight_table(members), hide_index=True, width="stretch", column_config={"Page": st.column_config.LinkColumn()})
            focus = st.selectbox("Inspect a page in these clusters", [r["url"] for r in members], key="cluster_focus_" + profile["id"] + digest(selected)[:8])
            render_page_focus(st, profile, snapshot, focus, "cluster_" + profile["id"], selected, entire_cluster=True)
        selected_urls = {p["url"] for p in snapshot["pages"] if p["cluster_id"] in selected}
        cross = [r for r in snapshot["cross_reviews"] if r["source_url"] in selected_urls]
        if cross:
            with st.expander("Cross-topic links to review"):
                st.caption("These are low-similarity links between inferred topics. They may be useful bridges; review the sentence before changing anything.")
                st.dataframe(pd.DataFrame(cross), hide_index=True, width="stretch")
    with st.expander("Explore seed keywords and coverage gaps (optional)"):
        st.caption("Searches the saved content and visible GSC queries. It does not crawl again or establish search volume for missing topics.")
        with st.form("seed_check_" + profile["id"]):
            seed_text = st.text_area("Seed keywords — one per line, up to 20", placeholder="document scanning\ninvoice processing")
            submitted = st.form_submit_button("Check seed topics")
        if submitted:
            seeds = [s.strip() for s in seed_text.splitlines() if s.strip()]
            if not seeds:
                st.info("Enter at least one seed topic.")
            else:
                with st.spinner("Checking seed topics against saved content…"):
                    seed_cluster_check(profile, seeds, snapshot)
        checks = cached_dataset(st, profile, "seed_checks")
        if checks["rows"]:
            if checks["meta"].get("insight_signature") != snapshot["meta"]["signature"]:
                st.warning("Saved seed checks predate the latest crawl or cluster corrections. Run the check again to refresh them.")
            st.dataframe(pd.DataFrame(checks["rows"]), hide_index=True, width="stretch")
            seed = st.selectbox("Seed to inspect", [r["seed"] for r in checks["rows"]], key="seed_detail_" + profile["id"])
            matching = [r for r in cached_dataset(st, profile, "seed_pages")["rows"] if r["seed"] == seed]
            if matching:
                st.dataframe(pd.DataFrame(matching)[["url", "page_type", "cluster", "match_evidence", "visible_matching_queries", "matching_query_impressions", "topic_similarity"]], hide_index=True, width="stretch")
            st.caption("A gap means no suitable page was found in the available content. Confirm business fit, keyword demand and crawl coverage before creating a new page. Use 'Add a cluster / seed topic' below to track a seed as its own cluster.")
    render_cluster_editor(st, profile, snapshot)
    export_key = digest([snapshot["meta"]["signature"], cached_dataset(st, profile, "seed_checks")["meta"].get("created_at")])[:16]
    output = client_dir(profile) / "exports" / f"cluster_insights_{export_key}.xlsx"
    if not output.is_file():
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(workbook_bytes([profile], ["Core pages", "Priority pages", "Topic clusters", "Cluster link reviews", "Seed checks"]))
        prune_files(output.parent, "cluster_insights_*.xlsx", keep=5)
    st.download_button("Download current cluster insights", output.read_bytes(), file_name=output.name,
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", on_click="ignore")


def render_simple_results(st, profile, job_active=False):
    result = cached_dataset(st, profile, "result")["meta"]
    if not result:
        st.caption("Select a client and click Find opportunities. Core pages, analysis, charts and workbook are prepared automatically.")
        return
    crawl_meta = cached_dataset(st, profile, "pages")["meta"]
    if crawl_meta.get("source") == "Built-in HTML crawl" and crawl_meta.get("crawl_schema", 0) < CRAWL_SCHEMA:
        st.warning("This saved crawl was made by an older version with less accurate core-page, canonical and page-region detection. Click Find opportunities to rebuild it.")
        return
    cols = st.columns(4)
    for column, label, key in zip(cols, ["Blog pages checked", "Core pages detected", "GSC page/query pairs", "Link opportunities"], ["blogs", "core_pages", "query_pairs", "opportunities"]):
        column.metric(label, result.get(key, 0))
    if result.get("invalid_canonicals"):
        st.warning(f"{result['invalid_canonicals']} page(s) have canonical tags pointing to broken, redirecting or noindex URLs. "
                   "Filter Priority pages by 'Invalid canonical' to see them.")
    workbook = Path(result.get("workbook", ""))
    if workbook.is_file():
        st.download_button("Download workbook", workbook.read_bytes(), file_name=workbook.name,
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", on_click="ignore", type="primary")
    st.caption(f"Last completed: {result.get('created_at', '')} · {result.get('crawl_source', '')}")
    render_core_editor(st, profile, job_active)
    if result.get("warnings"):
        with st.expander("Run notes / coverage"):
            for warning in result["warnings"]:
                st.write(warning)
    snapshot, previous = None, False
    try:
        snapshot, previous = explorer_for_ui(st, profile, job_active)
    except Exception as exc:
        st.error("Insights could not be prepared from the saved data: " + safe_error(exc) + " Click Find opportunities to rebuild them.")
    if previous and snapshot is not None:
        st.info("A run is updating this client. Priority pages and clusters show the previous results until it finishes.")
    tabs = st.tabs(["Priority pages", "Opportunities", "GSC queries", "Clusters"])
    with tabs[0]:
        if snapshot is not None:
            render_priority_pages(st, profile, snapshot)
        else:
            st.info("Priority pages will appear when the current run finishes.")
    recs_doc = cached_dataset(st, profile, "recommendations")
    recs, rec_meta = recs_doc["rows"], recs_doc["meta"]
    with tabs[1]:
        if not result.get("anchor_text") and rec_meta.get("matching_strategy") != "gsc_exact_queries":
            st.warning("These saved recommendations predate the exact GSC query workflow. Click Find opportunities to rebuild them.")
        elif rec_meta.get("matching_strategy") == "gsc_exact_queries" and not rec_meta.get("query_data_available"):
            st.warning("No GSC page/query data was available. Connect Google and click Find opportunities to generate query-based suggestions, or enter a manual anchor.")
        st.caption("Query impressions and average position belong to the exact query on the destination URL. Priority is a heuristic; internal links do not guarantee a ranking improvement.")
        if recs:
            df = pd.DataFrame(recs).rename(columns={"source_url": "Source page", "destination_url": "Destination page", "anchor_text": "Anchor text", "context": "Existing paragraph", "priority": "Priority",
                                                  "supporting_query": "GSC query", "query_impressions": "Query impressions", "query_position": "Average position",
                                                  "query_clicks": "Query clicks", "evidence_type": "Evidence", "reason": "Why this opportunity"})
            columns = ["Source page", "Destination page", "Anchor text", "GSC query", "Query impressions", "Average position", "Query clicks", "Priority", "Evidence", "Existing paragraph", "Why this opportunity"]
            st.dataframe(df.reindex(columns=columns), hide_index=True, width="stretch",
                         column_config={"Source page": st.column_config.LinkColumn(), "Destination page": st.column_config.LinkColumn(), "Existing paragraph": st.column_config.TextColumn(width="large"),
                                        "Average position": st.column_config.NumberColumn(format="%.1f"), "Query impressions": st.column_config.NumberColumn(format="%d")})
        else:
            st.info("No eligible exact query mentions were found, or the matching phrases were already linked or ambiguous. Check the GSC queries tab and Run notes for data and coverage.")
    with tabs[2]:
        query_doc = cached_dataset(st, profile, "gsc_queries")
        meta = query_doc["meta"]
        if not query_doc["rows"]:
            st.info("No visible non-brand page/query rows are saved for this client. Connect Google and run Find opportunities. Empty data is not treated as zero search demand.")
        else:
            st.caption(f"{meta.get('start_date', '')} to {meta.get('end_date', '')} · {meta.get('brand_method', '')} · {len(query_doc['rows']):,} query/page pairs")
            if profile.get("demo"):
                st.info("Demo queries and metrics are synthetic.")
            frame = pd.DataFrame(query_doc["rows"])
            choices = [""] + sorted(frame["page"].unique().tolist())
            selected_page = st.selectbox("Page", choices, format_func=lambda u: u or "All pages", key="gsc_page_" + profile["id"])
            if selected_page:
                frame = frame[frame["page"] == selected_page]
            search = st.text_input("Find a query", key="gsc_query_" + profile["id"], placeholder="e.g. automated document scanning")
            if search.strip():
                frame = frame[frame["query"].str.contains(search.strip(), case=False, regex=False, na=False)]
            frame = frame.copy()
            frame["Core destination"] = frame["page"].isin({c["url"] for c in profile.get("core_pages", [])})
            frame["CTR (%)"] = frame["ctr"] * 100
            frame = frame.rename(columns={"page": "Page", "query": "Query", "impressions": "Impressions", "position": "Average position", "clicks": "Clicks"})
            st.dataframe(frame[["Page", "Query", "Impressions", "Average position", "Clicks", "CTR (%)", "Core destination"]].sort_values("Impressions", ascending=False),
                         hide_index=True, width="stretch", column_config={"Page": st.column_config.LinkColumn(), "Average position": st.column_config.NumberColumn(format="%.1f"), "CTR (%)": st.column_config.NumberColumn(format="%.2f")})
            st.caption(meta.get("query_coverage", "Only visible GSC query rows are available; Google may omit queries for privacy and other API limits."))
    with tabs[3]:
        if snapshot is not None:
            render_cluster_explorer(st, profile, snapshot)
        else:
            st.info("Clusters will appear when the current run finishes.")


TERMINAL_STATES = {"completed", "cancelled", "failed", "completed_with_errors"}


def request_job_cancel(job_id):
    folder = DATA_DIR / "jobs" / job_id
    if not folder.is_dir():
        return False
    try:
        if read_json(folder / "status.json", {}).get("state") not in {"queued", "running"}:
            return False
        (folder / "cancel").touch()
        return True
    except FileNotFoundError:
        return False


def job_for_client(job_id, client_id):
    if not job_id:
        return False
    job = read_json(DATA_DIR / "jobs" / job_id / "job.json", {})
    return any(p.get("id") == client_id for p in job.get("profiles", []))


def finish_session_job(session, job_id, status, client_id):
    if session.get("active_job") == job_id:
        session.pop("active_job", None)
    session["last_job_notice"] = {"client_id": client_id, "job_id": job_id, **status}


def render_live_progress(st, job_id, client_id):
    @st.fragment(run_every="1s")
    def monitor():
        folder = DATA_DIR / "jobs" / job_id
        status = read_json(folder / "status.json", {})
        if not status:
            finish_session_job(st.session_state, job_id, {"state": "failed", "errors": [{"error": "Run storage was reset. Start a new run."}]}, client_id)
            st.rerun()
        state = status.get("state", "queued")
        if state in TERMINAL_STATES:
            finish_session_job(st.session_state, job_id, status, client_id)
            st.rerun()  # Full rerun removes this timed fragment entirely.
        step = f"Step {status.get('phase_index', 0) + 1}/{status.get('phase_count', 6)}"
        st.progress(float(max(0, min(1, status.get("overall_progress", 0)))), text=f"{step} · {status.get('stage', 'Starting…')} · {status.get('message', '')}")
        if status.get("total"):
            st.caption(f"{status.get('done', 0):,} of {status['total']:,} items in the current stage. Crawl totals may grow as new pages are discovered.")
        if st.button("Stop", key="stop_" + job_id):
            if request_job_cancel(job_id):
                st.info("Stopping after active requests finish…")
            else:
                st.rerun()
        with st.expander("Progress details"):
            log_file = folder / "worker.log"
            if log_file.is_file():
                st.code(log_file.read_text(encoding="utf-8", errors="replace")[-6000:], language="text")
    monitor()


def main():
    import streamlit as st
    st.set_page_config(page_title="Internal linking opportunities", page_icon="🔗", layout="wide")
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    # Migrate only the harmless crawl limit; security/runtime options are never user preferences.
    previous_settings = read_json(DATA_DIR / "settings.json", {})
    try:
        previous_limit = max(100, min(20000, int(previous_settings.get("crawl_limit", 2000))))
    except (TypeError, ValueError):
        previous_limit = 2000
    settings = st.session_state.setdefault("_crawl_settings", {"crawl_limit": previous_limit, "min_query_words": 2})
    password = str(secret_value(st, "app_password"))
    secret_token = secret_value(st, "gsc_token_json")
    secret_client = secret_value(st, "google_client_secret_json") or secret_value(st, "google_client_secret_path")
    profiles = read_json(DATA_DIR / "profiles.json", [])
    legacy_token = DATA_DIR / "auth" / "gsc_token.json"
    has_private_data = any(not p.get("demo") and (client_dir(p) / "gsc_pages.json").exists() for p in profiles)
    runtime_mode = deployment_mode()
    if runtime_mode != "local" and not password and (secret_client or secret_token or legacy_token.exists() or has_private_data):
        st.title("Internal linking opportunities")
        st.info("Add an app password in Streamlit Secrets before connecting or viewing client Search Console data.")
        st.code('app_password = "choose-a-private-password"', language="toml")
        st.stop()
    if password and not st.session_state.get("_authenticated"):
        st.title("Internal linking opportunities")
        entered = st.text_input("App password", type="password")
        if st.button("Sign in"):
            if hmac.compare_digest(entered.encode(), password.encode()):
                st.session_state["_authenticated"] = True
                st.rerun()
            else:
                st.error("Incorrect password.")
        st.stop()
    st.title("Internal linking opportunities")
    st.caption("GSC queries → exact unlinked mentions → core pages. Core pages come from the main navigation, the footer and site-wide links, and you can edit them.")
    # Migrate the v1 generated token into authenticated session memory, then remove
    # that plaintext copy. Credentials are never written back to the filesystem.
    if legacy_token.is_file():
        try:
            st.session_state.setdefault("gsc_credentials", validate_token_info(read_json(legacy_token)))
            legacy_token.unlink()
        except (ValueError, OSError):
            pass
    info = st.session_state.get("gsc_credentials")
    if not info and secret_token and not st.session_state.get("skip_secret_token"):
        try:
            info = validate_token_info(json.loads(secret_token) if isinstance(secret_token, str) else dict(secret_token))
            st.session_state["gsc_credentials"] = info
        except ValueError:
            info = None
    if info and not profiles and not st.session_state.get("auto_connection_attempted"):
        st.session_state["auto_connection_attempted"] = True
        try:
            info, _ = run_google_connection(st, info=info)
            profiles = read_json(DATA_DIR / "profiles.json", [])
        except Exception as exc:
            st.warning(safe_error(exc))
    google_panel = st.sidebar.container()
    st.sidebar.caption("Optional crawl controls")
    with st.sidebar.expander("Connection & crawl options", expanded=False):
        runtime = runtime_mode
        st.caption("This computer · desktop crawling enabled by the operator" if runtime == "local" else "Streamlit Cloud · automatic web crawl")
        settings["refresh_crawl"] = st.checkbox("Refresh saved crawl and GSC data", value=False)
        settings["crawl_limit"] = int(st.number_input("Maximum pages per crawl", 100, 20000, int(settings.get("crawl_limit", 2000)), 100))
        settings["min_query_words"] = int(st.number_input("Minimum words in a query anchor", 1, 6, int(settings.get("min_query_words", 2)),
                                                           help="One-word queries match almost everywhere; 2 or more keeps suggestions specific."))
        if runtime == "local":
            settings["sf_path"] = st.text_input("Screaming Frog CLI path (optional)", settings.get("sf_path", os.environ.get("INTERNAL_LINK_SF_PATH", "")))
        token_upload = st.file_uploader("Google JSON file (optional)", type="json", help="Accepts the downloaded Google client configuration or an existing authorized token. No upload is needed when google_client_secret_json is configured in Secrets.")
        site_url = st.text_input("Add a website without GSC (optional)", placeholder="https://example.com/")
        if st.button("Add website"):
            if url_key(site_url):
                profile = default_profile(urlsplit(site_url).hostname or "Client", site_url)
                automatic_brand_terms(profile)
                save_working_profile(profile)
                st.session_state["selected_client"] = profile["id"]
                st.rerun()
            else:
                st.error("Enter a complete https:// website URL.")
        if st.button("Try demo"):
            demo = install_demo()
            st.session_state["selected_client"] = demo["id"]
            st.rerun()
        if profiles:
            with st.popover("Use Screaming Frog exports (optional)"):
                current_id = st.session_state.get("selected_client") or profiles[0]["id"]
                current_profile = next((p for p in profiles if p["id"] == current_id), profiles[0])
                st.caption(f"For {current_profile['name']}. Automatic web crawling needs no uploads. Use these exports if the site blocks access or needs rendered HTML.")
                internal_csv = st.file_uploader("Internal:All CSV", type="csv")
                inlinks_csv = st.file_uploader("All Inlinks CSV", type="csv")
                content_csv = st.file_uploader("Optional HTML extraction CSV (Address + HTML)", type="csv")
                if st.button("Use these crawl files", disabled=internal_csv is None or inlinks_csv is None):
                    try:
                        save_crawl(current_profile, read_sf_csv(io.BytesIO(internal_csv.getvalue())), read_sf_csv(io.BytesIO(inlinks_csv.getvalue())), "Imported Screaming Frog exports")
                        if content_csv:
                            import_html_csv(current_profile, io.BytesIO(content_csv.getvalue()))
                        st.success("Crawl imported. Click Find opportunities to prepare all results.")
                    except Exception as exc:
                        st.error(safe_error(exc))
    with google_panel:
        try:
            config = load_google_client_config(st, runtime)
            uploaded = json.loads(token_upload.getvalue().decode("utf-8-sig")) if token_upload else None
            if isinstance(uploaded, dict) and ("web" in uploaded or "installed" in uploaded):
                config = validate_google_client_config(uploaded)
                uploaded = None
            render_google_connection(st, config, runtime, password, info, uploaded)
        except (ValueError, ImportError) as exc:
            st.error(safe_error(exc))
    if not profiles:
        st.info("Click Connect Google in the sidebar to load your clients. You can also add a website or try the demo under Connection & crawl options.")
        return
    ids = [p["id"] for p in profiles]
    if st.session_state.get("selected_client") not in ids:
        st.session_state["selected_client"] = None
    selected = st.selectbox("Client", ids, index=None, placeholder="Choose a client…", key="selected_client",
                            format_func=lambda x: next(p["name"] for p in profiles if p["id"] == x))
    if not selected:
        st.info("Choose a client first. Crawling, Search Console performance data and analysis start only after you click Find opportunities.")
        return
    profile = next(p for p in profiles if p["id"] == selected)
    if profile.get("demo"):
        st.info("Demo: all pages and metrics are synthetic. No external crawl or Google request will run.")
    anchor = st.text_input("Anchor text (optional)", placeholder="Leave blank for automatic suggestions, or enter e.g. options data API")
    destination = ""
    if anchor and profile.get("core_pages"):
        with st.expander("Choose a destination for this anchor (optional)"):
            choices = [""] + [c["url"] for c in profile["core_pages"]]
            destination = st.selectbox("Link to", choices, format_func=lambda x: x or "Automatically choose a relevant core page")
    active = read_job_lock().get("job_id")
    if active:
        folder = DATA_DIR / "jobs" / active
        active_status = read_json(folder / "status.json", {})
        record = read_json(folder / "process.json", {})
        if active_status.get("state") in TERMINAL_STATES or (record and not process_alive(record)):
            if active_status.get("state") in {"queued", "running"}:
                active_status.update(state="failed", errors=[{"error": "The worker stopped unexpectedly. You can start the run again."}])
                atomic_json(folder / "status.json", active_status)
            release_job_lock(active)
            active = None
    if st.button("Find opportunities", type="primary", disabled=bool(active)):
        try:
            options = {**settings, "anchor_text": anchor.strip(), "destination_url": destination}
            job_id = create_job([profile], [], options, credentials_info=st.session_state.get("gsc_credentials"), workflow="simple")
            st.session_state["active_job"] = job_id
            st.rerun()
        except Exception as exc:
            st.error(safe_error(exc))
    remembered = st.session_state.get("active_job")
    if remembered and not (DATA_DIR / "jobs" / remembered / "job.json").is_file():
        st.session_state.pop("active_job", None)
        remembered = None
    job_id = active if job_for_client(active, selected) else remembered if job_for_client(remembered, selected) else None
    if active and not job_for_client(active, selected):
        st.caption("Another client's run is active. You can inspect saved results while it finishes.")
    if job_id:
        render_live_progress(st, job_id, selected)
    notice = st.session_state.get("last_job_notice")
    if notice and notice.get("client_id") == selected:
        st.session_state.pop("last_job_notice", None)
        if notice.get("state") == "completed":
            st.success("Opportunities, analysis, charts and workbook are ready.")
        elif notice.get("state") == "cancelled":
            st.info("Stopped. Previously completed results remain available.")
        else:
            errors = notice.get("errors", [])
            st.error(errors[-1].get("error", "The run could not finish.") if errors else "The run could not finish.")
    render_simple_results(st, profile, job_active=bool(active and job_for_client(active, selected)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--worker", type=Path)
    parser.add_argument("--local", action="store_true", help="Enable desktop tools on a trusted local server.")
    args, _ = parser.parse_known_args()
    if args.local:
        os.environ["INTERNAL_LINK_MODE"] = "local"
    if args.worker:
        worker_main(args.worker)
    else:
        main()
