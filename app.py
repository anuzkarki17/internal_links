"""Internal linking opportunities — select a client, optionally enter an anchor,
then click Find opportunities. Navigation/footer core-page discovery, crawling,
GSC enrichment, matching, audit, charts and workbook generation run together.

GitHub: commit app.py and requirements.txt; Streamlit entrypoint is app.py.
Optional one-time Secrets:
    app_password = "a-private-password"
    gsc_token_json = '<the complete authorized GSC token JSON>'

Google credentials stay in memory and travel to a background worker through a
stdin pipe. Never commit credentials. Cloud mode uses a bounded HTML crawler;
local mode uses the installed Screaming Frog CLI when available. Saved crawl
results are reused for 24 hours unless Refresh is selected in the collapsed
connection/crawl drawer. Host storage can be reset on redeploy/reboot.
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import hmac
import ipaddress
import io
import json
import math
import os
import platform
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import unicodedata
import uuid
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed, wait, FIRST_COMPLETED
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit
from urllib.robotparser import RobotFileParser
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("INTERNAL_LINK_DATA_DIR", str(APP_DIR / "data"))).expanduser().resolve()
APP_VERSION = "2.0.0"
GOOGLE_CREDENTIALS_INFO = None  # Worker memory only; never included in job JSON.
UA = "CadenceInternalLinks/1.0"
SCOPES = ["https://www.googleapis.com/auth/webmasters.readonly"]
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
}
EMPTY_EXCLUSIONS = r"/(?:privacy(?:-policy)?|terms(?:-and-conditions)?|login|cart|checkout|account|search|tag|author)(?:/|$)"
TOKEN_RE = re.compile(r"[\w]+(?:[-’'][\w]+)*", re.UNICODE)
BAD_EDGE = set("a an the this that these those our your their its for to of in on at by with from and or but as is are was were be been being can could would should will may might how what why when where which who we you they it also more most very such into through than then have has had do does did using use used help helps improve improves including include includes provides provide offers offer".split())
GENERIC = set("company companies solution solutions service services product products information learn read more here click website page pages business businesses system systems tool tools technology technologies guide best good new support need needs help including provide provides offer offers".split())
GENERIC_ANCHORS = {"click here", "here", "read more", "learn more", "more", "this", "this page", "this link", "website", "link", "view more", "find out more", "details", "more information"}


class Cancelled(RuntimeError):
    pass


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
            json.dump(value, handle, ensure_ascii=False, indent=2, allow_nan=False, default=str)
        if private:
            try:
                temp.chmod(0o600)
            except OSError:
                pass
        os.replace(temp, path)
    finally:
        temp.unlink(missing_ok=True)


def read_json(path, default=None):
    path = Path(path)
    if not path.exists():
        return default
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def client_dir(profile):
    return DATA_DIR / "clients" / slug(profile["id"])


def save_dataset(profile, name, rows, **meta):
    atomic_json(client_dir(profile) / f"{name}.json", {"meta": {"created_at": utc_now(), "app_version": APP_VERSION, **meta}, "rows": rows})


def dataset(profile, name):
    return read_json(client_dir(profile) / f"{name}.json", {"meta": {}, "rows": []})


def input_signature(profile, names):
    stamps = {}
    for name in names:
        path = client_dir(profile) / f"{name}.json"
        stamps[name] = hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None
    return digest({"profile": profile, "datasets": stamps})


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


def site_hosts(profile):
    root = urlsplit(profile["root_url"]).hostname or ""
    return {root.lower(), *[x.strip().lower() for x in profile.get("allowed_hosts", []) if x.strip()]}


def same_site(url, profile):
    return bool(url_key(url)) and (urlsplit(url).hostname or "").lower() in site_hosts(profile)


def is_home(url, profile):
    return url_key(url) == url_key(profile["root_url"]) or urlsplit(url).path in {"", "/"}


def is_blog(url, profile):
    if url_key(url) in profile.get("blog_urls", []):
        return True
    path = urlsplit(url).path
    leaf = path.strip("/").split("/")[-1].lower()
    if leaf in {"blog", "blogs", "resources", "articles", "insights", "news"}:
        return False
    if re.search(r"/(?:tag|tags|author|authors|category|categories|page)/", path, re.I):
        return False
    return bool(re.search(profile.get("blog_pattern", r"/(blog|resources|articles|insights)/"), path, re.I))


def excluded(url, profile):
    return bool(profile.get("exclude_pattern") and re.search(profile["exclude_pattern"], urlsplit(url).path, re.I))


def phrase_pattern(phrase):
    words = text_norm(phrase).split()
    return re.compile(r"(?<!\w)" + r"\s+".join(re.escape(x) for x in words) + r"(?!\w)", re.I) if words else re.compile(r"(?!)")


def brand_pattern(profile):
    terms = [text_norm(x) for x in profile.get("brand_terms", []) if text_norm(x)]
    body = "|".join(r"\s+".join(re.escape(w) for w in term.split()) for term in sorted(terms, key=len, reverse=True))
    return re.compile(r"(?<!\w)(?:" + body + r")(?!\w)", re.I) if body else re.compile(r"(?!)")


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
        "sf_config": "", "sitemap_urls": [],
    }


def validate_profile(profile):
    if not url_key(profile.get("root_url", "")):
        raise ValueError("Enter a complete http(s) crawl URL.")
    for name in ["blog_pattern", "exclude_pattern"]:
        try:
            re.compile(profile.get(name, ""))
        except re.error as exc:
            raise ValueError(f"Invalid {name}: {exc}") from exc
    if profile.get("main_selector"):
        from bs4 import BeautifulSoup
        BeautifulSoup("<main></main>", "lxml").select(profile["main_selector"])
    for core in profile.get("core_pages", []):
        if not same_site(core["url"], profile):
            raise ValueError(f"Core page is outside the allowed hosts: {core['url']}")


def aliases_for(pages, profile):
    mapping = {}
    for p in pages:
        url = url_key(p["url"])
        redirect = url_key(p.get("redirect", ""))
        canonical = url_key(p.get("canonical", ""))
        if 300 <= int(p.get("status") or 0) < 400 and same_site(redirect, profile):
            mapping[url] = redirect
        elif "canonical" in p.get("indexability_status", "").lower() and not p.get("indexable") and same_site(canonical, profile) and canonical != url:
            mapping[url] = canonical
    return mapping


def resolve_alias(url, mapping):
    value = url_key(url)
    seen = set()
    while value in mapping and value not in seen:
        seen.add(value)
        value = mapping[value]
    return value


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
        row["source_nofollow"] = bool(re.search(r"\bnofollow\b", row["meta_robots"] + " " + row["x_robots"], re.I))
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
    meta = {"links_verified": True, "position_available": bool(link_fields["position"]),
            "warnings": [] if link_fields["position"] else ["Link Position is missing. Contextual counts are unknown and existing hyperlink pairs are conservatively excluded from new recommendations."]}
    return list(pages.values()), links, meta


def save_crawl(profile, internal_df, inlinks_df, source, **extras):
    pages, links, meta = sf_tables(internal_df, inlinks_df, profile)
    generation = uuid.uuid4().hex
    save_dataset(profile, "pages", pages, generation=generation, source=source, **extras)
    save_dataset(profile, "links", links, generation=generation, source=source, **meta, **extras)
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
    if options.get("runtime_mode", "hosted") != "local":
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
    parts = urlsplit(url)
    if parts.scheme not in {"http", "https"} or not parts.hostname or parts.username or parts.password:
        raise ValueError("Enter a public http(s) website URL.")
    if os.environ.get("INTERNAL_LINK_ALLOW_PRIVATE") == "1":
        return
    try:
        literal = ipaddress.ip_address(parts.hostname)
        addresses = [literal]
    except ValueError:
        try:
            addresses = [ipaddress.ip_address(info[4][0]) for info in socket.getaddrinfo(parts.hostname, parts.port or (443 if parts.scheme == "https" else 80), type=socket.SOCK_STREAM)]
        except OSError as exc:
            raise ValueError("The website's public address could not be resolved.") from exc
    if not addresses or any(not address.is_global for address in addresses):
        raise ValueError("Only public websites can be crawled; private and local network addresses are blocked.")


def get_bytes(url, max_bytes=5_000_000):
    import requests
    current, first_redirect = url, None
    for _ in range(7):
        validate_public_url(current)
        with requests.get(current, headers={"User-Agent": UA}, timeout=(10, 35), allow_redirects=False, stream=True) as response:
            headers = {k.lower(): v for k, v in response.headers.items()}
            if response.status_code in {301, 302, 303, 307, 308} and headers.get("location"):
                first_redirect = first_redirect or response.status_code
                current = urljoin(current, headers["location"])
                continue
            data = bytearray()
            for part in response.iter_content(65536):
                data.extend(part)
                if len(data) > max_bytes:
                    raise ValueError(f"Response exceeded the {max_bytes:,}-byte limit.")
            if first_redirect:
                headers["__redirect_status__"] = str(first_redirect)
            return response.status_code, headers, response.url, bytes(data)
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


def extract_content(html, url, selector=""):
    from bs4 import BeautifulSoup
    soup = BeautifulSoup(html, "lxml")
    title = text_norm(soup.title.get_text(" ", strip=True)) if soup.title else ""
    h1 = text_norm(soup.h1.get_text(" ", strip=True)) if soup.h1 else ""
    canonical_tag = soup.find("link", rel=lambda value: value and "canonical" in value)
    canonical = url_key(urljoin(url, canonical_tag.get("href", ""))) if canonical_tag else ""
    robots = " ".join(t.get("content", "") for t in soup.find_all("meta", attrs={"name": re.compile(r"^(robots|googlebot)$", re.I)}))
    main = soup.select_one(selector) if selector else (soup.find("main") or soup.find(attrs={"role": "main"}) or soup.find("article") or soup.body)
    if main is None:
        return {"success": False, "error": "Main content selector did not match.", "paragraphs": [], "text": ""}
    headings = [text_norm(x.get_text(" ", strip=True)) for x in main.find_all(["h1", "h2", "h3"])]
    for node in list(main.select("script, style, noscript, svg, nav, footer, header, aside, form, button, [hidden], [aria-hidden='true'], [role='navigation'], [role='contentinfo'], .footer, .site-footer, .footer_wrap, .footer_component, .footer-wrapper, .navbar, .site-header, .related-posts, .related-articles, .breadcrumbs, .social-share")):
        if node.parent is not None:
            node.decompose()
    outgoing = [url_key(urljoin(url, a.get("href", ""))) for a in main.find_all("a", href=True)]
    paragraphs = []
    for block in main.find_all(["p", "li", "dd", "blockquote"]):
        if block.find(["p", "li", "dd", "blockquote"]):
            continue
        paragraph = text_norm(block.get_text(" ", strip=True))
        if len(paragraph.split()) < 7:
            continue
        clone = BeautifulSoup(str(block), "lxml")
        for anchor in clone.find_all("a"):
            anchor.replace_with(" \ufff0 ")
        segments = [text_norm(s) for s in clone.get_text(" ", strip=True).split("\ufff0")]
        paragraphs.append({"text": paragraph, "unlinked": [s for s in segments if s], "locator": css_path(block), "block": len(paragraphs) + 1})
    body = text_norm(main.get_text(" ", strip=True))
    return {"success": bool(body), "error": "" if body else "No extractable body text.", "title": title, "h1": h1,
            "headings": headings, "text": body, "paragraphs": paragraphs, "outgoing_content": sorted(set(filter(None, outgoing))),
            "canonical": canonical, "noindex": bool(re.search(r"\bnoindex\b", robots, re.I))}


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
        except Exception as exc:
            log(f"Could not discover sitemaps from robots.txt: {exc}")
        urls += [origin + "/sitemap.xml", origin + "/sitemap_index.xml"]
    queue, seen, found, errors = deque(dict.fromkeys(urls)), set(), set(), []
    cap = int(options.get("sitemap_cap", 50))
    while queue and len(seen) < cap:
        check_cancel()
        u = url_key(queue.popleft())
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
                queue.extend(locations)
            else:
                found.update(url_key(x) for x in locations if same_site(x, profile))
            if len(found) > 100_000:
                raise ValueError("Sitemap inventory exceeded 100,000 URLs. Split the scope before continuing.")
        except Exception as exc:
            errors.append(f"{u}: {exc}")
    if not found and errors:
        raise ValueError("No sitemap URLs could be loaded. " + "; ".join(errors[:3]))
    save_dataset(profile, "sitemaps", [{"url": u} for u in sorted(found)], partial=bool(queue), sitemaps_checked=len(seen), warnings=errors)
    log(f"Discovered {len(found):,} URLs from {len(seen):,} sitemap requests.")


CORE_SKIP = re.compile(r"^/(?:about(?:-us)?|our-company|our-team|company|contact(?:-us|-sales)?|support|help(?:-center)?|faq|faqs|careers?|jobs?|work-for-us|team|privacy(?:-policy)?|terms(?:-of-service)?|legal|cookies?(?:-policy)?|login|logout|sign-in|sign-up|signup|account|cart|checkout|search|tag|tags|authors?|categories|blog(?:-category|-categories)?|blogs|articles|insights|news|resources|case-studies|customer-stories|testimonials|webinars|docs|documentation|developers|api-status|sitemap|accessibility|request(?:-a)?-demo|book-a-demo)(?:/|$)", re.I)
BINARY_PATH = re.compile(r"\.(?:jpe?g|png|webp|gif|svg|ico|css|js|map|pdf|zip|gz|xml|mp4|mov|mp3|woff2?|ttf|eot|xlsx?|docx?|csv)(?:$|\?)", re.I)


def page_from_html(raw, url, profile, headers=None):
    """One parse supplies article detection, crawl edges and source text."""
    from bs4 import BeautifulSoup
    soup = BeautifulSoup(raw, "lxml")
    headers = headers or {}
    extracted = extract_content(raw, url, profile.get("main_selector", ""))
    noindex = extracted.get("noindex", False) or bool(re.search(r"\bnoindex\b", headers.get("x-robots-tag", ""), re.I))
    canonical = extracted.get("canonical") or url
    page = {"url": url, "status": 200, "html": True, "content_type": "text/html", "title": extracted.get("title", ""),
            "h1": extracted.get("h1", ""), "canonical": canonical, "redirect": "", "source_nofollow": False,
            "indexable": not noindex and canonical == url, "indexability_status": "noindex" if noindex else "Canonicalised" if canonical != url else ""}
    robots = " ".join(t.get("content", "") for t in soup.find_all("meta", attrs={"name": re.compile(r"^(robots|googlebot)$", re.I)}))
    page["source_nofollow"] = bool(re.search(r"\bnofollow\b", robots + " " + headers.get("x-robots-tag", ""), re.I))
    ogtype = soup.find("meta", attrs={"property": "og:type"})
    schema_text = " ".join(t.get_text() for t in soup.find_all("script", attrs={"type": "application/ld+json"}))
    article = (bool(ogtype and ogtype.get("content", "").lower() == "article") or bool(re.search(r'"(?:BlogPosting|NewsArticle|Article)"', schema_text)))
    page["article"] = article or is_blog(url, profile)
    edges = []
    for anchor in soup.find_all("a", href=True):
        destination = url_key(urljoin(url, anchor["href"]))
        if not same_site(destination, profile):
            continue
        position = "Content"
        for parent in [anchor, *list(anchor.parents)]:
            classes = " ".join(parent.get("class", [])) if hasattr(parent, "get") else ""
            role = parent.get("role", "") if hasattr(parent, "get") else ""
            if parent.name == "footer" or role == "contentinfo" or re.search(r"(?:^|[-_ ])footer(?:$|[-_ ])", classes, re.I):
                position = "Footer"
                break
            if parent.name in {"nav", "header"} or role == "navigation" or re.search(r"(?:^|[-_ ])(?:nav|navbar|navigation|menu|header)(?:$|[-_ ])", classes, re.I):
                position = "Navigation"
                break
        image = anchor.find("img")
        edges.append({"source": url, "destination": destination, "anchor": text_norm(anchor.get_text(" ", strip=True)),
                      "alt": image.get("alt", "") if image else "", "position": position, "position_known": True,
                      "contextual": position == "Content", "type": "Hyperlink", "locator": "",
                      "followable": "nofollow" not in anchor.get("rel", []) and not page["source_nofollow"]})
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
                    if set(kinds) & {"Organization", "Corporation"} and value.get("name"):
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


def infer_core_pages(profile, pages, links, strict=True):
    page_map = {p["url"]: p for p in pages}
    aliases = aliases_for(pages, profile)
    candidates = {}
    for link in links:
        position = link.get("position", "").lower()
        if not any(term in position for term in ["nav", "header", "footer"]):
            continue
        u = resolve_alias(link["destination"], aliases)
        if not u or not same_site(u, profile) or is_home(u, profile) or is_blog(u, profile) or excluded(u, profile) or CORE_SKIP.search(urlsplit(u).path) or BINARY_PATH.search(u):
            continue
        p = page_map.get(u)
        if strict and (not p or not p.get("indexable") or p.get("status") != 200 or not p.get("html")):
            continue
        topic = without_brand(p.get("h1") or p.get("title") or link.get("anchor") or urlsplit(u).path.replace("-", " "), profile) if p else without_brand(link.get("anchor") or urlsplit(u).path.replace("-", " "), profile)
        priority = 5 if any(term in position for term in ["nav", "header"]) else 3
        if u not in candidates or candidates[u]["priority"] < priority:
            candidates[u] = {"url": u, "topic": topic, "priority": priority, "detected_from": "Navigation" if priority == 5 else "Footer"}
    if not candidates and pages:
        # Some themes render menus without semantic nav/footer landmarks.
        # Repeated destinations are a fallback, explicitly labeled as inferred.
        repeated = defaultdict(set)
        for link in links:
            repeated[resolve_alias(link["destination"], aliases)].add(link["source"])
        minimum = max(2, math.ceil(len(pages) * .2))
        for u, sources in repeated.items():
            p = page_map.get(u, {})
            if len(sources) >= minimum and p.get("indexable") and p.get("status") == 200 and same_site(u, profile) and not is_home(u, profile) and not is_blog(u, profile) and not excluded(u, profile) and not CORE_SKIP.search(urlsplit(u).path):
                candidates[u] = {"url": u, "topic": without_brand(p.get("h1") or p.get("title") or urlsplit(u).path, profile), "priority": 3, "detected_from": "Repeated site link (inferred)"}
    # Preserve intentionally supplied destinations from earlier versions.
    for core in profile.get("core_pages", []):
        u = resolve_alias(core["url"], aliases)
        p = page_map.get(u)
        if same_site(u, profile) and not is_home(u, profile) and (not strict or (p and p.get("indexable") and p.get("status") == 200)) and not CORE_SKIP.search(urlsplit(u).path):
            candidates.setdefault(u, {**core, "url": u, "detected_from": core.get("detected_from", "Saved priority page")})
    profile["core_pages"] = sorted(candidates.values(), key=lambda c: (-c["priority"], c["url"]))
    return profile["core_pages"]


def built_in_crawl(profile, options, log, check_cancel, homepage=None):
    """Bounded HTML crawl for hosted Streamlit; robots rules are respected."""
    limit = int(options.get("crawl_limit", 2000))
    queue, scheduled = [], set()
    queue_priority, in_flight = {}, set()
    pages, links, content, article_urls = {}, [], {}, set()
    import heapq
    robot_cache, rate_lock, last_request = {}, threading.Lock(), [0.0]
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
            heapq.heappush(queue, (priority, u))

    def robots_for(u):
        origin = urlunsplit((*urlsplit(u)[:2], "", "", ""))
        if origin not in robot_cache:
            parser = RobotFileParser(origin + "/robots.txt")
            try:
                code, _, _, body = get_bytes(origin + "/robots.txt", 1_000_000)
                parser.parse(body.decode("utf-8", errors="replace").splitlines() if code == 200 else ["User-agent: *", "Disallow:" if code in {404, 410} else "Disallow: /"])
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
        except Exception as exc:
            return u, None, str(exc)

    def consume(u, response, error=""):
        check_cancel()
        counters["checked"] += 1
        if error or response is None:
            pages[u] = {"url": u, "status": 0, "html": False, "indexable": False, "indexability_status": error, "title": "", "h1": "", "canonical": "", "redirect": ""}
            counters["failed"] += 1
            return
        status, headers, final, raw = response
        final = url_key(final)
        if not same_site(final, profile):
            counters["failed"] += 1
            return
        if u != final:
            pages[u] = {"url": u, "status": int(headers.get("__redirect_status__") or 0), "html": True, "indexable": False, "indexability_status": "Redirected (chain not recorded)", "title": "", "h1": "", "canonical": "", "redirect": final}
        if status != 200 or "html" not in headers.get("content-type", "").lower():
            if status >= 400:
                counters["failed"] += 1
            pages[final] = {"url": final, "status": status, "html": "html" in headers.get("content-type", ""), "indexable": False, "indexability_status": f"HTTP {status}", "title": "", "h1": "", "canonical": "", "redirect": ""}
            return
        page, edges, body, _ = page_from_html(raw, final, profile, headers)
        pages[final] = page
        canonical = page.get("canonical", "")
        if canonical and canonical != final and same_site(canonical, profile):
            enqueue(canonical, 0)
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
    except Exception as exc:
        log(f"Sitemap discovery unavailable; continuing through site links: {exc}")
    for r in dataset(profile, "sitemaps")["rows"]:
        enqueue(r["url"], 2 if is_blog(r["url"], profile) else 4)
    for r in dataset(profile, "gsc_total_pages")["rows"]:
        enqueue(r["page"], 2 if is_blog(r["page"], profile) else 4)
    with ThreadPoolExecutor(max_workers=3) as executor:
        futures = {}
        while queue or futures:
            check_cancel()
            while queue and len(futures) < 3 and counters["checked"] + len(futures) < limit:
                priority, u = heapq.heappop(queue)
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
                progress_update(log, counters["checked"], min(limit, len(scheduled)), f"Crawled {counters['checked']:,} pages · {len(queue) + len(futures):,} queued · {len(article_urls):,} blog pages found")
    profile["blog_urls"] = sorted(article_urls)
    generation = uuid.uuid4().hex
    remaining = {u for _, u in queue if u not in pages}
    partial = bool(remaining)
    metadata = dict(source="Built-in HTML crawl", generation=generation, partial=partial, crawl_limit=limit,
                    checked=counters["checked"], failed=counters["failed"], remaining=len(remaining), root=profile["root_url"])
    save_dataset(profile, "pages", list(pages.values()), **metadata)
    save_dataset(profile, "links", links, links_verified=True, position_available=True, warnings=[], **metadata)
    save_dataset(profile, "content", list(content.values()), **metadata)
    if partial:
        log(f"Crawl stopped at {limit:,} pages. {len(remaining):,} URLs remain; coverage is marked partial.")
    if not content:
        raise ValueError("The site returned no usable HTML. It may block automated access or require JavaScript. You can use Screaming Frog exports under Connection & crawl options.")
    return counters


def google_service(interactive=False, secret_path="", credentials_info=None, client_config=None):
    """Credentials stay in memory. Workers receive them through a stdin pipe."""
    global GOOGLE_CREDENTIALS_INFO
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from google_auth_oauthlib.flow import InstalledAppFlow
    from googleapiclient.discovery import build
    credentials = None
    info = credentials_info or GOOGLE_CREDENTIALS_INFO
    if info:
        credentials = Credentials.from_authorized_user_info(info, SCOPES)
        if not credentials.valid and credentials.refresh_token:
            credentials.refresh(Request())
    if not credentials or not credentials.valid:
        if not interactive:
            raise ValueError("Connect Google under Connection & crawl options, or configure gsc_token_json in Streamlit Secrets.")
        if not client_config:
            raise ValueError("Provide a Desktop OAuth client configuration for local sign-in.")
        flow = InstalledAppFlow.from_client_config(client_config, SCOPES)
        credentials = flow.run_local_server(host="localhost", port=0, open_browser=True, timeout_seconds=180)
    GOOGLE_CREDENTIALS_INFO = json.loads(credentials.to_json())
    return build("searchconsole", "v1", credentials=credentials, cache_discovery=False)


def execute_google(request_factory, check_cancel=lambda: None):
    for attempt in range(5):
        check_cancel()
        try:
            return request_factory().execute()
        except Exception as exc:
            status = getattr(getattr(exc, "resp", None), "status", None)
            if status not in {429, 500, 502, 503, 504} or attempt == 4:
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
    df = df[df["page"] != ""] if "page" in keys else df
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
    service = service or google_service()
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
    for row in remap("gsc_queries", True):
        if not brand_pattern(profile).search(row["query"]):
            queries[row["page"]].append(row)
    for values in queries.values():
        values.sort(key=lambda r: r.get("impressions", 0), reverse=True)
    return metrics, queries


def stem(token):
    token = token.lower().strip("’'")
    if len(token) > 5 and token.endswith("ies"):
        return token[:-3] + "y"
    if len(token) > 4 and token.endswith("s") and not token.endswith(("ss", "us", "is")):
        return token[:-1]
    return token


def meaningful_tokens(value):
    from sklearn.feature_extraction.text import ENGLISH_STOP_WORDS
    return [stem(m.group()) for m in TOKEN_RE.finditer(value.lower()) if m.group().lower() not in ENGLISH_STOP_WORDS and m.group().lower() not in GENERIC and len(m.group()) > 2]


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


def recommend(profile, options, log, check_cancel):
    if (not profile.get("brands_confirmed") and not options.get("automatic_setup")) or not profile.get("brand_terms"):
        raise ValueError("Review and confirm this client's brand exclusions before generating recommendations.")
    state = graph_state(profile)
    pages, aliases = state["pages"], state["aliases"]
    core = core_mapping(profile, aliases)
    if not core and not options.get("blog_to_blog"):
        raise ValueError("Add approved core pages, or explicitly enable blog-to-blog opportunities.")
    content = {r["url"]: r for r in dataset(profile, "content")["rows"] if r.get("success") and not r.get("noindex")}
    if not content:
        raise ValueError("Fetch page content first. Recommendation analysis never starts a content fetch automatically.")
    metrics, queries = metric_maps(profile, aliases)
    eligible = {u for u, p in pages.items() if p.get("status") == 200 and p.get("html") and p.get("indexable") and not excluded(u, profile)
                and u in content and url_key(content[u].get("final_url", u)) == u
                and (not content[u].get("canonical") or content[u]["canonical"] == u)}
    sources = [u for u in eligible if (is_blog(u, profile) or options.get("all_sources")) and not is_home(u, profile)]
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
                   "destination_nonbrand_position": position, "supporting_query": near_query["query"] if near_query else (qrows[0]["query"] if qrows else ""),
                   "query_impressions": near_query["impressions"] if near_query else (qrows[0]["impressions"] if qrows else None),
                   "query_position": near_query["position"] if near_query else (qrows[0]["position"] if qrows else None),
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


def page_summary(profile, state=None):
    state = state or graph_state(profile)
    metrics, _ = metric_maps(profile, state["aliases"])
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
                     "validation": "Crawled" if p else "Known URL; not validated in crawl"})
    return rows


def audit_links(profile, options, log, check_cancel):
    state = graph_state(profile)
    core = core_mapping(profile, state["aliases"])
    selected = set(options.get("audit_checks", list(AUDITS)))
    rows = []

    def issue(kind, destination, detail, action, severity="Review", source="", anchor="", **extra):
        rows.append({"client": profile["name"], "issue": kind, "priority": severity, "source_url": source,
                     "destination_url": destination, "anchor_text": anchor, "evidence": detail, "recommended_action": action, **extra})

    summary = page_summary(profile, state)
    for row in summary:
        check_cancel()
        u = row["url"]
        if is_home(u, profile) or excluded(u, profile):
            continue
        p = state["pages"].get(u, {})
        if "orphans" in selected and row["unique_inlink_sources"] == 0 and (not p or (p.get("html") and p.get("indexable") and p.get("status") == 200)):
            issue("Potential orphan", u, "No incoming hyperlink sources in this crawl snapshot. " + row["validation"],
                  "Validate the page and crawl coverage; add a relevant contextual or hub link if the page should be discoverable.", "High" if u in core else "Review")
        if u in core and "buried" in selected:
            depth = row["crawl_depth_from_home"]
            if depth is None or depth >= int(options.get("depth_threshold", 4)):
                issue("Core page unreachable from home" if depth is None else "Buried core page", u,
                      f"Shortest followed HTML hyperlink path from configured homepage: {depth if depth is not None else 'not found'}. Imported/sitemap seeds do not count as paths.",
                      "Review navigation and relevant hub pages, then add a shorter useful path.", "High", depth=depth)
        if u in core and "support" in selected and row["unique_contextual_sources"] is not None and row["unique_contextual_sources"] < int(options.get("minimum_contextual_sources", 2)):
            issue("Weak contextual support", u, f"{row['unique_contextual_sources']} unique contextual source pages; {row['unique_inlink_sources']} total source pages.",
                  "Review related blog paragraphs and hub copy for useful contextual links.", "High" if core[u].get("priority", 1) >= 4 else "Medium")
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
            status = p.get("status", 0)
            kind = "Broken destination" if status >= 400 or status == 0 else "Redirected destination" if 300 <= status < 400 else "Non-indexable HTML destination" if p.get("html") and not p.get("indexable") else ""
            if kind:
                issue(kind, d, f"HTTP {status}; {p.get('indexability_status', '')}",
                      "Review the intended destination; update the href to the valid preferred URL when appropriate.",
                      "High" if status >= 400 else "Review", link["source"], anchor,
                      preferred_url=resolve_alias(d, state["aliases"]), link_position=link.get("position", ""))
    # Core URLs absent from every discovery source remain visible for investigation.
    known = {r["url"] for r in summary}
    for u in core:
        if u not in known:
            issue("Approved core page absent from inventory", u, "The approved URL is absent from crawl, sitemap and available GSC page inventory.",
                  "Check the URL, crawl scope, redirects and sitemap inclusion before recommending links.", "High")
    warnings = list(dataset(profile, "links")["meta"].get("warnings", []))
    if state["home"] not in state["pages"]:
        warnings.append("The configured homepage was not found as a crawled page. Reachability findings need crawl-scope review.")
    if not dataset(profile, "sitemaps")["meta"]:
        warnings.append("Sitemap discovery has not been run. Orphan coverage is limited to the available crawl/GSC inventory.")
    save_dataset(profile, "audit", rows, input_signature=input_signature(profile, AUDIT_INPUTS), settings=options, warnings=warnings,
                 coverage="Findings describe this configured crawl and known URL inventory, not proof of a complete website crawl.")
    save_dataset(profile, "page_summary", summary, input_signature=input_signature(profile, AUDIT_INPUTS))
    log(f"Saved {len(rows):,} audit findings and {len(summary):,} page summaries.")


def infer_topics(summary, profile):
    from sklearn.feature_extraction.text import TfidfVectorizer
    topics = [c for c in profile.get("core_pages", []) if c.get("topic")]
    if not topics or not summary:
        return {r["url"]: r.get("topic") or (urlsplit(r["url"]).path.strip("/").split("/")[0] or "Home") for r in summary}
    docs = [c["topic"] for c in topics]
    page_docs = [" ".join([r.get("title", ""), r.get("h1", ""), urlsplit(r["url"]).path.replace("-", " ").replace("/", " ")]) for r in summary]
    try:
        matrix = TfidfVectorizer(stop_words="english", ngram_range=(1, 2)).fit_transform(docs + page_docs)
        sims = (matrix[len(topics):] @ matrix[:len(topics)].T).toarray()
        return {r["url"]: r.get("topic") or (topics[int(np.argmax(sims[i]))]["topic"] if float(np.max(sims[i])) >= .12 else "Unassigned") for i, r in enumerate(summary)}
    except ValueError:
        return {r["url"]: r.get("topic") or "Unassigned" for r in summary}


def make_visual(profile, options):
    import networkx as nx
    import plotly.graph_objects as go
    import plotly.express as px
    state = graph_state(profile)
    summary = page_summary(profile, state)
    topics = infer_topics(summary, profile)
    df = pd.DataFrame(summary)
    df["inferred_topic"] = df["url"].map(topics)
    kind = options.get("visual_type", "Opportunity chart")
    topic_filter = options.get("topic", "")
    if topic_filter:
        df = df[df["inferred_topic"].str.contains(topic_filter, case=False, regex=False)]
    if options.get("core_only"):
        df = df[df["page_type"] == "Core"]
    if kind == "Opportunity chart":
        df = df[df["gsc_data_available"] & df["unique_contextual_sources"].notna()]
        if df.empty:
            raise ValueError("This selection has no non-brand page metrics or contextual counts. Download GSC data and include Link Position in the crawl export.")
        df["display_priority"] = df["business_priority"].clip(lower=1)
        figure = px.scatter(df, x="unique_contextual_sources", y="nonbrand_impressions", size="display_priority", color="nonbrand_position",
                            color_continuous_scale="Viridis_r", hover_name="url", hover_data=["page_type", "inferred_topic", "crawl_depth_from_home"],
                            labels={"unique_contextual_sources": "Unique contextual source pages", "nonbrand_impressions": "Non-brand impressions (saved period)", "nonbrand_position": "Average position"})
        figure.update_layout(height=650)
        return figure, frame_rows(df), "Bubble size = business priority. Colors = page-level average position. Missing GSC data is excluded, not treated as zero."
    cap = int(options.get("node_cap", 150))
    focus = options.get("focus_url", "")
    recs = dataset(profile, "recommendations")["rows"] if options.get("show_proposed") else []
    if focus and focus in state["graph"]:
        neighbors = {focus, *state["graph"].predecessors(focus), *state["graph"].successors(focus)}
        neighbors.update(r["source_url"] for r in recs if r["destination_url"] == focus)
        neighbors.update(r["destination_url"] for r in recs if r["source_url"] == focus)
        df = df[df["url"].isin(neighbors)]
    df = df.sort_values(["business_priority", "nonbrand_impressions"], ascending=False, na_position="last").head(cap)
    nodes = set(df["url"])
    if not nodes:
        raise ValueError("No pages match these visualization filters.")
    graph = (state["content_graph"] if options.get("content_only") and kind != "Crawl tree" else state["graph"]).subgraph(nodes).copy()
    graph.add_nodes_from(nodes)
    note = f"Showing {len(nodes):,} selected pages. Topic labels outside approved core pages are inferred."
    if kind == "Crawl tree":
        # Use the full site's shortest paths, then display selected nodes. Never
        # turn sitemap-discovered URLs into direct children of the homepage.
        parent = {v: u for u, v in nx.bfs_edges(state["graph"], state["home"])} if state["home"] in state["graph"] else {}
        tree = nx.DiGraph()
        tree.add_nodes_from(nodes)
        tree.add_edges_from((p, u) for u, p in parent.items() if u in nodes and p in nodes)
        graph = tree
        levels = defaultdict(list)
        orphan_level = max(state["depths"].values(), default=0) + 2
        for u in sorted(nodes):
            levels[state["depths"].get(u, orphan_level)].append(u)
        positions = {u: (i - (len(group) - 1) / 2, -level) for level, group in levels.items() for i, u in enumerate(group)}
        note += " Tree edges show one homepage discovery path; filters may hide intermediate nodes. This is not the complete link graph."
    else:
        positions = nx.spring_layout(graph, seed=42, iterations=70)
    figure = go.Figure()

    def add_edges(edges, color, dash, label):
        x, y = [], []
        for s, d in list(edges)[:1800]:
            if s in positions and d in positions:
                x.extend([float(positions[s][0]), float(positions[d][0]), None])
                y.extend([float(positions[s][1]), float(positions[d][1]), None])
        figure.add_trace(go.Scatter(x=x, y=y, mode="lines", line=dict(color=color, width=1, dash=dash), hoverinfo="skip", name=label))
    add_edges(graph.edges(), "#cbd5e1", "solid", "Existing links")
    proposed = [(r["source_url"], r["destination_url"]) for r in recs if r.get("status") not in {"Dismissed", "Implemented"}]
    if proposed:
        add_edges(proposed, "#16a34a", "dash", "Proposed links")
    palette = px.colors.qualitative.Safe
    topic_colors = {t: palette[i % len(palette)] for i, t in enumerate(sorted(set(topics.values())))}
    record_map = {r["url"]: r for r in summary}
    for topic in sorted({topics[u] for u in nodes}):
        group = sorted(u for u in nodes if topics[u] == topic)
        figure.add_trace(go.Scatter(
            x=[float(positions[u][0]) for u in group], y=[float(positions[u][1]) for u in group], mode="markers",
            marker=dict(size=[12 + min(22, 3 * math.log1p(record_map[u].get("nonbrand_impressions") or 0)) for u in group], color=topic_colors[topic],
                        symbol=["diamond" if record_map[u]["page_type"] == "Core" else "circle" for u in group],
                        line=dict(color=["#dc2626" if record_map[u]["unique_inlink_sources"] == 0 and u != state["home"] else "#ffffff" for u in group], width=2)),
            text=[f"{u}<br>Topic: {topics[u]}<br>Impressions: {record_map[u]['nonbrand_impressions'] if record_map[u]['gsc_data_available'] else 'No data'}<br>Position: {record_map[u]['nonbrand_position']}<br>Depth: {record_map[u]['crawl_depth_from_home']}" for u in group],
            hoverinfo="text", name=topic))
    figure.update_layout(height=720, xaxis=dict(visible=False), yaxis=dict(visible=False), plot_bgcolor="#f8fafc", margin=dict(l=10, r=10, t=10, b=10), legend=dict(orientation="h"))
    return figure, frame_rows(df), note + " Core pages are diamonds; red outlines indicate no discovered incoming sources. Edges are displayed without arrowheads; direction is in the link table."


def safe_excel(value):
    if isinstance(value, (list, dict)):
        value = json.dumps(value, ensure_ascii=False)
    if isinstance(value, str):
        value = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", value)[:32760]
        if value.lstrip().startswith(("=", "+", "-", "@")):
            value = "'" + value
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
                for stage in ["pages", "links", "sitemaps", "gsc_pages", "gsc_queries", "content", "recommendations", "audit"]:
                    doc = dataset(profile, stage)
                    if not doc["meta"]:
                        continue
                    stale = stage == "recommendations" and doc["meta"].get("input_signature") != input_signature(profile, REC_INPUTS)
                    stale = stale or (stage == "audit" and doc["meta"].get("input_signature") != input_signature(profile, AUDIT_INPUTS))
                    collected[name].append({"client": profile["name"], "dataset": stage, "rows": len(doc["rows"]), "stale": stale,
                                             "created_at": doc["meta"].get("created_at"), "metadata": doc["meta"]})
                continue
            key = {"Recommendations": "recommendations", "Existing-link issues": "audit", "Page summary": "page_summary", "GSC pages": "gsc_pages", "GSC queries": "gsc_queries", "Content diagnostics": "content", "Existing links": "links"}[name]
            doc = dataset(profile, key)
            values = doc["rows"]
            reviews = read_json(client_dir(profile) / "reviews.json", {}) if key == "recommendations" else {}
            stale = None
            if key in {"recommendations", "audit", "page_summary"}:
                inputs = REC_INPUTS if key == "recommendations" else AUDIT_INPUTS
                stale = doc["meta"].get("input_signature") != input_signature(profile, inputs)
            for raw in values:
                row = dict(raw)
                row["client"] = profile["name"]
                if key in {"recommendations", "audit", "page_summary"}:
                    row["analysis_stale"] = stale
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
                for row in ws.iter_rows(min_row=2):
                    for cell in row:
                        if isinstance(cell.value, str):
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
    for _ in range(3):
        try:
            fd = os.open(str(lock), os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump({"job_id": job_id, "created_at": utc_now()}, handle)
            return
        except FileExistsError:
            try:
                previous = read_json(lock, {})
            except json.JSONDecodeError:
                previous = {}
            prior_folder = folder / previous.get("job_id", "unknown")
            status = read_json(prior_folder / "status.json", {})
            process = read_json(prior_folder / "process.json", {})
            age = time.time() - lock.stat().st_mtime
            stopped = process and not process_alive(process)
            finished = status.get("state") in {"completed", "completed_with_errors", "cancelled", "failed"}
            if finished or stopped or (not process and age > 30):
                if status and not finished:
                    status.update(state="failed", message="Previous worker stopped unexpectedly.", finished_at=utc_now())
                    atomic_json(prior_folder / "status.json", status)
                lock.unlink(missing_ok=True)
                continue
            raise ValueError("A job is already active. Finish or cancel it before starting another batch.")
    raise ValueError("Could not acquire the local job queue. Refresh and retry.")


def release_job_lock(job_id):
    lock = DATA_DIR / "jobs" / "queue.lock"
    if read_json(lock, {}).get("job_id") == job_id:
        lock.unlink(missing_ok=True)


def create_job(profiles, stages, options, credentials_info=None, workflow="legacy"):
    import psutil
    DATA_DIR.mkdir(parents=True, exist_ok=True)
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
    global DATA_DIR, GOOGLE_CREDENTIALS_INFO
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


def install_demo():
    """Deterministic synthetic data; no live clients, credentials or requests."""
    p = default_profile("Demo — synthetic data", "https://demo.example/")
    p.update(id="demo", demo=True, brand_terms=["DemoCo", "DemoCapture"], brands_confirmed=True,
             blog_pattern=r"/blog/", core_pages=[
                 {"url": "https://demo.example/solutions/invoice-data-capture/", "topic": "Invoice data capture software", "priority": 5},
                 {"url": "https://demo.example/solutions/document-scanning/", "topic": "Document scanning services", "priority": 4}])
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
    save_dataset(p, "pages", pages, generation=gen, source="Synthetic demo")
    save_dataset(p, "links", links, generation=gen, links_verified=True, position_available=True, source="Synthetic demo")
    save_dataset(p, "content", content, source="Synthetic demo", failed=0, partial=False)
    save_dataset(p, "sitemaps", [{"url": root + "unlinked-resource/"}], source="Synthetic demo")
    metrics = [{"page": core1, "impressions": 14000, "clicks": 120, "position": 11.4, "ctr": 120 / 14000},
               {"page": core2, "impressions": 8200, "clicks": 100, "position": 8.2, "ctr": 100 / 8200}]
    meta = dict(source="Synthetic demo", start_date="2026-08-01", end_date="2026-10-29", brand_method="Synthetic NON_BRANDED", metric_basis="Synthetic data; not live GSC")
    save_dataset(p, "gsc_pages", metrics, **meta)
    save_dataset(p, "gsc_total_pages", metrics, **meta)
    save_dataset(p, "gsc_queries", [{**m, "query": "invoice data capture software" if m["page"] == core1 else "document scanning services"} for m in metrics], **meta)
    profiles = read_json(DATA_DIR / "profiles.json", [])
    profiles = [r for r in profiles if r["id"] != p["id"]] + [p]
    atomic_json(DATA_DIR / "profiles.json", profiles)
    return p


def recent_dataset(profile, name, hours=24):
    doc = dataset(profile, name)
    try:
        stamp = datetime.fromisoformat(doc["meta"]["created_at"])
        return bool(doc["rows"]) and (datetime.now(timezone.utc) - stamp).total_seconds() < hours * 3600
    except (KeyError, ValueError):
        return False


def save_working_profile(profile):
    current = read_json(DATA_DIR / "profiles.json", [])
    found = False
    for i, row in enumerate(current):
        if row["id"] == profile["id"]:
            current[i] = profile
            found = True
            break
    if not found:
        current.append(profile)
    atomic_json(DATA_DIR / "profiles.json", current)


def safe_error(exc):
    if type(exc).__name__ in {"RefreshError", "OAuthError", "TokenExpiredError"}:
        return "Google authorization expired or was revoked. Reconnect Google in Connection & crawl options."
    status = getattr(getattr(exc, "resp", None), "status", None)
    if status:
        return f"Google returned HTTP {status}. Check account access, API enablement or quota, then reconnect if needed."
    value = str(exc)
    value = re.sub(r'(?i)(access_token|refresh_token|client_secret|authorization)([\s\"\':=]+)[^\s,}\"]+', r'\1\2[redacted]', value)
    return value[:1000]


def simple_pipeline(job, status, log, check_cancel, folder):
    """The one-click workflow; no credentials are written to any dataset."""
    profile = dict(job["profiles"][0])
    options = dict(job["options"])
    options.update(automatic_setup=True, all_sources=False, blog_to_blog=False,
                   audit_checks=list(AUDITS), recommendation_cap=300,
                   links_per_target=30 if options.get("anchor_text") else 5,
                   paragraphs_per_target=500 if options.get("anchor_text") else 120,
                   content_cap=options.get("crawl_limit", 2000))
    phases = ["Discover pages & navigation", "Crawl blogs & core pages", "Load search performance", "Find contextual links", "Analyze internal links", "Prepare charts & workbook"]
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
    old_pages, old_links = dataset(profile, "pages"), dataset(profile, "links")
    cached = (profile.get("demo") or (not options.get("refresh_crawl") and recent_dataset(profile, "pages") and old_links["meta"].get("links_verified") and old_pages["meta"].get("generation") == old_links["meta"].get("generation")))
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
            automatic_brand_terms(profile, names)
            infer_core_pages(profile, [page], edges, strict=False)
            progress(1, 1, f"Detected {len(profile['core_pages'])} candidate core pages from navigation and footer.")
        except Exception as exc:
            if options.get("runtime_mode") != "local":
                raise ValueError(f"Could not read the website: {safe_error(exc)}") from exc
            warnings.append("Homepage HTML could not be read; using the local Screaming Frog crawl to identify navigation links.")
    if not profile.get("demo") and GOOGLE_CREDENTIALS_INFO and profile.get("gsc_property") and not recent_dataset(profile, "gsc_total_pages"):
        try:
            log("Loading known landing pages from Search Console for crawl discovery.")
            end = datetime.now(ZoneInfo("America/Los_Angeles")).date() - timedelta(days=3)
            start = end - timedelta(days=89)
            rows, capped = gsc_rows(google_service(), profile["gsc_property"], start, end, ["page"], [], check_cancel)
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
    pages = dataset(profile, "pages")["rows"]
    infer_core_pages(profile, pages, dataset(profile, "links")["rows"])
    detect_proprietary_product_brands(profile, dataset(profile, "content")["rows"])
    if not profile.get("core_pages"):
        raise ValueError("No eligible core pages were found in the navigation/footer. A JavaScript-rendered menu may need a local Screaming Frog crawl or imported exports.")
    save_working_profile(profile)
    status["core_pages"] = len(profile["core_pages"])
    indexable_urls = {p["url"] for p in pages if p.get("indexable")}
    status["blogs"] = sum(is_blog(c["url"], profile) for c in dataset(profile, "content")["rows"] if c.get("success") and c["url"] in indexable_urls)
    phase(2)
    if profile.get("demo"):
        progress(1, 1, "Using synthetic demo metrics.")
    elif GOOGLE_CREDENTIALS_INFO and profile.get("gsc_property"):
        gsc_meta = dataset(profile, "gsc_pages")["meta"]
        if recent_dataset(profile, "gsc_pages") and not options.get("refresh_crawl") and gsc_meta.get("brand_rules_hash") == digest(profile.get("brand_terms", [])):
            progress(1, 1, "Using saved Search Console metrics.")
        else:
            try:
                end = datetime.now(ZoneInfo("America/Los_Angeles")).date() - timedelta(days=3)
                download_gsc(profile, {**options, "start_date": str(end - timedelta(days=89)), "end_date": str(end), "brand_mode": "auto"}, log, check_cancel)
            except Cancelled:
                raise
            except Exception as exc:
                warnings.append("Search Console unavailable for this run: " + safe_error(exc) + " Content matching will continue.")
    else:
        progress(1, 1, "Search Console is optional; matching will use page content and existing links.")
        if not dataset(profile, "gsc_pages")["rows"]:
            warnings.append("No GSC metrics are connected. Opportunities use content relevance and internal links; impressions/positions are left blank.")
    phase(3)
    recommend(profile, options, log, check_cancel)
    phase(4)
    audit_links(profile, options, log, check_cancel)
    phase(5)
    visual_rows = []
    kinds = ["Opportunity chart", "Topic graph", "Crawl tree"]
    for i, kind in enumerate(kinds, 1):
        check_cancel()
        try:
            figure, rows, note = make_visual(profile, {"visual_type": kind, "show_proposed": True, "node_cap": 120})
            visual_rows.append({"kind": kind, "figure_json": figure.to_json(), "note": note})
        except ValueError as exc:
            if kind != "Opportunity chart":
                warnings.append(safe_error(exc))
        progress(i, 4, f"Prepared {kind.lower()}.")
    save_dataset(profile, "visuals", visual_rows)
    workbook = workbook_bytes([profile], ["Recommendations", "Existing-link issues", "Page summary", "Run summary"])
    output = client_dir(profile) / "exports" / f"internal_links_{job['id']}.xlsx"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(workbook)
    for name in ["pages", "recommendations"]:
        if dataset(profile, name)["meta"].get("partial"):
            warnings.append("This run covers a limited selection of pages. Coverage and limits are included in the workbook.")
    failures = dataset(profile, "pages")["meta"].get("failed", 0)
    if failures:
        warnings.append(f"{failures} page requests failed or were blocked. Results cover pages that could be read.")
    save_dataset(profile, "result", [], workbook=str(output), warnings=list(dict.fromkeys(warnings)), job_id=job["id"],
                 core_pages=status["core_pages"], blogs=status["blogs"], anchor_text=options.get("anchor_text", ""),
                 opportunities=len(dataset(profile, "recommendations")["rows"]), crawl_source=dataset(profile, "pages")["meta"].get("source"))
    status.update(state="completed", overall_progress=1, phase_progress=1, done=4, total=4, warnings=list(dict.fromkeys(warnings)),
                  finished_at=utc_now(), message="Opportunities, analysis, charts and workbook are ready.")
    publish()


def parse_core_lines(value):
    rows = []
    for line in value.splitlines():
        if not line.strip():
            continue
        parts = [x.strip() for x in line.split("|")]
        url = url_key(parts[0])
        if not url:
            raise ValueError(f"Invalid core page URL: {parts[0]}")
        topic = parts[1] if len(parts) > 1 else urlsplit(url).path.strip("/").replace("-", " ")
        priority = int(parts[2]) if len(parts) > 2 and parts[2] else 3
        if not 1 <= priority <= 5:
            raise ValueError("Business priorities must be between 1 and 5.")
        rows.append({"url": url, "topic": topic, "priority": priority})
    return list({row["url"]: row for row in rows}.values())


def show_saved_warnings(st, doc):
    for warning in doc.get("meta", {}).get("warnings", []):
        st.warning(warning)
    if doc.get("meta", {}).get("partial"):
        st.warning("This saved result covers a capped/partial selection. See Run summary for its scope.")


def register_google_properties(properties):
    """One preferred property per host; retain existing client identities."""
    profiles = read_json(DATA_DIR / "profiles.json", [])
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
    atomic_json(DATA_DIR / "profiles.json", profiles)
    atomic_json(DATA_DIR / "properties.json", properties)
    return profiles


def secret_value(st, name, default=""):
    try:
        return st.secrets.get(name, default)
    except FileNotFoundError:
        return default


def validate_token_info(value):
    if not isinstance(value, dict) or not all(value.get(k) for k in ["refresh_token", "client_id", "client_secret"]):
        raise ValueError("Choose the authorized token JSON created after Google sign-in. It must contain refresh_token, client_id and client_secret.")
    scopes = value.get("scopes", [])
    if isinstance(scopes, str):
        scopes = scopes.split()
    if scopes and not set(scopes).issubset(set(SCOPES)):
        raise ValueError("Use a token authorized only for Google Search Console read-only access.")
    return value


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


def connect_properties(info=None, client_config=None):
    service = google_service(credentials_info=info, interactive=bool(client_config), client_config=client_config)
    properties = execute_google(lambda: service.sites().list()).get("siteEntry", [])
    register_google_properties(properties)
    return dict(GOOGLE_CREDENTIALS_INFO), properties


def render_simple_results(st, profile):
    result = dataset(profile, "result")["meta"]
    if not result:
        st.caption("Select a client and click Find opportunities. Core pages, analysis, charts and workbook are prepared automatically.")
        return
    cols = st.columns(3)
    for column, label, key in zip(cols, ["Blog pages checked", "Core pages detected", "Link opportunities"], ["blogs", "core_pages", "opportunities"]):
        column.metric(label, result.get(key, 0))
    workbook = Path(result.get("workbook", ""))
    if workbook.is_file():
        st.download_button("Download workbook", workbook.read_bytes(), file_name=workbook.name,
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", on_click="ignore", type="primary")
    st.caption(f"Last completed: {result.get('created_at', '')} · {result.get('crawl_source', '')}")
    with st.expander("Core pages detected"):
        st.dataframe(pd.DataFrame([{"URL": c["url"], "Topic": c.get("topic", ""), "Found in": c.get("detected_from", "Saved priority page")} for c in profile.get("core_pages", [])]), hide_index=True, width="stretch")
    if result.get("warnings"):
        with st.expander("Run notes / coverage"):
            for warning in result["warnings"]:
                st.write(warning)
    tabs = st.tabs(["Opportunities", "Analysis", "Site map"])
    recs = dataset(profile, "recommendations")["rows"]
    with tabs[0]:
        if recs:
            df = pd.DataFrame(recs).rename(columns={"source_url": "Source page", "destination_url": "Destination page", "anchor_text": "Anchor text", "context": "Existing paragraph", "priority": "Priority"})
            st.dataframe(df[["Source page", "Destination page", "Anchor text", "Existing paragraph", "Priority"]], hide_index=True, width="stretch",
                         column_config={"Source page": st.column_config.LinkColumn(), "Destination page": st.column_config.LinkColumn(), "Existing paragraph": st.column_config.TextColumn(width="large")})
        else:
            st.info("No suitable unlinked phrases passed the relevance checks. Try another anchor, or review crawl coverage in Run notes.")
    visuals = {r["kind"]: r for r in dataset(profile, "visuals")["rows"]}
    import plotly.io as pio
    with tabs[1]:
        if "Opportunity chart" in visuals:
            visual = visuals["Opportunity chart"]
            st.plotly_chart(pio.from_json(visual["figure_json"]), width="stretch")
            st.caption(visual["note"])
        issues = pd.DataFrame(dataset(profile, "audit")["rows"])
        if not issues.empty:
            st.dataframe(issues[["issue", "destination_url", "evidence", "recommended_action"]], hide_index=True, width="stretch")
        else:
            st.caption("No internal-link issues were found in the available crawl snapshot.")
    with tabs[2]:
        choices = [k for k in ["Topic graph", "Crawl tree"] if k in visuals]
        if choices:
            view = st.radio("Map view", choices, horizontal=True, key="map_" + profile["id"])
            st.plotly_chart(pio.from_json(visuals[view]["figure_json"]), width="stretch")
            st.caption(visuals[view]["note"])


def render_live_progress(st, job_id):
    @st.fragment(run_every="1s")
    def monitor():
        folder = DATA_DIR / "jobs" / job_id
        status = read_json(folder / "status.json", {})
        state = status.get("state", "queued")
        step = f"Step {status.get('phase_index', 0) + 1}/{status.get('phase_count', 6)}"
        st.progress(float(max(0, min(1, status.get("overall_progress", 0)))), text=f"{step} · {status.get('stage', 'Starting…')} · {status.get('message', '')}")
        if state in {"queued", "running"}:
            if status.get("total"):
                st.caption(f"{status.get('done', 0):,} of {status['total']:,} items in the current stage. Crawl totals may grow as new pages are discovered.")
            if st.button("Stop", key="stop_" + job_id):
                (folder / "cancel").touch()
                st.info("Stopping after active requests finish…")
        elif state == "completed":
            st.success("Opportunities, analysis, charts and workbook are ready.")
        elif state == "cancelled":
            st.info("Stopped. Previously completed results remain available.")
        elif state in {"failed", "completed_with_errors"}:
            errors = status.get("errors", [])
            st.error(errors[-1].get("error", "The run could not finish.") if errors else "The run could not finish.")
        if state in {"completed", "cancelled", "failed", "completed_with_errors"} and st.session_state.get("finished_job") != job_id:
            st.session_state["finished_job"] = job_id
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
    settings = read_json(DATA_DIR / "settings.json", {})
    password = str(secret_value(st, "app_password"))
    secret_token = secret_value(st, "gsc_token_json")
    profiles = read_json(DATA_DIR / "profiles.json", [])
    legacy_token = DATA_DIR / "auth" / "gsc_token.json"
    has_private_data = any(not p.get("demo") and (client_dir(p) / "gsc_pages.json").exists() for p in profiles)
    if settings.get("runtime_mode", "hosted") != "local" and not password and (secret_token or legacy_token.exists() or has_private_data):
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
    # Migrate the v1 generated token into authenticated session memory, then remove
    # that plaintext copy. Credentials are never written back to the filesystem.
    if legacy_token.is_file():
        try:
            st.session_state.setdefault("gsc_credentials", validate_token_info(read_json(legacy_token)))
            legacy_token.unlink()
        except (ValueError, OSError):
            pass
    info = st.session_state.get("gsc_credentials")
    if not info and secret_token:
        try:
            info = validate_token_info(json.loads(secret_token) if isinstance(secret_token, str) else dict(secret_token))
            st.session_state["gsc_credentials"] = info
        except ValueError:
            info = None
    if info and not profiles and not st.session_state.get("auto_connection_attempted"):
        st.session_state["auto_connection_attempted"] = True
        try:
            with st.spinner("Loading your clients from Search Console…"):
                info, _ = connect_properties(info)
                st.session_state["gsc_credentials"] = info
                profiles = read_json(DATA_DIR / "profiles.json", [])
        except Exception as exc:
            st.warning(safe_error(exc))
    st.sidebar.caption("One-time connection and optional crawl controls")
    with st.sidebar.expander("Connection & crawl options", expanded=False):
        runtime = st.selectbox("Run on", ["hosted", "local"], index=0 if settings.get("runtime_mode", "hosted") != "local" else 1,
                               format_func=lambda x: "Streamlit Cloud — automatic web crawl" if x == "hosted" else "This computer — Screaming Frog when available")
        settings["runtime_mode"] = runtime
        settings["refresh_crawl"] = st.checkbox("Refresh saved crawl and GSC data", value=False)
        settings["crawl_limit"] = int(st.number_input("Maximum pages per crawl", 100, 20000, int(settings.get("crawl_limit", 2000)), 100))
        if runtime == "local":
            settings["sf_path"] = st.text_input("Screaming Frog CLI path (optional)", settings.get("sf_path", ""))
        token_upload = st.file_uploader("Google authorized token JSON", type="json", help="Stored in session memory. For persistence, use gsc_token_json in Streamlit Secrets.")
        if st.button("Connect Google / refresh clients"):
            try:
                if runtime == "hosted" and not password:
                    raise ValueError("Set app_password in Streamlit Secrets before connecting Google.")
                value = json.loads(token_upload.getvalue()) if token_upload else info
                if not value:
                    raise ValueError("Upload your authorized GSC token JSON or configure gsc_token_json in Streamlit Secrets.")
                local_config = value if runtime == "local" and "installed" in value else None
                token = None if local_config else validate_token_info(value)
                with st.spinner("Connecting…"):
                    connected, _ = connect_properties(token, local_config)
                st.session_state["gsc_credentials"] = connected
                atomic_json(DATA_DIR / "settings.json", settings)
                st.rerun()
            except Exception as exc:
                st.error(safe_error(exc))
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
                current_id = st.session_state.get("selected_client", profiles[0]["id"])
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
    st.title("Internal linking opportunities")
    st.caption("Blog pages → relevant core pages. Core pages are detected from navigation and footer links.")
    if not profiles:
        st.info("Connect Google once under Connection & crawl options to load your clients, or add a website there. You can also try the demo.")
        return
    ids = [p["id"] for p in profiles]
    if st.session_state.get("selected_client") not in ids:
        st.session_state["selected_client"] = ids[0]
    selected = st.selectbox("Client", ids, key="selected_client", format_func=lambda x: next(p["name"] for p in profiles if p["id"] == x))
    profile = next(p for p in profiles if p["id"] == selected)
    if profile.get("demo"):
        st.info("Demo: all pages and metrics are synthetic. No external crawl or Google request will run.")
    anchor = st.text_input("Anchor text (optional)", placeholder="Leave blank for automatic suggestions, or enter e.g. options data API")
    destination = ""
    if anchor and profile.get("core_pages"):
        with st.expander("Choose a destination for this anchor (optional)"):
            choices = [""] + [c["url"] for c in profile["core_pages"]]
            destination = st.selectbox("Link to", choices, format_func=lambda x: x or "Automatically choose a relevant core page")
    active = read_json(DATA_DIR / "jobs" / "queue.lock", {}).get("job_id")
    if active:
        folder = DATA_DIR / "jobs" / active
        active_status = read_json(folder / "status.json", {})
        record = read_json(folder / "process.json", {})
        if active_status.get("state") in {"completed", "failed", "cancelled", "completed_with_errors"} or (record and not process_alive(record)):
            if active_status.get("state") in {"queued", "running"}:
                active_status.update(state="failed", errors=[{"error": "The worker stopped unexpectedly. You can start the run again."}])
                atomic_json(folder / "status.json", active_status)
            release_job_lock(active)
            active = None
    if st.button("Find opportunities", type="primary", disabled=bool(active)):
        try:
            options = {**settings, "anchor_text": anchor.strip(), "destination_url": destination}
            atomic_json(DATA_DIR / "settings.json", settings)
            job_id = create_job([profile], [], options, credentials_info=st.session_state.get("gsc_credentials"), workflow="simple")
            st.session_state["active_job"] = job_id
            st.rerun()
        except Exception as exc:
            st.error(safe_error(exc))
    job_id = active or st.session_state.get("active_job")
    if job_id:
        render_live_progress(st, job_id)
    render_simple_results(st, profile)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--worker", type=Path)
    args, _ = parser.parse_known_args()
    if args.worker:
        worker_main(args.worker)
    else:
        main()
