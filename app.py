"""Cadence internal linking workbench. Run: python -m streamlit run app.py

GITHUB / STREAMLIT CLOUD: Put app.py and requirements.txt at repository root;
select app.py as the entrypoint. Try Demo & help before connecting real data.
Cloud mode imports Screaming Frog CSV exports; it cannot launch a desktop app.
Optional Streamlit Secrets:
    app_password = "choose-a-private-password"
    gsc_token_json = '''{contents of an already-authorized GSC token JSON}'''
Keep OAuth credentials out of GitHub. Connect Google under Clients & settings.

Every network call, crawl, analysis and export is gated by an explicit action.
The same file is a detached worker: python app.py --worker /path/to/job.json.
Credentials and results stay in the configured local data directory.
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import hmac
import io
import json
import math
import os
import platform
import re
import shutil
import subprocess
import sys
import threading
import time
import unicodedata
import uuid
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit
from urllib.robotparser import RobotFileParser
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("INTERNAL_LINK_DATA_DIR", str(APP_DIR / "data"))).expanduser().resolve()
APP_VERSION = "1.0.0"
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
    return bool(re.search(profile.get("blog_pattern", r"/(blog|resources|articles|insights)/"), urlsplit(url).path, re.I))


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
    raise FileNotFoundError("Screaming Frog CLI was not found. Set its executable path in Clients & settings.")


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
            while process.poll() is None:
                check_cancel()
                if time.monotonic() - started > int(options.get("crawl_timeout_minutes", 180)) * 60:
                    raise TimeoutError("Crawl exceeded the configured timeout. See the crawl log.")
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


def get_bytes(url, max_bytes=5_000_000):
    import requests
    with requests.get(url, headers={"User-Agent": UA}, timeout=(10, 35), allow_redirects=True, stream=True) as response:
        data = bytearray()
        for part in response.iter_content(65536):
            data.extend(part)
            if len(data) > max_bytes:
                raise ValueError(f"Response exceeded the {max_bytes:,}-byte limit.")
        return response.status_code, {k.lower(): v for k, v in response.headers.items()}, response.url, bytes(data)


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
    for node in list(main.select("script, style, noscript, svg, nav, footer, header, aside, form, button, [hidden], [aria-hidden='true'], .related-posts, .related-articles, .breadcrumbs, .social-share")):
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
    with ThreadPoolExecutor(max_workers=int(options.get("fetch_workers", 3))) as executor:
        futures = {executor.submit(fetch_one, u): u for u in pending}
        for i, future in enumerate(as_completed(futures), 1):
            check_cancel()
            row = future.result()
            output[row["url"]] = row
            if i % 20 == 0:
                log(f"Fetched {i:,}/{len(pending):,} pages; reused {len(selected) - len(pending):,} cached pages.")
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
        if not u or u in seen or not same_site(u, profile):
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


def google_service(interactive=False, secret_path=""):
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from google_auth_oauthlib.flow import InstalledAppFlow
    from googleapiclient.discovery import build
    token_path = DATA_DIR / "auth" / "gsc_token.json"
    credentials = None
    if token_path.exists():
        credentials = Credentials.from_authorized_user_file(str(token_path), SCOPES)
        if not credentials.valid and credentials.refresh_token:
            credentials.refresh(Request())
    if not credentials or not credentials.valid:
        if not interactive:
            raise ValueError("Connect Google in Clients & settings first. In hosted mode, use an authorized GSC token JSON or Streamlit Secrets.")
        secret = Path(secret_path).expanduser() if secret_path else DATA_DIR / "auth" / "oauth_client.json"
        if not secret.is_file():
            raise FileNotFoundError("Choose a Google OAuth Desktop app client JSON file first.")
        flow = InstalledAppFlow.from_client_secrets_file(str(secret), SCOPES)
        credentials = flow.run_local_server(host="localhost", port=0, open_browser=True, timeout_seconds=180)
    atomic_json(token_path, json.loads(credentials.to_json()), private=True)
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
        log(f"GSC {cursor} to {chunk_end}: {len(chunk):,} query/page rows.")
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
            words = [m.group().lower() for m in TOKEN_RE.finditer(anchor)]
            terms = meaningful_tokens(anchor)
            if not 2 <= len(words) <= 8 or len(anchor) > 100 or not terms or words[0] in BAD_EDGE or words[-1] in BAD_EDGE:
                continue
            if pattern.search(anchor) or text_norm(anchor).lower() in GENERIC_ANCHORS:
                continue
            overlap = set(terms) & set(weights)
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
    vectorizer = TfidfVectorizer(stop_words="english", ngram_range=(1, 2), sublinear_tf=True, max_features=50000, dtype=np.float32)
    matrix = vectorizer.fit_transform(documents + paragraphs)
    return matrix[:len(documents)], matrix[len(documents):], "lexical"


REC_INPUTS = ["pages", "links", "content", "gsc_pages", "gsc_queries"]
AUDIT_INPUTS = ["pages", "links", "sitemaps", "gsc_pages", "gsc_total_pages"]


def recommend(profile, options, log, check_cancel):
    if not profile.get("brands_confirmed") or not profile.get("brand_terms"):
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
        doc = " ".join([dest["topic"]] * 3 + [dest["title"], dest["h1"]] * 2 + [" ".join(q["query"] for q in queries.get(u, [])[:20]), " ".join(content[u].get("text", "").split()[:400])])
        documents.append(without_brand(doc, profile))
    mode = options.get("matching_mode", "lexical")
    threshold = float(options.get("semantic_threshold", .45) if mode == "semantic" else options.get("lexical_threshold", .14))
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
            pair = (resolve_alias(source, aliases), resolve_alias(target, aliases))
            existing_body = {resolve_alias(u, aliases) for u in content[source].get("outgoing_content", [])}
            if source == target or pair in state["blocked_pairs"] or pair[1] in existing_body or source in per_source:
                continue
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
        if (idx + 1) % 20 == 0:
            log(f"Checked {idx + 1:,}/{len(targets):,} destinations.")
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


def create_job(profiles, stages, options):
    import psutil
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    job_id = datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:6]
    acquire_job_lock(job_id)
    folder = DATA_DIR / "jobs" / job_id
    folder.mkdir(parents=True)
    job_path = folder / "job.json"
    atomic_json(job_path, {"id": job_id, "profiles": profiles, "stages": stages, "options": options, "data_dir": str(DATA_DIR)})
    atomic_json(folder / "status.json", {"state": "queued", "created_at": utc_now(), "job_id": job_id, "completed": [], "errors": []})
    flags = subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
    try:
        with (folder / "worker.log").open("w", encoding="utf-8") as log:
            process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--worker", str(job_path)],
                                       stdout=log, stderr=subprocess.STDOUT, cwd=str(APP_DIR), creationflags=flags,
                                       start_new_session=os.name != "nt", shell=False)
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
    global DATA_DIR
    job_path = Path(job_path)
    job = read_json(job_path)
    DATA_DIR = Path(job["data_dir"])
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
        status["errors"].append({"error": str(exc)})
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


def render_settings(st, profiles, selected):
    st.title("Clients & settings")
    settings = read_json(DATA_DIR / "settings.json", {})
    with st.expander("Deployment & Screaming Frog settings", expanded=not profiles):
        with st.form("global_settings"):
            runtime = st.radio("Where is this app running?", ["hosted", "local"], index=0 if settings.get("runtime_mode", "hosted") == "hosted" else 1,
                               format_func=lambda x: "GitHub / Streamlit Cloud" if x == "hosted" else "Local computer with Screaming Frog installed")
            st.caption("In hosted mode, import Screaming Frog exports below. Cloud storage can be reset on reboot/redeploy; download workbooks and client settings you want to retain.")
            sf_path = st.text_input("Screaming Frog CLI executable (blank = auto-detect)", value=settings.get("sf_path", ""), placeholder=r"C:\Program Files\Screaming Frog SEO Spider\ScreamingFrogSEOSpiderCli.exe")
            timeout = st.number_input("Crawl timeout (minutes)", min_value=5, max_value=1440, value=int(settings.get("crawl_timeout_minutes", 180)))
            if st.form_submit_button("Save local settings"):
                settings = {**settings, "runtime_mode": runtime, "sf_path": sf_path.strip(), "crawl_timeout_minutes": int(timeout)}
                atomic_json(DATA_DIR / "settings.json", settings)
                st.success("Settings saved. No crawl was started.")
    with st.expander("Connect Google and discover properties", expanded=not profiles):
        hosted = settings.get("runtime_mode", "hosted") != "local"
        st.write("One read-only Google authorization is shared across client profiles. An already-authorized token from your IBML script can access the properties available to that Google account.")
        token_upload = st.file_uploader("Authorized GSC token JSON (optional if configured in Streamlit Secrets)", type="json", key="token_upload")
        if hosted:
            st.write("Use the token file created after Google login, such as gsc_token_ibml.json. An OAuth client-secret JSON alone is not an authorized token.")
            st.code("app_password = \"choose-a-private-password\"\ngsc_token_json = '''\nPASTE THE COMPLETE AUTHORIZED TOKEN JSON HERE\n'''", language="toml")
            st.caption("Add these in Streamlit → app Settings → Secrets. Keep credentials out of GitHub. You may instead upload the authorized token above for this running app instance.")
        else:
            secret = st.file_uploader("Google OAuth Desktop client JSON (for a new local login)", type=["json"], key="oauth_upload")
            if st.button("Save OAuth client file", disabled=secret is None):
                try:
                    value = json.loads(secret.getvalue())
                    if "installed" not in value:
                        raise ValueError("Use a Desktop app OAuth client, not a service-account or web-app JSON.")
                    atomic_json(DATA_DIR / "auth" / "oauth_client.json", value, private=True)
                    st.success("OAuth client saved locally.")
                except Exception as exc:
                    st.error(str(exc))
        if st.button("Connect Google / refresh property list"):
            try:
                with st.spinner("Connecting to Google…"):
                    token_info = None
                    if token_upload is not None:
                        token_info = json.loads(token_upload.getvalue())
                    else:
                        try:
                            saved = st.secrets.get("gsc_token_json", "")
                            if saved:
                                token_info = json.loads(saved) if isinstance(saved, str) else dict(saved)
                        except FileNotFoundError:
                            pass
                    if token_info is not None:
                        if not all(token_info.get(k) for k in ["refresh_token", "client_id", "client_secret"]):
                            raise ValueError("This is not a usable authorized token JSON. It must include refresh_token, client_id and client_secret.")
                        atomic_json(DATA_DIR / "auth" / "gsc_token.json", token_info, private=True)
                    service = google_service(interactive=not hosted)
                    properties = execute_google(lambda: service.sites().list()).get("siteEntry", [])
                    properties = [p for p in properties if p.get("permissionLevel") != "siteUnverifiedUser"]
                    atomic_json(DATA_DIR / "properties.json", properties)
                st.success(f"Connected. Found {len(properties)} accessible properties.")
            except Exception as exc:
                st.error(str(exc))
        properties = read_json(DATA_DIR / "properties.json", [])
        choices = [p["siteUrl"] for p in properties]
        if choices:
            picked = st.multiselect("Create client profiles from properties", choices, help="Choose one preferred property per client; domain and prefix properties may overlap.")
            if st.button("Add selected clients", disabled=not picked):
                profiles = read_json(DATA_DIR / "profiles.json", [])
                existing = {(urlsplit(p["root_url"]).hostname or "").removeprefix("www.") for p in profiles}
                added = 0
                for prop in picked:
                    root = "https://" + prop.split(":", 1)[1] + "/" if prop.startswith("sc-domain:") else prop
                    host = (urlsplit(root).hostname or "").removeprefix("www.")
                    if host in existing:
                        continue
                    profiles.append(default_profile(host, root, prop))
                    existing.add(host)
                    added += 1
                atomic_json(DATA_DIR / "profiles.json", profiles)
                st.success(f"Added {added} client(s). Existing domains were kept. Review each crawl URL, brand list and core-page list.")
    with st.expander("Add a client manually"):
        with st.form("new_client"):
            name = st.text_input("Client name")
            root = st.text_input("Website / homepage URL", placeholder="https://www.example.com/")
            prop = st.text_input("GSC property (optional)", placeholder="sc-domain:example.com")
            if st.form_submit_button("Create client"):
                try:
                    if not name.strip():
                        raise ValueError("Enter a client name.")
                    p = default_profile(name.strip(), root.strip(), prop.strip())
                    validate_profile(p)
                    current = read_json(DATA_DIR / "profiles.json", [])
                    current.append(p)
                    atomic_json(DATA_DIR / "profiles.json", current)
                    st.success("Client created. Select it from the sidebar to finish setup.")
                except Exception as exc:
                    st.error(str(exc))
    with st.expander("Back up / restore client settings"):
        st.download_button("Download client settings JSON", json.dumps(profiles, indent=2, ensure_ascii=False), "internal_link_clients.json", "application/json", on_click="ignore", disabled=not profiles)
        backup = st.file_uploader("Client settings JSON to restore", type="json", key="profile_restore")
        if st.button("Import / merge client settings", disabled=backup is None):
            try:
                loaded = json.loads(backup.getvalue())
                if not isinstance(loaded, list):
                    raise ValueError("Expected a list of client profiles.")
                current = {r["id"]: r for r in read_json(DATA_DIR / "profiles.json", [])}
                for item in loaded:
                    validate_profile(item)
                    if not item.get("id") or slug(item["id"]) != item["id"]:
                        raise ValueError("Invalid client profile ID.")
                    current[item["id"]] = item
                atomic_json(DATA_DIR / "profiles.json", list(current.values()))
                st.success("Client settings merged. Credentials and crawl datasets are not included in this backup.")
            except Exception as exc:
                st.error(str(exc))
    if selected:
        p = selected
        st.subheader(f"Edit {p['name']}")
        with st.form("edit_profile_" + p["id"]):
            name = st.text_input("Client name", p["name"])
            root = st.text_input("Crawl start / homepage URL", p["root_url"])
            prop = st.text_input("Preferred GSC property", p.get("gsc_property", ""))
            brand_terms = st.text_area("Brand exclusions — one term per line", "\n".join(p.get("brand_terms", [])), help="Include company names, variants, abbreviations and branded products. Terms use word boundaries.")
            confirmed = st.checkbox("I have reviewed these brand terms", value=p.get("brands_confirmed", False))
            core = st.text_area("Approved core pages — URL | topic | priority (1–5)", "\n".join(f"{c['url']} | {c.get('topic', '')} | {c.get('priority', 3)}" for c in p.get("core_pages", [])), height=180,
                                placeholder="https://www.example.com/services/document-scanning/ | document scanning services | 5")
            blogs = st.text_input("Blog URL path regex", p.get("blog_pattern", ""))
            exclusions = st.text_input("Excluded destination paths regex", p.get("exclude_pattern", ""))
            hosts = st.text_area("Allowed hosts — one per line", "\n".join(p.get("allowed_hosts", [])))
            selector = st.text_input("Main content CSS selector (optional)", p.get("main_selector", ""), help="Examples: main, article .entry-content. Set this if shared modules appear in recommendations.")
            sf_config = st.text_input("Saved Screaming Frog configuration path (optional)", p.get("sf_config", ""))
            sitemap_urls = st.text_area("Sitemap URLs (optional, one per line)", "\n".join(p.get("sitemap_urls", [])))
            if st.form_submit_button("Save client profile", type="primary"):
                try:
                    changed = {**p, "name": name.strip(), "root_url": url_key(root), "gsc_property": prop.strip(),
                               "brand_terms": [x.strip() for x in brand_terms.splitlines() if x.strip()], "brands_confirmed": confirmed,
                               "core_pages": parse_core_lines(core), "blog_pattern": blogs.strip(), "exclude_pattern": exclusions.strip(),
                               "allowed_hosts": [x.strip().lower() for x in hosts.splitlines() if x.strip()], "main_selector": selector.strip(),
                               "sf_config": sf_config.strip(), "sitemap_urls": [x.strip() for x in sitemap_urls.splitlines() if x.strip()]}
                    validate_profile(changed)
                    current = read_json(DATA_DIR / "profiles.json", [])
                    atomic_json(DATA_DIR / "profiles.json", [changed if c["id"] == p["id"] else c for c in current])
                    st.success("Client saved. Saved analyses will show as outdated if their inputs changed.")
                except Exception as exc:
                    st.error(str(exc))
        with st.expander("Import an existing Screaming Frog crawl"):
            st.write("Export Internal:All and Bulk Export → Links → All Inlinks from the same crawl. Include Link Position for contextual analysis. Importing does not crawl or fetch pages.")
            internal = st.file_uploader("Internal:All CSV", type="csv", key="import_internal_" + p["id"])
            inlinks = st.file_uploader("All Inlinks CSV", type="csv", key="import_inlinks_" + p["id"])
            if st.button("Import both CSVs", disabled=internal is None or inlinks is None):
                try:
                    counts = save_crawl(p, read_sf_csv(io.BytesIO(internal.getvalue())), read_sf_csv(io.BytesIO(inlinks.getvalue())), "Manual SF CSV import", root=p["root_url"])
                    st.success(f"Imported {counts[0]:,} pages and {counts[1]:,} hyperlink records.")
                except Exception as exc:
                    st.error(str(exc))


def render_job_monitor(st):
    @st.fragment(run_every="3s")
    def monitor():
        folders = sorted((DATA_DIR / "jobs").glob("*/status.json"), reverse=True)[:5]
        if not folders:
            st.caption("No jobs have been started.")
        for path in folders:
            status = read_json(path, {})
            job_id = path.parent.name
            st.write(f"**{job_id}** — {status.get('state', 'unknown')}")
            if status.get("client"):
                st.caption(f"{status['client']} · {status.get('stage', '')} · {status.get('message', '')}")
            if status.get("state") in {"queued", "running", "cancelling"}:
                if st.button("Cancel job", key="cancel_" + job_id):
                    (path.parent / "cancel").touch()
                    st.info("Cancellation requested. Active HTTP requests may finish before the worker stops.")
            if status.get("errors"):
                st.dataframe(pd.DataFrame(status["errors"]), hide_index=True)
            with st.expander("Job log", expanded=False):
                log_path = path.parent / "worker.log"
                st.code(log_path.read_text(encoding="utf-8", errors="replace")[-14000:] if log_path.exists() else "Starting…", language="text")
    monitor()


def render_run(st, profiles, selected):
    st.title("Run selected tools")
    st.write("Choose the actions you want. Nothing runs automatically when you open a page or change a filter. Selected actions run in the order shown; unselected prerequisites must already have saved data.")
    settings = read_json(DATA_DIR / "settings.json", {})
    labels = {p["id"]: p["name"] for p in profiles}
    chosen = st.multiselect("Clients in this batch", list(labels), default=[selected["id"]] if selected else [], format_func=lambda x: labels[x])
    available_stages = list(STAGES) if settings.get("runtime_mode", "hosted") == "local" else [k for k in STAGES if k != "crawl"]
    if "crawl" not in available_stages:
        st.info("Hosted mode: import Screaming Frog CSVs in Clients & settings. Running your desktop installation requires Local computer mode on that computer.")
    actions = st.multiselect("Actions to run", available_stages, default=[], format_func=lambda x: STAGES[x])
    options = dict(settings)
    if "gsc" in actions:
        with st.expander("GSC options", expanded=True):
            try:
                today_pt = datetime.now(ZoneInfo("America/Los_Angeles")).date()
            except Exception:
                today_pt = date.today()
            end_default = today_pt - timedelta(days=3)
            cols = st.columns(2)
            options["start_date"] = str(cols[0].date_input("GSC start date (Pacific reporting dates)", end_default - timedelta(days=89)))
            options["end_date"] = str(cols[1].date_input("GSC end date", end_default))
            options["brand_mode"] = st.selectbox("Non-brand classification", ["auto", "native", "local"], format_func=lambda x: {"auto": "Google classification when available; otherwise local brand rules", "native": "Require Google classification", "local": "Use local brand rules"}[x])
            options["daily_gsc"] = st.checkbox("Download query data one day at a time", value=False, help="More API calls; can improve visible row coverage on larger sites. Weekly chunks are the default.")
            st.caption("Page metrics are requested separately from query rows. Native classification and query-text filters are not combined.")
    if "sitemaps" in actions:
        options["sitemap_cap"] = int(st.number_input("Maximum sitemap files to request", 1, 500, 50))
    if "content" in actions:
        with st.expander("Content options", expanded=True):
            st.caption("Content fetching reads server-returned HTML. JavaScript-only body copy may be unavailable; failed extractions are listed in Content diagnostics.")
            options["all_content"] = st.checkbox("Fetch all eligible HTML pages", value=False, help="Default: blogs and approved core pages only.")
            options["refresh_content"] = st.checkbox("Refresh even recently cached content", value=False)
            options["cache_hours"] = float(st.number_input("Reuse successful content younger than (hours)", 0.0, 720.0, 24.0))
            options["content_cap"] = int(st.number_input("Maximum pages to fetch / retain for this analysis", 1, 100000, 1500))
            options["fetch_workers"] = int(st.number_input("Concurrent content requests", 1, 8, 3))
            options["request_delay"] = float(st.number_input("Minimum delay between request starts (seconds)", 0.2, 30.0, 0.6))
    if "recommendations" in actions:
        with st.expander("Recommendation options", expanded=True):
            options["blog_to_blog"] = st.checkbox("Include blog-to-blog destinations", value=False)
            options["all_sources"] = st.checkbox("Allow sources beyond blogs", value=False)
            options["matching_mode"] = st.selectbox("Paragraph matching", ["lexical", "semantic"], format_func=lambda x: "Local word / phrase similarity (standard install)" if x == "lexical" else "Local semantic model (optional install)")
            if options["matching_mode"] == "semantic":
                st.caption("Optional: add sentence-transformers>=3.3,<6 to requirements.txt and redeploy. The model runs on the app host; first use needs model files and additional memory.")
                options["allow_model_download"] = st.checkbox("Allow downloading the semantic model if it is not cached", value=False)
                options["semantic_threshold"] = st.slider("Minimum semantic paragraph similarity", .2, .9, .45, .01)
            else:
                options["lexical_threshold"] = st.slider("Minimum word / phrase paragraph similarity", .05, .6, .14, .01)
            cols = st.columns(3)
            options["links_per_source"] = int(cols[0].number_input("Suggestions per source", 1, 20, 3))
            options["links_per_target"] = int(cols[1].number_input("Suggestions per destination", 1, 50, 5))
            options["recommendation_cap"] = int(cols[2].number_input("Total suggestions per client", 1, 10000, 300))
            with st.container(border=True):
                st.caption("Analysis size limits")
                options["target_cap"] = int(st.number_input("Maximum destinations to check", 1, 10000, 250))
                options["paragraph_cap"] = int(st.number_input("Maximum source paragraphs to compare", 100, 200000, 30000))
                options["paragraphs_per_target"] = int(st.number_input("Candidate paragraphs inspected per destination", 10, 2000, 120))
                options["ambiguity_margin"] = float(st.number_input("Skip competing destinations within this similarity margin", 0.0, .2, .04, .01))
            st.caption("Homepage and branded anchors are always excluded from new recommendations. Caps control review workload and are not Google rules.")
    if "audit" in actions:
        with st.expander("Audit options", expanded=True):
            options["audit_checks"] = st.multiselect("Checks to run", list(AUDITS), default=["orphans", "buried", "support"], format_func=lambda x: AUDITS[x])
            options["depth_threshold"] = int(st.number_input("Flag core pages at this depth or deeper", 2, 30, 4))
            options["minimum_contextual_sources"] = int(st.number_input("Flag core pages with fewer contextual source pages than", 1, 50, 2))
    if st.button("Run selected actions", type="primary"):
        try:
            if not chosen or not actions:
                raise ValueError("Select at least one client and one action.")
            if "audit" in actions and not options.get("audit_checks"):
                raise ValueError("Choose at least one audit check.")
            picked_profiles = [p for p in profiles if p["id"] in chosen]
            for p in picked_profiles:
                validate_profile(p)
            job_id = create_job(picked_profiles, actions, options)
            st.success(f"Started {job_id}. You can switch screens; the local worker continues.")
        except Exception as exc:
            st.error(str(exc))
    st.subheader("Recent jobs")
    render_job_monitor(st)


def render_recommendations(st, p):
    st.title("Contextual link opportunities")
    doc = dataset(p, "recommendations")
    if not doc["meta"]:
        st.info("Choose Find contextual link opportunities in Run selected tools. No analysis runs when you open this view.")
        return
    if doc["meta"].get("input_signature") != input_signature(p, REC_INPUTS):
        st.warning("Inputs have changed since these recommendations were generated. Run recommendations again before implementation.")
    show_saved_warnings(st, doc)
    reviews = read_json(client_dir(p) / "reviews.json", {})
    rows = [{**r, **reviews.get(r["id"], {})} for r in doc["rows"]]
    st.caption(f"Saved {doc['meta'].get('created_at')} · {len(rows)} recommendations · {doc['meta'].get('ambiguous_slots_skipped', 0)} ambiguous placements skipped")
    if not rows:
        st.info("No opportunities passed the selected rules. Review extraction, targets, matching mode and thresholds; the app does not force recommendations.")
        return
    cols = st.columns(2)
    statuses = cols[0].multiselect("Review status", ["Proposed", "Approved", "Dismissed", "Implemented"], default=["Proposed", "Approved"])
    search = cols[1].text_input("Filter source, destination, anchor or topic")
    df = pd.DataFrame(rows)
    filtered = df[df["status"].isin(statuses)]
    if search:
        filtered = filtered[filtered[["source_url", "destination_url", "anchor_text", "destination_topic"]].astype(str).apply(lambda c: c.str.contains(search, case=False, regex=False)).any(axis=1)]
    columns = ["id", "status", "priority", "source_url", "destination_url", "anchor_text", "context", "destination_nonbrand_impressions", "destination_nonbrand_position", "reason", "notes"]
    edited = st.data_editor(filtered[columns], hide_index=True, width="stretch", key="review_" + p["id"],
                            disabled=[c for c in columns if c not in {"status", "notes"}],
                            column_config={"id": None, "status": st.column_config.SelectboxColumn(options=["Proposed", "Approved", "Dismissed", "Implemented"], required=True),
                                           "source_url": st.column_config.LinkColumn("Source"), "destination_url": st.column_config.LinkColumn("Destination"), "context": st.column_config.TextColumn("Existing paragraph", width="large")})
    if st.button("Save review decisions"):
        for row in edited.to_dict("records"):
            reviews[row["id"]] = {"status": row["status"], "notes": text_norm(row.get("notes", ""))}
        atomic_json(client_dir(p) / "reviews.json", reviews)
        st.success("Review decisions saved. Dismissed and implemented placements are suppressed on later recommendation runs.")
    if not filtered.empty:
        chosen_id = st.selectbox("Inspect placement", filtered["id"].tolist(), format_func=lambda x: next(f"{r['anchor_text']} → {r['destination_url']}" for r in rows if r["id"] == x))
        row = next(r for r in rows if r["id"] == chosen_id)
        st.write("**Existing paragraph**")
        st.write(row["context"])
        st.write("**Use this exact unlinked phrase:**", row["anchor_text"])
        st.code(row["source_locator"], language="css")
        st.caption(f"Paragraph similarity {row['paragraph_similarity']} ({row['matching_mode']}); heuristic priority score {row['heuristic_score']}. Scores are not ranking forecasts.")


def render_audit(st, p):
    st.title("Existing internal-link audit")
    doc = dataset(p, "audit")
    if not doc["meta"]:
        st.info("Choose Audit existing internal links in Run selected tools, then select the checks you need.")
        return
    if doc["meta"].get("input_signature") != input_signature(p, AUDIT_INPUTS):
        st.warning("The available crawl, GSC, sitemap or profile data has changed. These audit findings are from the previous snapshot.")
    show_saved_warnings(st, doc)
    st.caption(doc["meta"].get("coverage", ""))
    df = pd.DataFrame(doc["rows"])
    if df.empty:
        st.info("No findings for the checks selected in the saved audit.")
    else:
        issues = st.multiselect("Issue types", sorted(df["issue"].unique()), default=sorted(df["issue"].unique()))
        st.dataframe(df[df["issue"].isin(issues)], hide_index=True, width="stretch")
    with st.expander("Saved page summary"):
        st.dataframe(pd.DataFrame(dataset(p, "page_summary")["rows"]), hide_index=True, width="stretch")


def render_visuals(st, p):
    st.title("Site structure & opportunity")
    st.write("Build only the view you need from saved data. Graphs are capped for readability.")
    with st.form("visual_options_" + p["id"]):
        kind = st.selectbox("View", ["Opportunity chart", "Topic graph", "Crawl tree"])
        topic = st.text_input("Filter topic labels (optional)")
        focus = st.text_input("Focus on a page and its immediate neighbors (optional URL)")
        cap = st.slider("Maximum graph nodes", 20, 300, 150, 10)
        core_only = st.checkbox("Show core pages only", value=False)
        content_only = st.checkbox("Graph contextual links only", value=False)
        show_proposed = st.checkbox("Overlay saved proposed links", value=False)
        submitted = st.form_submit_button("Build selected visualization", type="primary")
    cache_key = "visual_" + p["id"]
    if submitted:
        try:
            with st.spinner("Building this view…"):
                result = make_visual(p, {"visual_type": kind, "topic": topic, "focus_url": url_key(focus), "node_cap": cap,
                                         "core_only": core_only, "content_only": content_only, "show_proposed": show_proposed})
                st.session_state[cache_key] = (*result, input_signature(p, AUDIT_INPUTS + ["recommendations"]))
        except Exception as exc:
            st.error(str(exc))
    if cache_key in st.session_state:
        figure, rows, note, signature = st.session_state[cache_key]
        if signature != input_signature(p, AUDIT_INPUTS + ["recommendations"]):
            st.warning("Saved data changed. Build the visualization again to refresh it.")
        st.plotly_chart(figure, width="stretch")
        st.caption(note)
        with st.expander("Pages shown"):
            st.dataframe(pd.DataFrame(rows), hide_index=True, width="stretch")
        with st.expander("Existing link directions for shown pages"):
            nodes = {r["url"] for r in rows}
            links = [r for r in dataset(p, "links")["rows"] if r["source"] in nodes and r["destination"] in nodes]
            st.dataframe(pd.DataFrame(links), hide_index=True, width="stretch")


def render_export(st, profiles, selected):
    st.title("Export workbook")
    st.write("Choose clients and sheets. Export uses saved results and does not rerun crawling or analysis.")
    labels = {p["id"]: p["name"] for p in profiles}
    ids = st.multiselect("Clients to export", list(labels), default=[selected["id"]] if selected else [], format_func=lambda x: labels[x])
    sheets = st.multiselect("Workbook sheets", ["Recommendations", "Existing-link issues", "Page summary", "GSC pages", "GSC queries", "Content diagnostics", "Existing links", "Run summary"],
                            default=["Recommendations", "Existing-link issues", "Page summary", "Run summary"])
    if st.button("Prepare selected workbook", type="primary"):
        try:
            if not ids or not sheets:
                raise ValueError("Choose at least one client and one sheet.")
            picked = [p for p in profiles if p["id"] in ids]
            with st.spinner("Preparing workbook…"):
                content = workbook_bytes(picked, sheets)
            filename = f"internal_links_{datetime.now().strftime('%Y%m%d_%H%M%S')}.xlsx"
            path = DATA_DIR / "exports" / filename
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
            st.session_state["export_payload"] = (filename, content)
            st.success("Workbook prepared. Run summary identifies saved dates, coverage and outdated analyses when that sheet is included.")
        except Exception as exc:
            st.error(str(exc))
    if "export_payload" in st.session_state:
        filename, content = st.session_state["export_payload"]
        st.download_button("Download prepared workbook", data=content, file_name=filename, mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", on_click="ignore")


def main():
    import streamlit as st
    st.set_page_config(page_title="Internal linking workbench", page_icon="🔗", layout="wide")
    try:
        password = st.secrets.get("app_password", "")
    except FileNotFoundError:
        password = ""
    if password and not st.session_state.get("_authenticated"):
        st.title("Internal linking workbench")
        entered = st.text_input("App password", type="password")
        if st.button("Sign in"):
            if hmac.compare_digest(entered.encode("utf-8"), str(password).encode("utf-8")):
                st.session_state["_authenticated"] = True
                st.rerun()
            else:
                st.error("Incorrect password.")
        st.stop()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    profiles = read_json(DATA_DIR / "profiles.json", [])
    st.sidebar.title("Internal linking workbench")
    selected = None
    if profiles:
        profile_ids = [p["id"] for p in profiles]
        if st.session_state.get("selected_client") not in profile_ids:
            st.session_state["selected_client"] = profile_ids[0]
        client_id = st.sidebar.selectbox("Client", profile_ids, key="selected_client", format_func=lambda x: next(p["name"] for p in profiles if p["id"] == x))
        selected = next(p for p in profiles if p["id"] == client_id)
    screens = ["Clients & settings", "Run selected tools", "Recommendations", "Audit", "Visualizations", "Export", "Demo & help"]
    screen = st.sidebar.radio("Open", screens)
    st.sidebar.caption("Every feature runs only when you request it. Saved data is reused across screens.")
    if selected:
        if selected.get("demo"):
            st.info("Demo client: all pages and metrics are synthetic. No live website data is represented.")
        docs = [dataset(selected, name) for name in ["pages", "gsc_pages", "content", "recommendations"]]
        cols = st.columns(4)
        for col, label, doc in zip(cols, ["Crawled URLs", "Non-brand GSC pages", "Content records", "Saved opportunities"], docs):
            col.metric(label, len(doc["rows"]))
    if screen == "Clients & settings":
        render_settings(st, profiles, selected)
    elif screen == "Demo & help":
        st.title("Try the workflow")
        st.write("The demo creates local synthetic crawl, content, sitemap and GSC datasets. It does not run recommendations, audits, charts or exports.")
        if st.button("Create / reset synthetic demo client"):
            install_demo()
            st.success("Demo datasets created. Select the demo client, then choose the individual tools you want to try.")
        st.markdown("""1. Select a client and review its settings.\n2. Import Internal:All and All Inlinks CSV exports from the same Screaming Frog crawl. In Local computer mode you can launch a crawl from this app.\n3. Choose sitemap discovery, GSC download and content fetching as needed.\n4. Run recommendations or selected audit checks against saved inputs.\n5. Review results, build a visualization, or export selected sheets.\n\n**GitHub deployment:** Commit only app.py and requirements.txt at repository root. Set the Streamlit entrypoint to app.py. Use Streamlit Secrets for app_password and gsc_token_json, or upload an authorized GSC token in Clients & settings. The app works with demo data before any credentials are added.\n\n**Cloud storage:** Download workbooks and client-settings backups you want to retain; files on the app host may be lost on reboot/redeploy. This version does not include a remote worker controlling your laptop.\n\n**Optional semantic mode:** Add sentence-transformers>=3.3,<6 to requirements.txt and redeploy. It uses additional host memory. Standard word/phrase matching works with the supplied requirements.\n\n**Local setup:** Install Python 3.11 or 3.12, run `python -m pip install -r requirements.txt`, then `python -m streamlit run app.py`. Choose Local computer mode in settings to enable desktop OAuth and the licensed Screaming Frog CLI.\n\n**Quality checks:** Confirm the phrase and destination in the live page before implementation. Crawl depth, similarity and internal rank are local models; important navigation changes may require a separate implementation task.""")
    elif screen == "Run selected tools":
        render_run(st, profiles, selected)
    elif screen == "Export":
        render_export(st, profiles, selected)
    elif not selected:
        st.info("Add a client or create the demo client first.")
    elif screen == "Recommendations":
        render_recommendations(st, selected)
    elif screen == "Audit":
        render_audit(st, selected)
    elif screen == "Visualizations":
        render_visuals(st, selected)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--worker", type=Path)
    args, _ = parser.parse_known_args()
    if args.worker:
        worker_main(args.worker)
    else:
        main()
