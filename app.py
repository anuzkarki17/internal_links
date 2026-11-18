
    
  
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


