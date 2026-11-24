#!/usr/bin/env python3
"""Verify BibTeX references (`papers/*/refs.bib`) offline and via arXiv / Crossref APIs.

Zero third-party dependencies.

Usage:
    python3 scripts/verify_refs.py --offline
    python3 scripts/verify_refs.py
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "papers"
ATOM_NS = {"atom": "http://www.w3.org/2005/Atom"}
STOPWORDS = {
    "a", "an", "and", "at", "by", "for", "from", "in", "of", "on", "the", "to", "with",
}


@dataclass
class BibEntry:
    path: Path
    entry_type: str
    key: str
    line: int
    fields: dict[str, str] = field(default_factory=dict)


def normalise_ascii(text: str) -> str:
    """Fold TeX accents / Unicode into lowercase ASCII words."""
    # Strip simple TeX accent macros like {\"o} or \H{o}
    text = re.sub(r"\\[A-Za-z`'^\"~=.]+\{([A-Za-z])\}", r"\1", text)
    text = re.sub(r"\\[A-Za-z]+\s*", " ", text)
    text = text.replace("{", "").replace("}", "")
    decomposed = unicodedata.normalize("NFKD", text)
    ascii_only = "".join(ch for ch in decomposed if not unicodedata.combining(ch))
    return ascii_only.lower()


def extract_first_surname(author_field: str) -> str:
    """Extract the first author's surname in normalized lowercase ASCII."""
    first = re.split(r"\s+and\s+", author_field, maxsplit=1, flags=re.IGNORECASE)[0].strip()
    if "," in first:
        surname = first.split(",", 1)[0].strip()
    else:
        parts = [p for p in re.split(r"\s+", first) if p]
        surname = parts[-1] if parts else ""
    cleaned = re.sub(r"[^a-z]", "", normalise_ascii(surname))
    return cleaned


def title_keywords(title: str) -> set[str]:
    """Return significant lowercase alphabetic words (length >= 4) from a title."""
    words = re.findall(r"[a-z]{4,}", normalise_ascii(title))
    return {w for w in words if w not in STOPWORDS}


def parse_bib_file(path: Path) -> list[BibEntry]:
    """Parse entries from a BibTeX `.bib` file cleanly with brace tracking."""
    text = path.read_text(encoding="utf-8")
    entries: list[BibEntry] = []
    i = 0
    n = len(text)

    while i < n:
        at_idx = text.find("@", i)
        if at_idx == -1:
            break
        m = re.match(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", text[at_idx:])
        if not m:
            i = at_idx + 1
            continue
        entry_type = m.group(1).lower()
        key = m.group(2)
        line_no = text[:at_idx].count("\n") + 1
        pos = at_idx + m.end()
        depth = 1
        body_start = pos
        while pos < n and depth > 0:
            ch = text[pos]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            pos += 1
        body = text[body_start : pos - 1]
        fields: dict[str, str] = {}
        j = 0
        bn = len(body)
        while j < bn:
            fm = re.match(r"\s*([A-Za-z0-9_-]+)\s*=\s*", body[j:])
            if not fm:
                j += 1
                continue
            fname = fm.group(1).lower()
            j += fm.end()
            if j >= bn:
                break
            if body[j] == "{":
                fdepth = 1
                j += 1
                vstart = j
                while j < bn and fdepth > 0:
                    if body[j] == "{":
                        fdepth += 1
                    elif body[j] == "}":
                        fdepth -= 1
                    j += 1
                val = body[vstart : j - 1]
            elif body[j] == '"':
                j += 1
                vstart = j
                while j < bn and body[j] != '"':
                    if body[j] == "\\" and j + 1 < bn:
                        j += 2
                    else:
                        j += 1
                val = body[vstart:j]
                j += 1
            else:
                vstart = j
                while j < bn and body[j] not in ",\r\n":
                    j += 1
                val = body[vstart:j].strip()
            fields[fname] = re.sub(r"\s+", " ", val.strip())
            comma = body.find(",", j)
            if comma == -1:
                break
            j = comma + 1
        entries.append(BibEntry(path=path, entry_type=entry_type, key=key, line=line_no, fields=fields))
        i = pos

    return entries


def http_get_text(url: str, retries: int = 3, delay: float = 1.5) -> str:
    """Fetch `url` with retry/backoff for transient 429/5xx limits."""
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "mahler32-ref-verifier/1.0 (+https://github.com/3y3y3y-huaiji/mahler32)"},
    )
    last_err: Exception | None = None
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                return resp.read().decode("utf-8", errors="replace")
        except urllib.error.HTTPError as exc:
            last_err = exc
            if exc.code in (429, 500, 502, 503, 504) and attempt + 1 < retries:
                time.sleep(delay * (2 ** attempt))
                continue
            raise
        except urllib.error.URLError as exc:
            last_err = exc
            if attempt + 1 < retries:
                time.sleep(delay * (2 ** attempt))
                continue
            raise
    assert last_err is not None
    raise last_err


def verify_arxiv(eprint: str, entry: BibEntry) -> tuple[bool, str]:
    """Query export.arxiv.org API and check ID existence, author surname, and title overlap."""
    clean_id = re.sub(r"^arXiv:", "", eprint.strip(), flags=re.IGNORECASE)
    clean_id = re.sub(r"v\d+$", "", clean_id)
    url = f"https://export.arxiv.org/api/query?id_list={urllib.parse.quote(clean_id)}"
    xml_text = http_get_text(url)
    root = ET.fromstring(xml_text)
    entries = root.findall("atom:entry", ATOM_NS)
    if not entries:
        return False, f"arXiv ID `{clean_id}` returned no entries"
    node = entries[0]
    remote_title_el = node.find("atom:title", ATOM_NS)
    if remote_title_el is None or not (remote_title_el.text or "").strip():
        return False, f"arXiv ID `{clean_id}` has missing metadata/title (possibly nonexistent)"
    remote_title = re.sub(r"\s+", " ", remote_title_el.text or "").strip()
    if remote_title.lower().startswith("error"):
        return False, f"arXiv API error for `{clean_id}`: {remote_title}"

    remote_authors = [
        (a.find("atom:name", ATOM_NS).text or "").strip()
        for a in node.findall("atom:author", ATOM_NS)
        if a.find("atom:name", ATOM_NS) is not None
    ]
    if not remote_authors:
        return False, f"arXiv ID `{clean_id}` returned empty author list"

    local_surname = extract_first_surname(entry.fields.get("author", ""))
    remote_author_blob = normalise_ascii(" ".join(remote_authors))
    if local_surname and local_surname not in remote_author_blob:
        return (
            False,
            f"arXiv `{clean_id}` author mismatch: expected `{local_surname}`, got {remote_authors!r}",
        )

    local_kw = title_keywords(entry.fields.get("title", ""))
    remote_kw = title_keywords(remote_title)
    if local_kw and not (local_kw & remote_kw):
        return (
            False,
            f"arXiv `{clean_id}` title mismatch: local `{entry.fields.get('title')}` vs remote `{remote_title}`",
        )
    return True, f"arXiv:{clean_id} matched ({remote_authors[0]} — {remote_title})"


def verify_doi(doi: str, entry: BibEntry) -> tuple[bool, str]:
    """Query api.crossref.org for `doi` metadata match."""
    clean_doi = doi.strip()
    url = f"https://api.crossref.org/works/{urllib.parse.quote(clean_doi)}"
    data = json.loads(http_get_text(url))
    msg = data.get("message", {})
    titles = msg.get("title") or []
    remote_title = titles[0] if titles else ""
    authors = [f"{a.get('given', '')} {a.get('family', '')}".strip() for a in msg.get("author") or []]
    local_surname = extract_first_surname(entry.fields.get("author", ""))
    remote_author_blob = normalise_ascii(" ".join(authors))
    if local_surname and local_surname not in remote_author_blob:
        return False, f"DOI `{clean_doi}` author mismatch: expected `{local_surname}`, got {authors!r}"
    local_kw = title_keywords(entry.fields.get("title", ""))
    remote_kw = title_keywords(remote_title)
    if local_kw and remote_kw and not (local_kw & remote_kw):
        return (
            False,
            f"DOI `{clean_doi}` title mismatch: local `{entry.fields.get('title')}` vs remote `{remote_title}`",
        )
    return True, f"DOI:{clean_doi} matched ({remote_title})"


def check_offline(entry: BibEntry) -> list[str]:
    """Validate structural BibTeX fields without network access."""
    errs: list[str] = []
    rel = entry.path.relative_to(ROOT)
    for req in ("author", "title", "year"):
        if not entry.fields.get(req):
            errs.append(f"{rel}:{entry.line} [{entry.key}]: missing or empty `{req}`")
    eprint = entry.fields.get("eprint", "")
    if eprint and not re.match(r"^(?:arXiv:)?(?:\d{4}\.\d{4,5}|[a-z\-]+(?:\.[A-Z]{2})?/\d{7})(?:v\d+)?$", eprint):
        errs.append(f"{rel}:{entry.line} [{entry.key}]: malformed eprint `{eprint}`")
    doi = entry.fields.get("doi", "")
    if doi and not re.match(r"^10\.\d{4,9}/\S+$", doi):
        errs.append(f"{rel}:{entry.line} [{entry.key}]: malformed DOI `{doi}`")
    return errs


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Verify BibTeX entries offline or via arXiv/Crossref.")
    parser.add_argument("--offline", action="store_true", help="Run offline field/format checks only.")
    args = parser.parse_args(argv)

    bib_files = sorted(PAPERS_DIR.glob("*/refs.bib"))
    if not bib_files:
        print("ERROR: no papers/*/refs.bib files found", file=sys.stderr)
        return 1

    # Deduplicate identical queries across companion papers' refs.bib
    cache: dict[tuple[str, str], tuple[bool, str]] = {}
    errors: list[str] = []

    for bib in bib_files:
        entries = parse_bib_file(bib)
        print(f"Checking {bib.relative_to(ROOT)} ({len(entries)} entries)...")
        for entry in entries:
            off_errs = check_offline(entry)
            errors.extend(off_errs)
            if args.offline or off_errs:
                continue

            eprint = entry.fields.get("eprint", "")
            doi = entry.fields.get("doi", "")
            archive_prefix = entry.fields.get("archiveprefix", "").lower()

            if eprint and (archive_prefix in ("", "arxiv")):
                ck = ("arxiv", eprint)
                if ck not in cache:
                    try:
                        cache[ck] = verify_arxiv(eprint, entry)
                    except (urllib.error.URLError, urllib.error.HTTPError, ET.ParseError) as exc:
                        cache[ck] = (False, f"arXiv lookup error for `{eprint}`: {exc}")
                    time.sleep(0.8)
                ok, msg = cache[ck]
                print(f"  [{'OK' if ok else 'FAIL'}] {entry.key}: {msg}")
                if not ok:
                    errors.append(f"{bib.relative_to(ROOT)}:{entry.line} [{entry.key}]: {msg}")

            elif doi:
                ck = ("doi", doi)
                if ck not in cache:
                    try:
                        cache[ck] = verify_doi(doi, entry)
                    except (urllib.error.URLError, urllib.error.HTTPError, json.JSONDecodeError) as exc:
                        cache[ck] = (False, f"Crossref lookup error for `{doi}`: {exc}")
                    time.sleep(0.4)
                ok, msg = cache[ck]
                print(f"  [{'OK' if ok else 'FAIL'}] {entry.key}: {msg}")
                if not ok:
                    errors.append(f"{bib.relative_to(ROOT)}:{entry.line} [{entry.key}]: {msg}")
            else:
                print(f"  [SKIP-NO-ID] {entry.key} (offline format ok; no arXiv eprint or DOI)")

    if errors:
        print("\nVerification failures:", file=sys.stderr)
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1

    print("verify_refs: all checked citations passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
