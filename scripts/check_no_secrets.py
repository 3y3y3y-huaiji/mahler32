#!/usr/bin/env python3
"""Block credentials and stray scratch files from entering this repository.

Two independent guards, both cheap and both deliberately blunt:

1. Content guard.  Any text file that looks like it carries a credential is
   refused.  The patterns below are the shapes actually produced by the
   Palomar submission flow (`access_token`, `pending_secret`, `Authorization:
   Bearer ...`) plus the common GitHub, AWS and Slack token prefixes and PEM
   private keys.
2. Layout guard.  Scratch responses belong outside the repository, so a `.json`
   file at the repository root is refused unless it is one of the two files
   that belong there.  Symlinks are refused outright.

Usage:
    python3 scripts/check_no_secrets.py --staged   # pre-commit: index only
    python3 scripts/check_no_secrets.py --tree     # CI: every tracked file
    python3 scripts/check_no_secrets.py --paths a.json b.txt

Exit status is 1 if anything is refused, so both a pre-commit hook and a CI
step can use it unchanged.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

# Root-level `.json` files that legitimately belong to the project.
ALLOWED_ROOT_JSON = {"comparator.json", "lake-manifest.json"}

# Filenames that the submission flow writes and that must never be committed,
# wherever they appear.
FORBIDDEN_NAMES = re.compile(
    r"""^(
        \.submit.*\.json | \.verify.*\.json | \.status\.json |
        \.tag_resp\.json | \.gist_resp\.json | \.review\.json | st\.json
    )$""",
    re.VERBOSE,
)

SECRET_PATTERNS = [
    (re.compile(r"access_token"), "contains `access_token`"),
    (re.compile(r"pending_secret"), "contains `pending_secret`"),
    (re.compile(r"Bearer\s+\S{8,}"), "contains a `Bearer <credential>` header"),
    (re.compile(r"\bgh[pousr]_[A-Za-z0-9]{20,}"), "contains a GitHub token"),
    (re.compile(r"\bgithub_pat_[A-Za-z0-9_]{20,}"), "contains a fine-grained GitHub token"),
    (re.compile(r"\bAKIA[0-9A-Z]{16}\b"), "contains an AWS access key id"),
    (re.compile(r"\bxox[baprs]-[A-Za-z0-9-]{10,}"), "contains a Slack token"),
    (re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----"), "contains a private key"),
]

# These two files have to name the patterns in order to forbid them, so the three
# keyword rules below would match their own documentation.  The exemption is
# narrow on purpose: every token-shape rule (GitHub/AWS/Slack prefixes, PEM keys)
# still applies to them, so a real credential pasted into either file is still
# refused.
SELF_REFERENTIAL = {"AGENTS.md", "scripts/check_no_secrets.py"}
KEYWORD_RULES = {"contains `access_token`", "contains `pending_secret`",
                 "contains a `Bearer <credential>` header"}

MAX_BYTES = 2 * 1024 * 1024


def git(*args: str) -> list[str]:
    out = subprocess.run(
        ["git", *args], check=True, capture_output=True, text=True
    ).stdout
    return [line for line in out.splitlines() if line]


def staged_paths() -> list[str]:
    return git("diff", "--cached", "--name-only", "--diff-filter=ACMR")


def tracked_paths() -> list[str]:
    return git("ls-files")


def read_text(path: str) -> str | None:
    try:
        with open(path, "rb") as handle:
            raw = handle.read(MAX_BYTES)
    except OSError:
        return None
    if b"\x00" in raw[:4096]:
        return None
    return raw.decode("utf-8", errors="replace")


def problems_for(path: str) -> list[str]:
    reasons: list[str] = []
    name = path.rsplit("/", 1)[-1]

    if FORBIDDEN_NAMES.match(name):
        reasons.append("is a submission scratch file")

    if path.count("/") == 0 and path.endswith(".json") and path not in ALLOWED_ROOT_JSON:
        reasons.append(
            "is a root-level .json that is not one of "
            + ", ".join(sorted(ALLOWED_ROOT_JSON))
        )

    if os.path.islink(path):
        reasons.append("is a symlink")

    text = read_text(path)
    if text is not None:
        exempt = path in SELF_REFERENTIAL
        for pattern, reason in SECRET_PATTERNS:
            if exempt and reason in KEYWORD_RULES:
                continue
            if pattern.search(text):
                reasons.append(reason)
    return reasons


def main(argv: list[str]) -> int:
    if "--staged" in argv:
        paths = staged_paths()
        scope = "staged"
    elif "--tree" in argv:
        paths = tracked_paths()
        scope = "tracked"
    elif "--paths" in argv:
        paths = argv[argv.index("--paths") + 1 :]
        scope = "given"
    else:
        print(__doc__)
        return 2

    failures: list[tuple[str, list[str]]] = []
    for path in paths:
        reasons = problems_for(path)
        if reasons:
            failures.append((path, reasons))

    if failures:
        print(f"Refusing {len(failures)} file(s) from the {scope} set:\n", file=sys.stderr)
        for path, reasons in failures:
            print(f"  {path}", file=sys.stderr)
            for reason in reasons:
                print(f"      - {reason}", file=sys.stderr)
        print(
            "\nScratch responses, tokens and one-off .json files belong outside the "
            "repository.\nSee AGENTS.md, rule 2.",
            file=sys.stderr,
        )
        return 1

    print(f"check_no_secrets: {len(paths)} {scope} file(s) clean")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
