#!/usr/bin/env python3
"""Classify the change set of a push/PR so CI can skip irrelevant heavy jobs.

Zero third-party dependencies.  Always exits 0: a classification failure is
reported conservatively as "Lean inputs changed" so the heavy build still runs.

Outputs (to ``$GITHUB_OUTPUT``, and to stdout when that is unset):

    lean=true|false      any Lean source / build input changed
    papers=true|false    any paper source changed
    docs_only=true|false only documentation changed (lean and papers false)
    changed=<n>          number of changed files

The diff is taken from the *latest* push when possible:

* ``pull_request`` / ``push``: ``github.event.before`` .. ``github.event.after``
* otherwise: the PR base .. head, or ``HEAD^`` .. ``HEAD``
"""

from __future__ import annotations

import fnmatch
import os
import subprocess
import sys
from pathlib import Path

LEAN_PATTERNS = (
    "*.lean",
    "lakefile.lean",
    "lean-toolchain",
    "lake-manifest.json",
    "comparator.json",
    "scripts/check_axioms.py",
    "scripts/generate_certificates.py",
    "scripts/verify_all.sh",
    ".github/workflows/lean_build.yml",
)
PAPERS_PATTERNS = (
    "papers/**",
    ".github/workflows/papers.yml",
)
DOCS_PATTERNS = (
    "README.md",
    "AGENTS.md",
    "SECURITY.md",
    "LICENSE*",
    "docs/**",
    ".github/ISSUE_TEMPLATE/**",
    ".github/PULL_REQUEST_TEMPLATE.md",
)


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def commit_exists(sha: str) -> bool:
    if not sha or set(sha) == {"0"}:
        return False
    try:
        subprocess.run(
            ["git", "cat-file", "-e", f"{sha}^{{commit}}"],
            check=True,
            capture_output=True,
        )
        return True
    except subprocess.CalledProcessError:
        return False


def changed_files() -> list[str] | None:
    event = os.environ.get("EVENT_NAME", "")
    before = os.environ.get("BEFORE_SHA", "")
    after = os.environ.get("AFTER_SHA", "")
    pr_base = os.environ.get("PR_BASE_SHA", "")
    pr_head = os.environ.get("PR_HEAD_SHA", "")

    if event == "workflow_dispatch":
        return None

    candidates: list[tuple[str, str]] = []
    if commit_exists(before) and commit_exists(after):
        candidates.append((before, after))
    if commit_exists(pr_base) and commit_exists(pr_head):
        candidates.append((pr_base, pr_head))
    candidates.append(("HEAD^", "HEAD"))

    for base, head in candidates:
        try:
            out = git("diff", "--name-only", "--no-renames", base, head)
        except subprocess.CalledProcessError:
            continue
        if out:
            return [line for line in out.splitlines() if line]
    return None


def matches(path: str, patterns: tuple[str, ...]) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in patterns)


def main() -> int:
    files = changed_files()

    if files is None:
        lean = papers = True
        docs_only = False
        count = 0
        print("classify: change set unknown; running every job")
    else:
        lean = any(matches(f, LEAN_PATTERNS) for f in files)
        papers = any(matches(f, PAPERS_PATTERNS) for f in files)
        docs_only = bool(files) and not lean and not papers and all(
            matches(f, DOCS_PATTERNS) for f in files
        )
        count = len(files)
        print(f"classify: {count} changed file(s); lean={lean} papers={papers}")
        for f in files:
            print(f"  {f}")

    outputs = {
        "lean": str(lean).lower(),
        "papers": str(papers).lower(),
        "docs_only": str(docs_only).lower(),
        "changed": str(count),
    }
    target = os.environ.get("GITHUB_OUTPUT")
    if target:
        with open(target, "a", encoding="utf-8") as handle:
            for key, value in outputs.items():
                handle.write(f"{key}={value}\n")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        lines = [f"- changed files: **{count}**",
                 f"- Lean inputs changed: **{lean}**",
                 f"- paper sources changed: **{papers}**",
                 f"- documentation only: **{docs_only}**"]
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write("### PR change classification\n\n" + "\n".join(lines) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
