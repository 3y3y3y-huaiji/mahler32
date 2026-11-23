#!/usr/bin/env python3
"""Single-source-of-truth (SSOT) gate for this repository.

Zero third-party dependencies.  Exit status is strictly binary:

    0  every SSOT invariant holds
    1  at least one invariant is broken (the reason is printed)

The gate enforces four things, all mechanical:

1. **Toolchain.**  ``lean-toolchain`` is the only source of truth for the Lean
   version.  ``formalization.yaml`` and ``README.md`` must quote exactly that
   version (``vX.Y.Z``), so a toolchain bump cannot leave the self-report or
   the badge stale.
2. **Module inventory.**  Every ``Mahler32/*.lean`` module must be
       * import-reachable from ``Mahler32Core.lean`` (transitive imports count),
       * named in ``AuditAxioms.lean`` (the kernel-axiom audit),
       * named in ``SpecCheck.lean`` (the definition/statement lock), and
       * registered by path in ``README.md``.
   A new module that escapes any of the four is exactly the drift this gate
   exists to stop.
3. **Stale claims.**  A small blacklist of already-corrected mis-statements may
   not reappear in ``README.md`` or under ``papers/``.
4. **Links.**  Every repository-internal path named in ``README.md``,
   ``AGENTS.md`` or ``docs/`` must exist.

Usage::

    python3 scripts/verify_ssot.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Already-corrected mis-statements.  Matching is done on whitespace-stripped
# text, so spacing variants are caught too.  These are deliberately the exact
# claims that were false: the single-branch cage says nothing about the joint
# two-branch relation, and the constant 8/57 is a cup-map preimage, not a
# single-branch emptying threshold.
STALE_PHRASES = [
    "单分支清空否定8/57",
    "8/57单分支清空",
    "双分支3步清空",
    "[2/7,5/7)双分支3步清空",
    "two-branchempties[2/7,5/7)in3steps",
    "single-branchempties[2/7,5/7)",
]

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$")
VERSION_RE = re.compile(r":v?(\d+\.\d+\.\d+)\s*$")
PATH_TOKEN_RE = re.compile(
    r"^[A-Za-z0-9_.\-]+(?:/[A-Za-z0-9_.\-]+)*/?$"
)
FILE_SUFFIXES = (".lean", ".py", ".sh", ".yml", ".yaml", ".md", ".json", ".tex", ".bib", ".toml")
REPO_DIRS = ("Mahler32/", "Mahler32Conditional/", "docs/", "papers/", "scripts/", ".github/", ".githooks/")
EXTERNAL_DIRS = ("Mathlib/", "mathlib4/")
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
CODE_RE = re.compile(r"`([^`\n]+)`")
MATH_CHARS = set("^+\\${}=* \t")

failures: list[str] = []


def fail(message: str) -> None:
    failures.append(message)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as exc:  # noqa: BLE001 - report, do not crash
        fail(f"cannot read {path.relative_to(ROOT)}: {exc}")
        return ""


def toolchain_version() -> str | None:
    text = read_text(ROOT / "lean-toolchain").strip()
    match = VERSION_RE.search(text)
    if not match:
        fail(f"lean-toolchain is not a recognised pin: {text!r}")
        return None
    return "v" + match.group(1)


def check_versions(version: str) -> None:
    readme = read_text(ROOT / "README.md")
    if not re.search(rf"Lean[^\n]{{0,40}}{re.escape(version)}", readme):
        fail(f"README.md does not state `Lean {version}` (lean-toolchain source of truth)")
    if not re.search(rf"Mathlib[^\n]{{0,40}}{re.escape(version)}", readme):
        fail(f"README.md does not state Mathlib {version}")

    formalization = read_text(ROOT / "formalization.yaml")
    if f'lean: "{version}"' not in formalization:
        fail(f'formalization.yaml must contain `lean: "{version}"`')
    if f'mathlib: "{version}"' not in formalization:
        fail(f'formalization.yaml must contain `mathlib: "{version}"`')

    # No competing Lean pin may be advertised in the self-report.
    for other in set(re.findall(r"lean:\s*\"v(\d+\.\d+\.\d+)\"", formalization)):
        if other != version.lstrip("v"):
            fail(f"formalization.yaml advertises a second Lean version v{other}")


def module_name(path: Path) -> str:
    return "Mahler32." + path.stem


def imports_of(path: Path) -> set[str]:
    found: set[str] = set()
    for line in read_text(path).splitlines():
        match = IMPORT_RE.match(line)
        if match:
            found.add(match.group(1))
    return found


def reachable_modules() -> set[str]:
    graph: dict[str, set[str]] = {}
    for path in (ROOT / "Mahler32").glob("*.lean"):
        graph[module_name(path)] = imports_of(path)
    core = ROOT / "Mahler32Core.lean"
    graph["Mahler32Core"] = imports_of(core)

    seen: set[str] = set()
    stack = ["Mahler32Core"]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(graph.get(current, set()))
    return seen


def check_modules() -> None:
    audit = read_text(ROOT / "AuditAxioms.lean")
    spec = read_text(ROOT / "SpecCheck.lean")
    readme = read_text(ROOT / "README.md")
    formalization = read_text(ROOT / "formalization.yaml")
    reachable = reachable_modules()

    modules = sorted((ROOT / "Mahler32").glob("*.lean"))
    if not modules:
        fail("no Mahler32/*.lean modules found")
        return

    for path in modules:
        name = module_name(path)
        rel = f"Mahler32/{path.name}"
        if name not in reachable:
            fail(f"{rel} is not import-reachable from Mahler32Core.lean")
        if name not in audit:
            fail(f"{rel} is not audited in AuditAxioms.lean (expected `{name}`)")
        if name not in spec:
            fail(f"{rel} is not locked in SpecCheck.lean (expected `{name}`)")
        if rel not in readme:
            fail(f"{rel} is not registered in README.md")
        if rel not in formalization:
            fail(f"{rel} is not listed in formalization.yaml `modules:`")

    conditional = ROOT / "Mahler32Conditional" / "AlgebraicPairBranch.lean"
    if conditional.exists():
        if "Mahler32Conditional/AlgebraicPairBranch.lean" not in readme:
            fail(
                "Mahler32Conditional/AlgebraicPairBranch.lean is not described in README.md"
            )
        if "Mahler32Conditional/AlgebraicPairBranch.lean" not in formalization:
            fail(
                "Mahler32Conditional/AlgebraicPairBranch.lean is not listed in "
                "formalization.yaml `modules:`"
            )


def normalise(text: str) -> str:
    return re.sub(r"\s+", "", text)


def check_stale_phrases() -> None:
    targets = [ROOT / "README.md"]
    targets.extend(sorted((ROOT / "papers").rglob("*")))
    for path in targets:
        if not path.is_file() or path.suffix not in {".md", ".tex", ".bib", ".txt"}:
            continue
        text = normalise(read_text(path))
        for phrase in STALE_PHRASES:
            if normalise(phrase) in text:
                fail(f"stale claim {phrase!r} reappeared in {path.relative_to(ROOT)}")


def resolves(path: Path, doc_dir: Path) -> bool:
    if path.exists():
        return True
    candidate = doc_dir / path
    return candidate.exists()


def check_links() -> None:
    documents = [ROOT / "README.md", ROOT / "AGENTS.md"]
    documents.extend(sorted((ROOT / "docs").glob("*.md")))
    root_files = {p.name for p in ROOT.iterdir() if p.is_file()}

    for doc in documents:
        doc_dir = doc.parent
        text = read_text(doc)

        for target in LINK_RE.findall(text):
            target = target.strip().strip("<>").split()[0] if target.strip() else ""
            target = target.split("#", 1)[0]
            if not target or re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", target):
                continue
            # `$step^[k](x+2^k)$`-style mathematics is not a markdown link.
            if any(ch in MATH_CHARS for ch in target):
                continue
            if "/" not in target and "." not in target and target not in root_files:
                continue
            if not resolves(Path(target.lstrip("/")), doc_dir):
                fail(f"broken link in {doc.relative_to(ROOT)}: {target}")

        for token in CODE_RE.findall(text):
            token = token.strip().rstrip("/")
            if not token or not PATH_TOKEN_RE.match(token):
                continue
            if token in FILE_SUFFIXES:
                continue
            if token.startswith(".") and not token.startswith((".github/", ".githooks/")):
                continue
            if "/" not in token and token not in root_files:
                continue
            if token.startswith(EXTERNAL_DIRS):
                continue
            has_suffix = token.endswith(FILE_SUFFIXES)
            is_repo_dir = token.endswith(tuple(d.rstrip("/") for d in REPO_DIRS))
            if not has_suffix and not is_repo_dir:
                continue
            if not resolves(Path(token), doc_dir):
                fail(f"broken path in {doc.relative_to(ROOT)}: `{token}`")


def main() -> int:
    version = toolchain_version()
    if version is not None:
        check_versions(version)
    check_modules()
    check_stale_phrases()
    check_links()

    if failures:
        print("verify_ssot: FAILED", file=sys.stderr)
        for message in failures:
            print(f"  - {message}", file=sys.stderr)
        return 1

    print(
        f"verify_ssot: OK (Lean {version}; "
        f"{len(list((ROOT / 'Mahler32').glob('*.lean')))} core modules)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
