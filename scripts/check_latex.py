#!/usr/bin/env python3
"""LaTeX source and build-log quality gate for companion papers.

Usage:
    python3 scripts/check_latex.py --source
    python3 scripts/check_latex.py --build papers/main
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "papers"

UNICODE_MATH_CHARS = set("→↦↔≤≥≠≡∤∈∪∩ℤℚℕℝ⌈⌉⌊⌋±×·")
COLLOQUIAL_RE = re.compile(
    r"\b(?:Two-World|two-world|Anti-Misfire|anti-misfire|Misfire|misfire|Ghost|ghost|Cage|cage)\b"
    r"|双世界|防哑火|防误射|幽灵|牢笼|团灭|秒杀|血条"
)
ENV_RE = re.compile(r"\\(begin|end)\{([^}]+)\}")
HEADING_RE = re.compile(r"\\(?:title|section|subsection|subsubsection|paragraph)\*?\{")
CITE_RE = re.compile(r"\\cite[pt]?\*?(?:\[[^\]]*\])*\{([^}]+)\}")
BIB_KEY_RE = re.compile(r"@\w+\s*\{\s*([^,\s]+)\s*,")
OVERFULL_RE = re.compile(r"Overfull \\hbox \(([0-9]+(?:\.[0-9]+)?)pt too wide\)")


def strip_tex_comments(text: str) -> str:
    """Remove TeX comments while preserving literal escaped `\\%`."""
    out_lines: list[str] = []
    for line in text.splitlines():
        cleaned: list[str] = []
        i = 0
        while i < len(line):
            ch = line[i]
            if ch == "\\" and i + 1 < len(line):
                cleaned.append(line[i : i + 2])
                i += 2
                continue
            if ch == "%":
                break
            cleaned.append(ch)
            i += 1
        out_lines.append("".join(cleaned))
    return "\n".join(out_lines)


def extract_braced(text: str, open_brace_idx: int) -> tuple[str, int]:
    """Return content inside `{...}` starting at `open_brace_idx` and the closing index."""
    depth = 0
    i = open_brace_idx
    while i < len(text):
        ch = text[i]
        if ch == "\\" and i + 1 < len(text):
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[open_brace_idx + 1 : i], i
        i += 1
    return text[open_brace_idx + 1 :], len(text) - 1


def strip_protected_spans(text: str) -> str:
    """Blank out `\\lean{...}`, `\\texttt{...}`, `\\nolinkurl{...}`, `\\label{...}`, `\\cite{...}`."""
    protected_cmds = re.compile(
        r"\\(?:lean|texttt|nolinkurl|url|label|ref|eqref|pageref|autoref|cite[pt]?\*?)\*?"
        r"(?:\[[^\]]*\])*\{",
    )
    chars = list(text)
    for match in protected_cmds.finditer(text):
        start = match.start()
        brace_idx = match.end() - 1
        _, end_idx = extract_braced(text, brace_idx)
        for j in range(start, end_idx + 1):
            if chars[j] != "\n":
                chars[j] = " "
    return "".join(chars)


def check_bib_file(bib_path: Path) -> tuple[set[str], list[str]]:
    """Parse citation keys and validate BibTeX metadata."""
    errors: list[str] = []
    if not bib_path.exists():
        return set(), [f"{bib_path}: missing BibTeX file"]
    text = bib_path.read_text(encoding="utf-8")
    keys = set(BIB_KEY_RE.findall(text))
    for i, line in enumerate(text.splitlines(), 1):
        if re.search(r"\byear\s*=\s*\{\s*\}", line, re.IGNORECASE):
            errors.append(f"{bib_path}:{i}: empty `year` field in BibTeX entry")
    return keys, errors


def check_tex_source(tex_path: Path) -> list[str]:
    """Validate a single `main.tex` source file and its sibling `refs.bib`."""
    errors: list[str] = []
    raw = tex_path.read_text(encoding="utf-8")
    clean = strip_tex_comments(raw)

    for required in (r"\documentclass", r"\begin{document}", r"\end{document}", r"\maketitle"):
        if required not in clean:
            errors.append(f"{tex_path}: missing required `{required}`")

    # Environment and brace balance.
    stack: list[str] = []
    for kind, env_name in ENV_RE.findall(clean):
        if kind == "begin":
            stack.append(env_name)
        elif not stack or stack[-1] != env_name:
            errors.append(f"{tex_path}: mismatched `\\end{{{env_name}}}`")
            break
        else:
            stack.pop()
    else:
        if stack:
            errors.append(f"{tex_path}: unclosed environment(s) {stack}")

    unescaped = re.sub(r"\\[{}]", "", clean)
    if unescaped.count("{") != unescaped.count("}"):
        errors.append(f"{tex_path}: unbalanced curly braces")

    # Per-line source checks.
    for i, line in enumerate(clean.splitlines(), 1):
        if re.search(r"`[^`\n]+`", line):
            errors.append(f"{tex_path}:{i}: markdown backtick syntax in LaTeX source")
        if re.search(r"\\begin\{(?:table|figure)\}\[h\]", line):
            errors.append(f"{tex_path}:{i}: bare `[h]` float placement (use `[htbp]`)")
        bad_chars = sorted(set(line) & UNICODE_MATH_CHARS)
        if bad_chars:
            errors.append(f"{tex_path}:{i}: raw Unicode math character(s) {bad_chars}")

    # Headings / title must wrap `$...$` in `\texorpdfstring`.
    for match in HEADING_RE.finditer(clean):
        arg, _ = extract_braced(clean, match.end() - 1)
        arg_chars = list(arg)
        for tm in re.finditer(r"\\texorpdfstring\{", arg):
            _, end1 = extract_braced(arg, tm.end() - 1)
            for j in range(tm.start(), end1 + 1):
                if arg_chars[j] != "\n":
                    arg_chars[j] = " "
        if "$" in "".join(arg_chars):
            line_no = clean[: match.start()].count("\n") + 1
            errors.append(
                f"{tex_path}:{line_no}: math `$` in heading/title without `\\texorpdfstring`"
            )

    # Colloquial terminology check outside protected `\lean{}` / `\texttt{}` spans.
    prose_only = strip_protected_spans(clean)
    for i, line in enumerate(prose_only.splitlines(), 1):
        m = COLLOQUIAL_RE.search(line)
        if m:
            errors.append(
                f"{tex_path}:{i}: colloquial term `{m.group(0)}` outside code/Lean identifier"
            )

    # Citation keys exist in `refs.bib`.
    bib_keys, bib_errors = check_bib_file(tex_path.parent / "refs.bib")
    errors.extend(bib_errors)
    for match in CITE_RE.finditer(clean):
        for key in match.group(1).split(","):
            key_s = key.strip()
            if key_s and key_s not in bib_keys:
                line_no = clean[: match.start()].count("\n") + 1
                errors.append(f"{tex_path}:{line_no}: citation key `{key_s}` missing in refs.bib")

    return errors


def check_build_dir(build_dir: Path, max_overfull_pt: float) -> list[str]:
    """Validate compiled `.log` and `.blg` diagnostics inside `build_dir`."""
    errors: list[str] = []
    log_path = build_dir / "main.log"
    blg_path = build_dir / "main.blg"

    if not log_path.exists():
        return [f"{log_path}: compiled TeX log not found"]

    log_text = log_path.read_text(encoding="utf-8", errors="replace")
    bad_log_patterns = (
        (r"^! ", "TeX compilation error"),
        (r"LaTeX Error:", "LaTeX Error in log"),
        (r"There were undefined references", "undefined cross-references"),
        (r"There were undefined citations", "undefined citations"),
        (r"LaTeX Warning: Reference `[^']+' on page", "undefined reference"),
        (r"Package natbib Warning: Citation `[^']+'", "undefined natbib citation"),
        (r"Package hyperref Warning: Token not allowed in a PDF string", "hyperref PDF-string warning"),
        (r"LaTeX Warning: `h' float specifier changed to `ht'", "float specifier `[h]` warning"),
        (r"Missing character:", "missing character glyph warning"),
    )
    for pat, label in bad_log_patterns:
        for m in re.finditer(pat, log_text, re.MULTILINE):
            line_no = log_text[: m.start()].count("\n") + 1
            errors.append(f"{log_path}:{line_no}: {label}: {m.group(0)}")

    for m in OVERFULL_RE.finditer(log_text):
        pt = float(m.group(1))
        if pt > max_overfull_pt:
            line_no = log_text[: m.start()].count("\n") + 1
            errors.append(
                f"{log_path}:{line_no}: Overfull \\hbox ({pt:.2f}pt > {max_overfull_pt:.1f}pt)"
            )

    if blg_path.exists():
        blg_text = blg_path.read_text(encoding="utf-8", errors="replace")
        for pat, label in (
            (r"^Warning--", "BibTeX warning"),
            (r"I couldn't", "BibTeX missing entry/file"),
            (r"There (?:was|were) \d+ error", "BibTeX error"),
        ):
            for m in re.finditer(pat, blg_text, re.MULTILINE):
                line_no = blg_text[: m.start()].count("\n") + 1
                errors.append(f"{blg_path}:{line_no}: {label}: {m.group(0)}")

    return errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="LaTeX source and build-log quality gate.")
    parser.add_argument(
        "--source",
        action="store_true",
        help="Validate LaTeX/BibTeX sources under papers/*/main.tex.",
    )
    parser.add_argument(
        "--build",
        type=Path,
        default=None,
        help="Validate compiled main.log/main.blg inside the given paper build directory.",
    )
    parser.add_argument(
        "--max-overfull-pt",
        type=float,
        default=5.0,
        help="Maximum allowed Overfull \\hbox width in pt (default: 5.0).",
    )
    args = parser.parse_args(argv)

    run_source = args.source or args.build is None
    errors: list[str] = []

    if run_source:
        tex_files = sorted(PAPERS_DIR.glob("*/main.tex"))
        if not tex_files:
            errors.append(f"No papers/*/main.tex files found under {PAPERS_DIR}")
        for tex in tex_files:
            file_errors = check_tex_source(tex)
            errors.extend(file_errors)
            if not file_errors:
                print(f"ok [source] {tex.relative_to(ROOT)}")

    if args.build is not None:
        build_errors = check_build_dir(args.build, args.max_overfull_pt)
        errors.extend(build_errors)
        if not build_errors:
            print(f"ok [build]  {args.build}")

    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
