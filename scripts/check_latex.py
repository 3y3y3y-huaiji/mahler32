#!/usr/bin/env python3
"""LaTeX source and build-log quality gate for companion papers.

Usage:
    python3 scripts/check_latex.py --source
    python3 scripts/check_latex.py --build papers/main
    python3 scripts/check_latex.py --check-bundle papers/main
"""

from __future__ import annotations

import argparse
import json
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
ABSTRACT_RE = re.compile(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.DOTALL)
PLAIN_TEXT_MACRO_RE = re.compile(
    r"\\(?:texttt|emph|textbf|textit|lean|fract|cite[pt]?|ref|eqref)\b"
    r"|\\['\"`^~=.uvHc](?:\{|[A-Za-z])"
)
TILDE_JOIN_RE = re.compile(r"(?<=\S)~(?=\S)")
DOUBLE_HYPHEN_RE = re.compile(r"(?<=[A-Za-z])--(?=[A-Za-z])")
MIN_PDF_BYTES = 1024


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


def strip_math_spans(text: str) -> str:
    """Blank out `$...$` and `\\(...\\)` inline math spans while preserving newlines."""
    chars = list(text)
    n = len(text)
    i = 0
    in_dollar = False
    in_paren = False
    while i < n:
        ch = text[i]
        if ch == "\\" and i + 1 < n:
            nxt = text[i + 1]
            if not in_dollar and not in_paren and nxt == "(":
                in_paren = True
                chars[i] = " "
                chars[i + 1] = " "
                i += 2
                continue
            if in_paren and nxt == ")":
                in_paren = False
                chars[i] = " "
                chars[i + 1] = " "
                i += 2
                continue
            if in_dollar or in_paren:
                chars[i] = " "
                if chars[i + 1] != "\n":
                    chars[i + 1] = " "
            i += 2
            continue
        if ch == "$" and not in_paren:
            if i + 1 < n and text[i + 1] == "$":
                chars[i] = " "
                chars[i + 1] = " "
                i += 2
                continue
            in_dollar = not in_dollar
            chars[i] = " "
            i += 1
            continue
        if (in_dollar or in_paren) and chars[i] != "\n":
            chars[i] = " "
        i += 1
    return "".join(chars)


def check_abstract_plain_text(tex_path: Path, clean: str) -> list[str]:
    """Ensure abstract body is clean for web metadata extraction (no text-level TeX macros)."""
    errors: list[str] = []
    match = ABSTRACT_RE.search(clean)
    if not match:
        return [f"{tex_path}: missing `\\begin{{abstract}}...\\end{{abstract}}` block"]
    abstract_raw = match.group(1)
    base_line = clean[: match.start()].count("\n") + 1
    if r"\fract{" in abstract_raw:
        errors.append(
            f"{tex_path}:{base_line}: custom macro `\\fract{{...}}` inside abstract "
            "(use standard `\\{{...\\}}`)"
        )
    prose_only = strip_math_spans(abstract_raw)
    for label, pattern in (
        ("text-level LaTeX macro or accent escape", PLAIN_TEXT_MACRO_RE),
        ("non-breaking tilde `~` outside math", TILDE_JOIN_RE),
        ("LaTeX double-hyphen `--` in prose word join", DOUBLE_HYPHEN_RE),
    ):
        found = pattern.search(prose_only)
        if found:
            line_no = base_line + prose_only[: found.start()].count("\n")
            errors.append(f"{tex_path}:{line_no}: {label} `{found.group(0)}` inside abstract")
    return errors


def check_metadata_plain_text() -> list[str]:
    """Ensure CITATION.cff and .zenodo.json are valid and free of raw LaTeX text escapes."""
    errors: list[str] = []
    cff_path = ROOT / "CITATION.cff"
    if cff_path.exists():
        cff_text = cff_path.read_text(encoding="utf-8")
        for i, line in enumerate(cff_text.splitlines(), 1):
            m = PLAIN_TEXT_MACRO_RE.search(line) or TILDE_JOIN_RE.search(line) or DOUBLE_HYPHEN_RE.search(line)
            if m:
                errors.append(f"{cff_path}:{i}: raw LaTeX escape/macro `{m.group(0)}` in CITATION.cff")

    zenodo_path = ROOT / ".zenodo.json"
    if zenodo_path.exists():
        try:
            data = json.loads(zenodo_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            errors.append(f"{zenodo_path}: invalid JSON: {exc}")
            return errors
        for field in ("title", "description"):
            val = data.get(field)
            if isinstance(val, str):
                m = PLAIN_TEXT_MACRO_RE.search(val) or TILDE_JOIN_RE.search(val) or DOUBLE_HYPHEN_RE.search(val)
                if m:
                    errors.append(
                        f"{zenodo_path}: raw LaTeX escape/macro `{m.group(0)}` in `.zenodo.json` field `{field}`"
                    )
    return errors


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

    # Abstract plain-text / aiXiv web compatibility check.
    errors.extend(check_abstract_plain_text(tex_path, clean))

    return errors


def check_pdf_artifact(pdf_path: Path) -> list[str]:
    """Verify compiled PDF artifact exists, is non-trivial, and begins with `%PDF-`."""
    if not pdf_path.exists():
        return [f"{pdf_path}: missing compiled PDF artifact (required for release/submission)"]
    size = pdf_path.stat().st_size
    if size < MIN_PDF_BYTES:
        return [f"{pdf_path}: PDF artifact too small ({size} bytes < {MIN_PDF_BYTES})"]
    with pdf_path.open("rb") as handle:
        header = handle.read(5)
    if header != b"%PDF-":
        return [f"{pdf_path}: invalid PDF header {header!r} (expected b'%PDF-')"]
    return []


def check_submission_bundle(bundle_dir: Path) -> list[str]:
    """Validate that a paper directory holds a complete, clean release/submission bundle."""
    errors: list[str] = []
    tex_path = bundle_dir / "main.tex"
    bib_path = bundle_dir / "refs.bib"
    pdf_path = bundle_dir / "main.pdf"
    if not tex_path.exists():
        errors.append(f"{tex_path}: missing main.tex")
    else:
        errors.extend(check_tex_source(tex_path))
    if not bib_path.exists():
        errors.append(f"{bib_path}: missing refs.bib")
    errors.extend(check_pdf_artifact(pdf_path))
    for stray in sorted(bundle_dir.glob("HANDOFF*.md")):
        errors.append(f"{stray}: stray handoff note inside submission directory")
    return errors


def check_build_dir(build_dir: Path, max_overfull_pt: float) -> list[str]:
    """Validate submission completeness plus compiled `.log` and `.blg` inside `build_dir`."""
    errors: list[str] = []
    if not (build_dir / "main.tex").exists():
        errors.append(f"{build_dir / 'main.tex'}: missing TeX entrypoint")
    if not (build_dir / "refs.bib").exists():
        errors.append(f"{build_dir / 'refs.bib'}: missing BibTeX file")
    errors.extend(check_pdf_artifact(build_dir / "main.pdf"))

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
        "--check-bundle",
        type=Path,
        default=None,
        help="Validate release/submission bundle completeness (main.tex + refs.bib + main.pdf).",
    )
    parser.add_argument(
        "--max-overfull-pt",
        type=float,
        default=5.0,
        help="Maximum allowed Overfull \\hbox width in pt (default: 5.0).",
    )
    args = parser.parse_args(argv)

    run_source = args.source or (args.build is None and args.check_bundle is None)
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
        meta_errors = check_metadata_plain_text()
        errors.extend(meta_errors)
        if not meta_errors:
            print("ok [meta]   CITATION.cff & .zenodo.json")

    if args.check_bundle is not None:
        bundle_errors = check_submission_bundle(args.check_bundle)
        errors.extend(bundle_errors)
        if not bundle_errors:
            print(f"ok [bundle] {args.check_bundle}")

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
