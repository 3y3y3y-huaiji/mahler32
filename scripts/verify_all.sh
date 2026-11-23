#!/usr/bin/env bash
# End-to-end verification for the Mahler 3/2 repository.
#
#   ./scripts/verify_all.sh
#
# This script mirrors `.github/workflows/lean_build.yml` (plus `guards.yml`) step
# for step, so "green locally" and "green in CI" mean the same thing.  Every step
# must exit 0.
set -euo pipefail

cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  if [ -x "$HOME/.elan/bin/lake" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
  else
    echo "error: lake not found (install elan: https://github.com/leanprover/elan)" >&2
    exit 1
  fi
fi

echo "== [1/12] secret / scratch-file guard =="
python3 scripts/check_no_secrets.py --tree

echo "== [2/12] SSOT gate (toolchain, inventory, stale claims, links) =="
python3 scripts/verify_ssot.py

echo "== [3/12] core source gate (no sorry/admit/native_decide/axiom) =="
python3 - <<'PY'
import pathlib, re, sys

def strip_comments(s: str) -> str:
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)   # block / doc comments
    s = re.sub(r"--[^\n]*", "", s)              # line comments
    return s

core = sorted(pathlib.Path("Mahler32").glob("*.lean")) + [pathlib.Path("Mahler32Core.lean")]
bad = False
for f in core:
    text = strip_comments(f.read_text())
    for kw in ("sorry", "admit", "native_decide"):
        for m in re.finditer(r"\b" + kw + r"\b", text):
            line = text[: m.start()].count("\n") + 1
            print(f"error file={f},line={line}: forbidden `{kw}` in core module")
            bad = True
    if re.search(r"^\s*(private\s+|protected\s+|noncomputable\s+)*axiom\b", text, re.M):
        print(f"error file={f}: core modules must not declare axioms")
        bad = True

leak_scan = core + [pathlib.Path("Solution.lean")]
for f in leak_scan:
    if "schlickewei_subspace_Q3" in f.read_text():
        print(f"error file={f}: the conditional axiom leaked into the zero-axiom core")
        bad = True
sys.exit(1 if bad else 0)
PY

echo "== [4/12] lake build -KwarningAsError=true =="
lake build -KwarningAsError=true

echo "== [5/12] Palomar targets (Solution, Challenge) =="
lake build Solution
lake build Challenge

echo "== [6/12] conditional target =="
lake build Mahler32Conditional

echo "== [7/12] strict per-module verification =="
status=0
for f in Mahler32Core.lean Mahler32.lean AuditAxioms.lean AuditAxiomsConditional.lean \
         Mahler32/*.lean Mahler32Conditional/*.lean; do
  echo "   lake env lean -D warningAsError=true $f"
  lake env lean -D warningAsError=true "$f" || status=1
done
[ "$status" -eq 0 ] || exit 1

echo "== [8/12] #lint over the whole zero-axiom core =="
LINT_FILE=$(mktemp --suffix=.lean)
printf 'import Mahler32Core\n\n#lint\n' > "$LINT_FILE"
lake env lean "$LINT_FILE"
rm -f "$LINT_FILE"

echo "== [9/12] kernel-axiom audits =="
python3 scripts/check_axioms.py AuditAxioms.lean propext,Quot.sound,Classical.choice
python3 scripts/check_axioms.py \
  AuditAxiomsConditional.lean \
  propext,Quot.sound,Classical.choice,Mahler32Conditional.schlickewei_subspace_Q3

echo "== [10/12] SpecCheck locks =="
lake env lean -D warningAsError=true SpecCheck.lean
lake env lean -D warningAsError=true SpecCheckConditional.lean

echo "== [11/12] exact rational certificates (verify + reproducibility) =="
python3 scripts/generate_certificates.py --verify
python3 scripts/generate_certificates.py > /tmp/mahler32-cert-a.txt
python3 scripts/generate_certificates.py > /tmp/mahler32-cert-b.txt
diff -u /tmp/mahler32-cert-a.txt /tmp/mahler32-cert-b.txt

echo "== [12/12] workflows and papers =="
if command -v actionlint >/dev/null 2>&1; then
  actionlint -color
else
  echo "   actionlint not found; skipping workflow lint (CI installs v1.7.9)"
fi

if command -v latexmk >/dev/null 2>&1; then
  for d in papers/*/; do
    ( cd "$d" && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex && latexmk -c )
  done
elif command -v pdflatex >/dev/null 2>&1; then
  for d in papers/*/; do
    ( cd "$d" && pdflatex -interaction=nonstopmode -halt-on-error main.tex \
        && (bibtex main || true) \
        && pdflatex -interaction=nonstopmode -halt-on-error main.tex \
        && pdflatex -interaction=nonstopmode -halt-on-error main.tex )
  done
else
  echo "   no TeX engine found; running structural check only"
  python3 - <<'PY'
import pathlib, re, sys
bad = False
for tex in sorted(pathlib.Path("papers").glob("*/main.tex")):
    text = tex.read_text()
    envs = re.findall(r"\\(begin|end)\{([^}]+)\}", text)
    stack = []
    for kind, name in envs:
        if kind == "begin":
            stack.append(name)
        else:
            if not stack or stack[-1] != name:
                print(f"   {tex}: environment mismatch at \\end{{{name}}}")
                bad = True
                break
            stack.pop()
    if stack:
        print(f"   {tex}: unclosed environments {stack}")
        bad = True
    if text.count("{") != text.count("}"):
        print(f"   {tex}: unbalanced braces")
        bad = True
    if not bad:
        print(f"   ok {tex}")
sys.exit(1 if bad else 0)
PY
fi

echo
echo "verify_all: all gates passed"
