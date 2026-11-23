#!/usr/bin/env bash
# End-to-end verification for the Mahler 3/2 repository.
#
#   ./scripts/verify_all.sh
#
# Steps, all of which must exit 0:
#   1. Lean build with warnings-as-errors
#   2. SpecCheck / SpecCheckConditional sealed-target check
#   3. kernel-axiom audit (zero-axiom core only)
#   4. exact rational certificates
#   5. secret / scratch-file guard
#   6. papers: compile when a TeX engine is available, otherwise structural check
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

echo "== [1/6] lake build -KwarningAsError=true =="
lake build -KwarningAsError=true

echo "== [2/6] sealed targets =="
lake build SpecCheck SpecCheckConditional

echo "== [3/6] kernel-only axiom audit =="
python3 scripts/check_axioms.py AuditAxioms.lean propext,Quot.sound,Classical.choice

echo "== [4/6] exact rational certificates =="
python3 scripts/generate_certificates.py --verify

echo "== [5/6] secret / scratch-file guard =="
python3 scripts/check_no_secrets.py --tree

echo "== [6/6] papers =="
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
for tex in pathlib.Path("papers").glob("*/main.tex"):
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
