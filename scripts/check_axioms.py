#!/usr/bin/env python3
"""Kernel-axiom audit for a Lean file full of `#print axioms` commands.

Usage:
    python3 scripts/check_axioms.py AUDIT.lean propext,Quot.sound,Classical.choice

The script elabourates the audit file with `lake env lean`, then parses lines of the form

    'Mahler32.foo' depends on axioms: [propext, Quot.sound]
    'Mahler32.bar' does not depend on any axioms

and fails if

* a reported declaration depends on an axiom outside the whitelist (in particular
  `sorryAx`), or
* no `#print axioms` line was produced at all, or
* Lean itself exited non-zero.

This makes it impossible for a new module to be smuggled into the build while escaping the
axiom audit: the audit file lists *every* main theorem and the whitelist is explicit.
"""
from __future__ import annotations

import re
import subprocess
import sys

LINE = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    re.DOTALL,
)


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    audit_file = sys.argv[1]
    allowed = {a.strip() for a in sys.argv[2].split(",") if a.strip()}

    proc = subprocess.run(
        ["lake", "env", "lean", audit_file],
        capture_output=True,
        text=True,
    )
    output = proc.stdout + proc.stderr
    print(output, end="")

    if proc.returncode != 0:
        print(f"\nERROR: `lake env lean {audit_file}` failed", file=sys.stderr)
        return 1

    if "sorryAx" in output:
        print("\nERROR: a declaration depends on sorryAx", file=sys.stderr)
        return 1

    seen = 0
    failed = False
    # `#print axioms` pretty-prints long axiom lists across several lines, so match over the
    # whole output rather than line by line.
    for m in LINE.finditer(output):
        seen += 1
        name = m.group(1)
        axioms = m.group(2)
        used = {a.strip() for a in axioms.split(",") if a.strip()} if axioms else set()
        extra = used - allowed
        if extra:
            print(f"ERROR: {name} depends on disallowed axioms: {sorted(extra)}", file=sys.stderr)
            failed = True

    if seen == 0:
        print("\nERROR: no `#print axioms` output was parsed", file=sys.stderr)
        return 1
    if failed:
        return 1

    print(f"\nOK: {seen} declarations checked; axioms within {{{', '.join(sorted(allowed))}}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
