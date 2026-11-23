#!/usr/bin/env python3
"""Exact rational certificates for the Mahler 3/2 barrier families.

This script recomputes, in exact rational arithmetic (``fractions.Fraction``), the finite
certificates quoted in ``papers/paper2_zero_entropy_fluid``.  It never uses floating point for a
decision.

Run ``python3 scripts/generate_certificates.py`` to print the certificate table, or with
``--verify`` to assert every finite claim and exit non-zero on any mismatch.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F

Q = F  # readability alias for exact rationals


def normalise(intervals):
    """Sort and merge half-open rational intervals ``[a, b)``."""
    out: list[tuple[Q, Q]] = []
    for a, b in sorted(intervals):
        if a >= b:
            continue
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def intersect(u, v):
    return normalise(
        [
            (max(a, c), min(b, d))
            for a, b in u
            for c, d in v
            if max(a, c) < min(b, d)
        ]
    )


def preimage(intervals):
    """Exact preimage under ``T x = {3x/2}`` on ``[0, 1)``."""
    out: list[tuple[Q, Q]] = []
    for a, b in intervals:
        for shift in (Q(0), Q(1)):
            lo = max(Q(0), Q(2, 3) * (a + shift))
            hi = min(Q(1), Q(2, 3) * (b + shift))
            if lo < hi:
                out.append((lo, hi))
    return normalise(out)


def emptying_depth(u, max_depth=30):
    """Least ``n`` with ``{x : T^k x in u for 0 <= k <= n} == empty``; None if not reached."""
    cur = normalise(u)
    for n in range(max_depth + 1):
        if not cur:
            return n
        cur = intersect(u, preimage(cur))
    return None


def cup(x: Q) -> Q:
    y = Q(3, 2) * x
    return y if y < Q(1, 2) else y - Q(1, 2)


def dag_step(g: int) -> int:
    return (3 * g + g % 2) // 2


DAG_TARGET = {0, 4, 94, 120}
DAG_S7 = {
    0, 4, 10, 15, 23, 28, 35, 42, 50, 53, 56, 61, 63, 69, 75, 80,
    84, 85, 88, 92, 94, 95, 104, 113, 120, 126, 127,
}


def dag_depth(g: int):
    cur, seen = g % 128, set()
    for n in range(64):
        if cur in DAG_TARGET:
            return n
        if cur in seen:
            return None
        seen.add(cur)
        cur = dag_step(cur) % 128
    return None


BARRIERS = {
    "[2/7, 5/7)": [(Q(2, 7), Q(5, 7))],
    "[1/7, 3/7) u [4/7, 6/7)": [(Q(1, 7), Q(3, 7)), (Q(4, 7), Q(6, 7))],
    "[28/97, 69/97)": [(Q(28, 97), Q(69, 97))],
    "[5/24, 11/24) u [13/24, 19/24)": [(Q(5, 24), Q(11, 24)), (Q(13, 24), Q(19, 24))],
    "[1/5, 7/15) u [8/15, 4/5)": [(Q(1, 5), Q(7, 15)), (Q(8, 15), Q(4, 5))],
}

EXPECTED_DEPTH = {
    "[2/7, 5/7)": 3,
    "[1/7, 3/7) u [4/7, 6/7)": 5,
    "[28/97, 69/97)": 3,
    "[5/24, 11/24) u [13/24, 19/24)": 3,
    "[1/5, 7/15) u [8/15, 4/5)": 4,
}


def main(argv: list[str]) -> int:
    verify = "--verify" in argv
    failures: list[str] = []

    def check(ok: bool, label: str) -> None:
        print(("  ok   " if ok else "  FAIL ") + label)
        if not ok:
            failures.append(label)

    print("== cup map 4/19 three-cycle ==")
    cyc = (Q(4, 19), Q(6, 19), Q(9, 19))
    ok = cup(cyc[0]) == cyc[1] and cup(cyc[1]) == cyc[2] and cup(cyc[2]) == cyc[0]
    print("   4/19 ->", cup(Q(4, 19)), " 6/19 ->", cup(Q(6, 19)), " 9/19 ->", cup(Q(9, 19)))
    if verify:
        check(ok, "cup_cycle 4/19 -> 6/19 -> 9/19 -> 4/19")

    print("\n== barrier emptying depths (T x = {3x/2} on [0,1)) ==")
    for name, u in BARRIERS.items():
        d = emptying_depth(u)
        width = sum(b - a for a, b in u)
        print(f"   {name:34s} width={width}  emptying depth={d}")
        if verify:
            check(d == EXPECTED_DEPTH[name], f"{name}: emptying depth == {EXPECTED_DEPTH[name]}")

    print("\n== 8/57 threshold check (paper Remark 2/8) ==")
    d857 = emptying_depth([(Q(8, 57), Q(1, 2))])
    d757 = emptying_depth([(Q(7, 57), Q(1, 2))])
    print(f"   [8/57, 1/2) empties at depth {d857}")
    print(f"   [7/57, 1/2) empties at depth {d757}  (7/57 < 8/57)")
    print("   => 8/57 is not a critical threshold; the quoted claim is not asserted.")
    if verify:
        check(d857 is not None, "[8/57,1/2) empties")
        check(d757 is not None, "[7/57,1/2) also empties (8/57 not critical)")

    print("\n== widths ==")
    print("   [2/7,5/7) width =", Q(5, 7) - Q(2, 7))
    print("   holed width      =", (Q(3, 7) - Q(1, 7)) + (Q(6, 7) - Q(4, 7)))
    if verify:
        check(Q(5, 7) - Q(2, 7) == Q(3, 7), "width [2/7,5/7) == 3/7")
        check((Q(3, 7) - Q(1, 7)) + (Q(6, 7) - Q(4, 7)) == Q(4, 7), "holed width == 4/7")

    print("\n== DAG bounded gap (S7 exactness and g+128 carry) ==")
    hits = {g for g in range(128) if dag_depth(g) is not None and dag_depth(g) <= 11}
    max_depth = max((d for d in (dag_depth(g) for g in DAG_S7)), default=-1)
    carry_ok = all(dag_step(g + 128) == dag_step(g) + 192 for g in range(1000))
    print(f"   |S7|={len(DAG_S7)}  max depth in S7={max_depth}  hit<=11 set == S7: {hits == DAG_S7}")
    print(f"   dag_step(g+128) == dag_step(g)+192 for g<1000: {carry_ok}")
    if verify:
        check(hits == DAG_S7, "S7 is exactly the <=11 hitting set")
        check(max_depth <= 11, "all of S7 hits within 11 steps")
        check(carry_ok, "carry branch shift by 192")

    print()
    if verify:
        if failures:
            print(f"FAILED {len(failures)} check(s)")
            return 1
        print("all finite certificates verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
