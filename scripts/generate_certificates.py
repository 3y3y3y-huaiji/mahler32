#!/usr/bin/env python3
"""Exact rational certificates for the Mahler 3/2 double-branch system.

The map is presented through its two genuine branches on ``[0, 1)``

    T0 x = {3x/2},        T1 x = {3x/2 + 1/2},

with ``{·}`` the fractional part.  Everything below is decided in exact rational arithmetic
(``fractions.Fraction``); floating point is only ever printed, never used to decide a claim.

The script certifies three independent finite facts:

* the deterministic (forward ``T0``) emptying depths of the barrier families quoted in
  ``papers/paper2_zero_entropy_fluid`` -- the interval ``[2/7, 5/7)`` dies at depth ``3``, the holed
  ``4/7`` set at depth ``5``, etc.;
* the **double-branch cage**: for each barrier family ``U`` the least ``n`` for which the two-branch
  survivor ``U ∩ T0⁻¹(·) ∩ T1⁻¹(·)`` is empty, i.e. no ``x ∈ U`` keeps *both* branches confined to
  ``U`` for ``n`` steps.  For ``[2/7, 5/7)`` this is ``n = 1`` -- the Lean theorem
  ``cage_two_sevenths_double``; the holed ``4/7`` set needs ``n = 2``;
* the exact emptying-depth profile of the left family ``[δ, 1/2)`` as ``δ`` varies, reported
  without any threshold claim: the family empties for every ``δ > 0`` and only ``δ = 0`` survives.

Run ``python3 scripts/generate_certificates.py`` to print the table, or add ``--verify`` to assert
every finite claim and exit non-zero on any mismatch.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F

Q = F  # readability alias for exact rationals


# ---------------------------------------------------------------------------
# the two branches, written exactly as in Mahler32/ZeroEntropyCages.lean
# ---------------------------------------------------------------------------

def _frac(y: Q) -> Q:
    """Fractional part of a non-negative rational ``y``."""
    return y - (y.numerator // y.denominator)


def T0(x: Q) -> Q:
    """``{3x/2}`` (only used on ``[0, 1)``)."""
    y = Q(3, 2) * x
    return y - 1 if y >= 1 else y


def T1(x: Q) -> Q:
    """``{3x/2 + 1/2}`` (only used on ``[0, 1)``)."""
    y = Q(3, 2) * x + Q(1, 2)
    return y - 1 if y >= 1 else y


# ---------------------------------------------------------------------------
# exact interval arithmetic
# ---------------------------------------------------------------------------

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
        [(max(a, c), min(b, d)) for a, b in u for c, d in v if max(a, c) < min(b, d)]
    )


def union(u, v):
    return normalise(list(u) + list(v))


def preimage(intervals, branch):
    """Exact preimage of a half-open set under ``T0`` (``branch=0``) or ``T1`` (``branch=1``).

    For ``T0``: ``T0 x = y`` means ``3x/2 = y + k`` for ``k ∈ {0, 1}``, i.e. ``x = (2/3)(y + k)``.
    For ``T1``: ``T1 x = y`` means ``3x/2 + 1/2 = y + k``, i.e. ``x = (2/3)(y + k - 1/2)``.
    In both cases the result is clipped to ``[0, 1)``.
    """
    out: list[tuple[Q, Q]] = []
    offset = Q(0) if branch == 0 else Q(1, 2)
    for a, b in intervals:
        for k in (Q(0), Q(1)):
            lo = max(Q(0), Q(2, 3) * (a + k - offset))
            hi = min(Q(1), Q(2, 3) * (b + k - offset))
            if lo < hi:
                out.append((lo, hi))
    return normalise(out)


def deterministic_depth(u, max_depth=60):
    """Least ``n`` with ``{x : T0^k x ∈ u for 0 <= k <= n} == ∅`` (the forward Mahler map)."""
    cur = normalise(u)
    for n in range(max_depth + 1):
        if not cur:
            return n
        cur = intersect(u, preimage(cur, 0))
    return None


def double_branch_depth(u, max_depth=40):
    """Least ``n`` with the two-branch survivor ``U ∩ T0⁻¹(·) ∩ T1⁻¹(·)`` empty after ``n`` steps.

    Equivalently: the least ``n`` for which no ``x ∈ U`` has *both* branch iterates of length
    ``≤ n`` confined to ``U``.  ``n = 1`` is the one-step double-branch cage.
    """
    cur = normalise(u)
    for n in range(max_depth + 1):
        if not cur:
            return n
        cur = intersect(u, intersect(preimage(cur, 0), preimage(cur, 1)))
    return None


# ---------------------------------------------------------------------------
# separate bounded-gap automaton checks (task 12, unchanged)
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# data
# ---------------------------------------------------------------------------

BARRIERS = {
    "[2/7, 5/7)": [(Q(2, 7), Q(5, 7))],
    "[1/7, 3/7) u [4/7, 6/7)": [(Q(1, 7), Q(3, 7)), (Q(4, 7), Q(6, 7))],
    "[28/97, 69/97)": [(Q(28, 97), Q(69, 97))],
    "[5/24, 11/24) u [13/24, 19/24)": [(Q(5, 24), Q(11, 24)), (Q(13, 24), Q(19, 24))],
    "[1/5, 7/15) u [8/15, 4/5)": [(Q(1, 5), Q(7, 15)), (Q(8, 15), Q(4, 5))],
}

# deterministic (forward T0) emptying depths
EXPECTED_DEPTH = {
    "[2/7, 5/7)": 3,
    "[1/7, 3/7) u [4/7, 6/7)": 5,
    "[28/97, 69/97)": 3,
    "[5/24, 11/24) u [13/24, 19/24)": 3,
    "[1/5, 7/15) u [8/15, 4/5)": 4,
}

# double-branch (T0 and T1 both confined) emptying depths
EXPECTED_DOUBLE_DEPTH = {
    "[2/7, 5/7)": 1,
    "[1/7, 3/7) u [4/7, 6/7)": 2,
    "[28/97, 69/97)": 1,
    "[5/24, 11/24) u [13/24, 19/24)": 1,
    "[1/5, 7/15) u [8/15, 4/5)": 1,
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

    print("\n== deterministic emptying depths (forward branch T0 x = {3x/2}) ==")
    for name, u in BARRIERS.items():
        d = deterministic_depth(u)
        width = sum(b - a for a, b in u)
        print(f"   {name:34s} width={width}  emptying depth={d}")
        if verify:
            check(d == EXPECTED_DEPTH[name], f"{name}: emptying depth == {EXPECTED_DEPTH[name]}")

    print("\n== double-branch cage: least n with U ∩ T0⁻¹(·) ∩ T1⁻¹(·) empty ==")
    for name, u in BARRIERS.items():
        d = double_branch_depth(u)
        print(f"   {name:34s} double-branch emptying depth={d}")
        if verify:
            check(d == EXPECTED_DOUBLE_DEPTH[name],
                  f"{name}: double-branch emptying depth == {EXPECTED_DOUBLE_DEPTH[name]}")

    print("\n== exact δ-profile of the left family [δ, 1/2) (forward T0) ==")
    print("   δ = 0 survives (the fixed point 0); every δ > 0 empties, with these least depths:")
    profile = {}
    for num in range(0, 20):
        delta = Q(num, 57)
        d = deterministic_depth([(delta, Q(1, 2))])
        profile[num] = d
        tag = "survives" if d is None else f"depth {d}"
        print(f"   [δ={num:2d}/57, 1/2)  {tag}")
    if verify:
        check(profile[0] is None, "delta = 0 survives ([0,1/2) contains the fixed point 0)")
        check(all(profile[n] is not None for n in range(1, 20)),
              "every delta = k/57, k >= 1, empties")
        check(profile[8] == 4 and profile[9] == 3,
              "depth drops from 4 to 3 between 8/57 and 9/57 (8/57 is not a threshold)")

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
