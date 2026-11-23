#!/usr/bin/env python3
"""Exact rational / integer certificates for the Mahler ``3/2`` barrier families
and for the ``9/4`` finite-roof model.

This script recomputes, in exact arithmetic (``fractions.Fraction`` and Python
``int``), the finite certificates quoted in ``papers/paper2_zero_entropy_fluid``.
It never uses floating point for a decision.

Two independent blocks:

* **Circle-map barriers.**  The Mahler map ``T x = {3x/2}`` on ``[0, 1)`` has two
  monotone (inverse) branches, the *even* branch ``T0`` and the *odd* branch
  ``T1``.  The exact preimage refinement is run for each branch separately; the
  barrier sets empty at the same finite depth under both branches, which is the
  machine-independent half of ``Mahler32/ZeroEntropyCages.lean``.

* **``9/4`` finite-roof model.**  The integer model ``4 g_{k+1} = 9 g_k + d_k``,
  ``d_k in {2, 3}``, together with its mirror involution, its even-rung
  annihilation, the independent difference/sum shadow maps, and the finite
  mirror-block counting bounds.  These are the script half of
  ``Mahler32/Model94Obstructions.lean``; the Lean module proves the general
  statements, this script re-checks concrete instances.

Run ``python3 scripts/generate_certificates.py`` to print the certificate table,
or with ``--verify`` to assert every finite claim and exit non-zero on any
mismatch.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F

Q = F  # readability alias for exact rationals


# ---------------------------------------------------------------------------
# half-open rational interval arithmetic
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
        [
            (max(a, c), min(b, d))
            for a, b in u
            for c, d in v
            if max(a, c) < min(b, d)
        ]
    )


def preimage(intervals, branch=0):
    """Exact preimage of ``intervals`` under **one** monotone branch.

    ``branch = 0``  is the even branch ``T0 x = {3x/2}``:  the two inverse lifts
    ``x = (2/3)(y + shift)`` for ``shift in {0, 1}``.

    ``branch = 1``  is the odd branch ``T1 x = {3x/2 + 1/2}``:  the inverse lifts
    ``x = (2/3)(y + k - 1/2)`` for the admissible integers ``k``.

    Passing the branch explicitly is the fix for the original single-branch bug:
    the barrier depths below are checked **for each branch**, not just for the
    even one.
    """
    out: list[tuple[Q, Q]] = []
    if branch == 0:
        for a, b in intervals:
            for shift in (Q(0), Q(1)):
                lo = max(Q(0), Q(2, 3) * (a + shift))
                hi = min(Q(1), Q(2, 3) * (b + shift))
                if lo < hi:
                    out.append((lo, hi))
    elif branch == 1:
        for a, b in intervals:
            for k in (Q(0), Q(1)):
                lo = max(Q(0), Q(2, 3) * (a - Q(1, 2) + k))
                hi = min(Q(1), Q(2, 3) * (b - Q(1, 2) + k))
                if lo < hi:
                    out.append((lo, hi))
    else:  # pragma: no cover - defensive
        raise ValueError(f"unknown branch {branch!r}")
    return normalise(out)


def emptying_depth(u, branch=0, max_depth=30):
    """Least ``n`` with ``{x : T_branch^k x in u for 0 <= k <= n} == empty``."""
    cur = normalise(u)
    for n in range(max_depth + 1):
        if not cur:
            return n
        cur = intersect(u, preimage(cur, branch))
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


# ---------------------------------------------------------------------------
# the 9/4 finite-roof model
# ---------------------------------------------------------------------------

def step94(g: int):
    """One step of ``4 g_{k+1} = 9 g_k + d_k`` with ``d_k in {2, 3}``.

    Only ``g % 4 in {1, 2}`` survives; ``1 -> +3`` and ``2 -> +2``.
    """
    m = g % 4
    if m == 1:
        return (9 * g + 3) // 4
    if m == 2:
        return (9 * g + 2) // 4
    return None


def iter94(k: int, g: int):
    for _ in range(k):
        g = step94(g)
        if g is None:
            return None
    return g


def survives94(k: int, g: int) -> bool:
    return iter94(k, g) is not None


def step_diff(d: int):
    """Difference shadow ``Delta``: ``d = g - g'``; ``2`` is impossible."""
    m = d % 4
    if m == 0:
        return 9 * d // 4
    if m == 1:
        return (9 * d - 1) // 4
    if m == 3:
        return (9 * d + 1) // 4
    return None


def step_sum(s: int):
    """Sum shadow ``S``: ``s = g + g'``; ``1`` is impossible."""
    m = s % 4
    if m == 0:
        return (9 * s + 4) // 4
    if m == 2:
        return (9 * s + 6) // 4
    if m == 3:
        return (9 * s + 5) // 4
    return None


def iter_shadow(f, k: int, x: int):
    for _ in range(k):
        x = f(x)
        if x is None:
            return None
    return x


def check_mirror_conservation(n_max=5):
    """Theorem 1: ``g_k + g̃_k = 9^k 4^{N-k} - 1``."""
    for N in range(1, n_max + 1):
        M = 4 ** N
        for g0 in range(M):
            mir = M - 1 - g0
            for k in range(N + 1):
                gk = iter94(k, g0)
                if gk is not None:
                    gt = iter94(k, mir)
                    if gt is None or gk + gt != 9 ** k * 4 ** (N - k) - 1:
                        return False
    return True


def check_even_annihilation(n_max=6):
    """Theorem 2: even rungs cannot have both mirror twins survive ``N + 2``."""
    for N in range(2, n_max + 1, 2):
        M = 4 ** N
        for g0 in range(M):
            mir = M - 1 - g0
            if survives94(N + 2, g0) and survives94(N + 2, mir):
                return False
    return True


def survivor_counts(N: int, extra: int):
    """``|S_N|`` and ``|S_{N+extra}|`` inside ``[0, 4^N)``."""
    M = 4 ** N
    sN = sum(1 for g in range(M) if survives94(N, g))
    sNe = sum(1 for g in range(M) if survives94(N + extra, g))
    return sN, sNe


def check_forbidden_sum(c_max=18, k_max=4):
    """Theorem 3: ``g0 + g0' = c 4^k - 1`` with ``c = 2 mod 4`` never both survive."""
    for c in range(2, c_max + 1, 4):
        for k in range(k_max + 1):
            total = c * 4 ** k - 1
            for g0 in range(total + 1):
                g1 = total - g0
                if survives94(k + 1, g0) and survives94(k + 1, g1):
                    return False
    return True


def check_shadow_maps(n_max=4, bound=250):
    """Theorem 5: the difference and sum shadows reproduce the pair dynamics."""
    for N in range(1, n_max + 1):
        for g0 in range(min(4 ** N, bound)):
            for g1 in range(g0 + 1):
                for k in range(N + 1):
                    gk = iter94(k, g0)
                    gk1 = iter94(k, g1)
                    if gk is not None and gk1 is not None:
                        if iter_shadow(step_diff, k, g0 - g1) != gk - gk1:
                            return False
                        if iter_shadow(step_sum, k, g0 + g1) != gk + gk1:
                            return False
    return True


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

    print("\n== barrier emptying depths, both monotone branches ==")
    print("   (T0 x = {3x/2} even branch, T1 x = {3x/2 + 1/2} odd branch)")
    for name, u in BARRIERS.items():
        d0 = emptying_depth(u, 0)
        d1 = emptying_depth(u, 1)
        width = sum(b - a for a, b in u)
        print(f"   {name:34s} width={width}  depth(T0)={d0}  depth(T1)={d1}")
        if verify:
            check(d0 == EXPECTED_DEPTH[name], f"{name}: T0 emptying depth == {EXPECTED_DEPTH[name]}")
            check(d1 == EXPECTED_DEPTH[name], f"{name}: T1 emptying depth == {EXPECTED_DEPTH[name]}")

    print("\n== 8/57 is a preimage boundary of the cup cycle, not an emptying threshold ==")
    # 8/57 = T0^{-1}(4/19) = (2/3) * (4/19): an exact preimage of the periodic point.
    pre_419 = Q(2, 3) * Q(4, 19)
    d857_0 = emptying_depth([(Q(8, 57), Q(1, 2))], 0)
    d757_0 = emptying_depth([(Q(7, 57), Q(1, 2))], 0)
    d857_1 = emptying_depth([(Q(8, 57), Q(1, 2))], 1)
    print(f"   T0^{{-1}}(4/19) = (2/3)(4/19) = {pre_419}   (= 8/57: {pre_419 == Q(8, 57)})")
    print(f"   [8/57, 1/2) empties at depth(T0)={d857_0}, depth(T1)={d857_1}")
    print(f"   [7/57, 1/2) empties at depth(T0)={d757_0}  (7/57 < 8/57)")
    print("   => 8/57 is an exact preimage of the 4/19 cycle, but it is *not* a critical")
    print("      emptying threshold: the left-hole family empties for every delta > 0 tested.")
    if verify:
        check(pre_419 == Q(8, 57), "8/57 == (2/3)(4/19), a preimage of the cup cycle")
        check(d857_0 is not None and d857_1 is not None, "[8/57,1/2) empties on both branches")
        check(d757_0 is not None, "[7/57,1/2) also empties (8/57 not a critical depth)")

    print("\n== widths ==")
    print("   [2/7,5/7) width =", Q(5, 7) - Q(2, 7))
    print("   holed width      =", (Q(3, 7) - Q(1, 7)) + (Q(6, 7) - Q(4, 7)))
    if verify:
        check(Q(5, 7) - Q(2, 7) == Q(3, 7), "width [2/7,5/7) == 3/7")
        check((Q(3, 7) - Q(1, 7)) + (Q(6, 7) - Q(4, 7)) == Q(4, 7), "holed width == 4/7")

    print("\n== 9/4 model: mirror conservation (Theorem 1) ==")
    t1 = check_mirror_conservation()
    print(f"   g_k + g~_k == 9^k 4^(N-k) - 1 for all N <= 5: {t1}")
    if verify:
        check(t1, "mirror conservation 9^k 4^(N-k) - 1")

    print("\n== 9/4 model: even-rung mirror annihilation (Theorem 2) ==")
    t2 = check_even_annihilation()
    print(f"   no even rung N <= 6 lets both twins survive N+2: {t2}")
    if verify:
        check(t2, "even-rung mirror annihilation")

    print("\n== 9/4 model: |S_N| = 2^N and the 3/8 roof (Theorem 7) ==")
    counts_ok = True
    roof_ok = True
    for N in range(2, 9):
        sN, sNe = survivor_counts(N, 2)
        counts_ok &= (sN == 2 ** N)
        roof_ok &= (8 * sNe <= 3 * sN)
        print(f"   N={N}: |S_N|={sN} (=2^{N}: {sN == 2 ** N})  "
              f"|S_(N+2)|={sNe}  8|S_(N+2)|<=3|S_N|: {8 * sNe <= 3 * sN}")
    if verify:
        check(counts_ok, "|S_N| == 2^N for N in 2..8")
        check(roof_ok, "finite-roof bound 8|S_(N+2)| <= 3|S_N| for N in 2..8")

    print("\n== 9/4 model: forbidden sums (Theorem 3) ==")
    t3 = check_forbidden_sum()
    print(f"   c = 2 mod 4, g0 + g0' = c 4^k - 1 never both survive: {t3}")
    if verify:
        check(t3, "forbidden sum c = 2 mod 4")

    print("\n== 9/4 model: shadow maps (Theorem 5) ==")
    t5 = check_shadow_maps()
    print(f"   difference Delta and sum S shadows reproduce pair dynamics: {t5}")
    if verify:
        check(t5, "difference / sum shadow exactness")

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
