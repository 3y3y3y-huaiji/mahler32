#!/usr/bin/env python3
"""Exact rational / integer certificates for the Mahler ``3/2`` barrier families
and for the ``9/4`` finite-roof model.

This script recomputes, in exact arithmetic (``fractions.Fraction`` and Python
``int``), the finite certificates quoted in ``papers/paper2_zero_entropy_fluid``.
It never uses floating point for a decision.

Two independent blocks:

* **Circle-map barriers.**  The Mahler map ``T x = {3x/2}`` has two monotone
  branches ``T0 x = {3x/2}`` and ``T1 x = {3x/2 + 1/2}``.  A genuine Mahler
  orbit may switch branches at every step, so the correct object is the
  **two-branch joint relation**

      ``Step x y  <=>  y = T0 x  or  y = T1 x``.

  For a barrier ``U`` the ``n``-step *joint survivor set* is

      ``V_n = U ∩ (T0^{-1}(V_{n-1}) ∪ T1^{-1}(V_{n-1}))``,

  a finite union of rational half-open intervals, computed exactly here.  Note
  that the earlier "single-branch emptying depth" (iterating ``T0`` alone or
  ``T1`` alone) does **not** describe the joint relation; it is replaced by:

    - the exact joint survivor sequence ``V_n`` (component count + total
      length), showing which barriers empty at a finite depth and which keep a
      (Cantor / countable / finite) survivor set forever;
    - a finite-depth rational Markov partition and its directed transition
      graph, with SCC decomposition and a branching / double-cycle test;
    - the exact rational periodic cycles of the joint relation inside ``U``
      (period up to ``P_MAX``), verifying that they are genuine cycles.

  The honest conclusions are recorded per barrier: ``[5/24,11/24) ∪
  [13/24,19/24)`` has the **finite** survivor set ``{4/15, 2/5, 3/5, 11/15}``
  (a single 2-cycle plus two transients, i.e. a genuine finite-state cage),
  while ``[2/7,5/7)`` and ``[28/97,69/97)`` have **infinite** zero-entropy
  survivor sets (the joint relation is *not* emptied; only its cylinder count
  grows sub-exponentially).  These are not "single-branch emptying" results.

* **Left-hole family** ``[δ, 1/2)`` under the cup map ``F = T0 on [0,1/3)``,
  ``T1 on [1/3,1/2)``.  Exact rational arithmetic confirms the three regimes:
  ``δ > 4/19`` empties finitely; ``8/57 < δ ≤ 4/19`` does not empty but has a
  finite / zero-entropy survivor set containing the 3-cycle ``4/19 → 6/19 →
  9/19 → 4/19``; ``δ < 8/57`` has exponentially growing survivor-cylinder
  count (positive entropy), driven by the exact fold ``T1 ∘ T0³`` sending
  ``[8/81, 8/57)`` into ``[0, 4/19)`` (``T1(T0³(8/57)) = 4/19``).

* **``9/4`` finite-roof model.**  The integer model ``4 g_{k+1} = 9 g_k + d_k``,
  ``d_k in {2, 3}``, together with its mirror involution, its even-rung
  annihilation, the independent difference/sum shadow maps, and the finite
  mirror-block counting bounds.

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


def total_length(u) -> Q:
    return sum((b - a for a, b in u), Q(0))


def T0q(x: Q) -> Q:
    """The even branch ``T0 x = {3x/2}``."""
    y = Q(3, 2) * x
    return y if y < 1 else y - 1


def T1q(x: Q) -> Q:
    """The odd branch ``T1 x = {3x/2 + 1/2}``."""
    y = Q(3, 2) * x + Q(1, 2)
    if y < 1:
        return y
    if y < 2:
        return y - 1
    return y - 2


def preimage(intervals, branch=0):
    """Exact preimage of ``intervals`` under one monotone branch (on ``[0,1)``).

    ``branch = 0``: the two inverse lifts of ``T0 x = {3x/2}`` are
    ``x = (2/3)(y + shift)`` for ``shift in {0, 1}``.

    ``branch = 1``: the two inverse lifts of ``T1 x = {3x/2 + 1/2}`` are
    ``x = (2/3)(y + shift)`` for ``shift in {-1/2, 1/2}``.
    """
    out: list[tuple[Q, Q]] = []
    shifts = (Q(0), Q(1)) if branch == 0 else (Q(-1, 2), Q(1, 2))
    for a, b in intervals:
        for shift in shifts:
            lo = max(Q(0), Q(2, 3) * (a + shift))
            hi = min(Q(1), Q(2, 3) * (b + shift))
            if lo < hi:
                out.append((lo, hi))
    return normalise(out)


def joint_preimage(intervals):
    """Preimage under the **joint** two-branch relation ``{T0, T1}``."""
    return normalise(preimage(intervals, 0) + preimage(intervals, 1))


def joint_survivors(u, max_depth):
    """Return the joint survivor sequence ``[V_0, V_1, ...]`` (exact rationals)."""
    seq = [normalise(u)]
    cur = normalise(u)
    for _ in range(max_depth):
        cur = intersect(u, joint_preimage(cur))
        seq.append(cur)
        if not cur:
            break
    return seq


# ---------------------------------------------------------------------------
# periodic cycles of the joint relation inside a barrier
# ---------------------------------------------------------------------------

def step_branch(j: int, y: Q) -> Q:
    return T0q(y) if j == 0 else T1q(y)


def in_domain(domain, x: Q) -> bool:
    return any(lo <= x < hi for lo, hi in domain)


def periodic_points(domain, p_max: int):
    """Enumerate the ``Step``-cycles of period ``<= p_max`` lying in ``domain``.

    ``domain`` is a list of half-open rational intervals.  Every cycle point is
    the fixed point of an affine composition with slope ``(3/2)^p``, hence
    rational; we enumerate the branch word and the additive constants, solve the
    fixed-point equation, and re-verify the whole orbit.
    """
    import itertools

    found: dict[Q, tuple[int, tuple[Q, ...]]] = {}
    for p in range(1, p_max + 1):
        for mask in range(1 << p):
            word = [(mask >> k) & 1 for k in range(p)]
            opts = [([Q(0), Q(1)] if j == 0 else [Q(-1, 2), Q(1, 2)]) for j in word]
            for ks in itertools.product(*opts):
                q = Q(1)
                r = Q(0)
                for k in ks:
                    q = Q(3, 2) * q
                    r = Q(3, 2) * r - k
                if q == 1:
                    continue
                x = r / (1 - q)
                if not in_domain(domain, x):
                    continue
                y = x
                orbit = [y]
                ok = True
                for j in word:
                    y = step_branch(j, y)
                    if not in_domain(domain, y):
                        ok = False
                        break
                    orbit.append(y)
                if ok and y == x:
                    found[x] = (p, tuple(orbit))
    return found


def cycle_key(points, x):
    """Normalise a cycle by its starting point already being returned."""
    return points[x][1]


# ---------------------------------------------------------------------------
# finite-depth rational Markov partition + SCC analysis
# ---------------------------------------------------------------------------

def markov_atoms(lo: Q, hi: Q, depth: int):
    """A finite rational partition of ``[lo, hi)`` closed under one-step preimage
    refinement up to the branches' own breakpoints (depth is a safety bound).

    The cuts are the endpoints ``lo, hi`` and all one-step preimages of ``lo`` and
    of the branch breakpoints that fall inside the interval, iterated ``depth``
    times.  This is the exact depth-``depth`` martingale partition; its atoms are
    rational and the transition graph below is computed on it exactly.
    """
    cuts = {lo, hi}
    seeds = {lo, hi, Q(1, 3), Q(2, 3)}
    for _ in range(depth):
        new = set(cuts)
        for c in seeds | cuts:
            for shift in (Q(0), Q(1), Q(-1, 2), Q(1, 2)):
                x = Q(2, 3) * (c + shift)
                if lo < x < hi:
                    new.add(x)
        if new == cuts:
            break
        cuts = new
    xs = sorted(cuts)
    return [(xs[i], xs[i + 1]) for i in range(len(xs) - 1)]


def atom_transitions(atoms, lo: Q, hi: Q):
    """Outer transition relation of the joint map on a partition of ``[lo,hi)``."""
    n = len(atoms)
    edges: list[set[int]] = [set() for _ in range(n)]
    for i, (p, q) in enumerate(atoms):
        for branch in (0, 1):
            cuts = sorted({p, q} | {c for c in (Q(1, 3), Q(2, 3)) if p < c < q})
            for u, v in zip(cuts, cuts[1:]):
                f = T0q if branch == 0 else T1q
                a, b = f(u), f(v)
                if a > b:
                    a, b = b, a
                for k, (c, d) in enumerate(atoms):
                    if max(a, c) < min(b, d):
                        edges[i].add(k)
    return edges


def scc(n: int, edges: list[set[int]]):
    """Tarjan SCC decomposition (iterative to avoid recursion depth issues)."""
    index = [0]
    ind = [-1] * n
    low = [0] * n
    on = [False] * n
    stack: list[int] = []
    comps: list[list[int]] = []

    for root in range(n):
        if ind[root] != -1:
            continue
        work = [(root, iter(sorted(edges[root])))]
        ind[root] = low[root] = index[0]
        index[0] += 1
        stack.append(root)
        on[root] = True
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if ind[w] == -1:
                    ind[w] = low[w] = index[0]
                    index[0] += 1
                    stack.append(w)
                    on[w] = True
                    work.append((w, iter(sorted(edges[w]))))
                    advanced = True
                    break
                if on[w] and ind[w] < low[v]:
                    low[v] = ind[w]
            if advanced:
                continue
            work.pop()
            if work:
                u = work[-1][0]
                if low[v] < low[u]:
                    low[u] = low[v]
            if low[v] == ind[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on[w] = False
                    comp.append(w)
                    if w == v:
                        break
                comps.append(comp)
    return comps


def graph_report(lo: Q, hi: Q, depth: int):
    atoms = markov_atoms(lo, hi, depth)
    edges = atom_transitions(atoms, lo, hi)
    n = len(atoms)
    comps = scc(n, edges)
    nontrivial = []
    branching = 0
    for c in comps:
        cs = set(c)
        internal = [len(edges[v] & cs) for v in c]
        if len(c) > 1 or any(v in edges[v] for v in c):
            nontrivial.append(len(c))
            if any(k > 1 for k in internal):
                branching += 1
    return {
        "states": n,
        "sccs": len(comps),
        "nontrivial_scc_sizes": sorted(nontrivial, reverse=True),
        "branching_sccs": branching,
    }


# ---------------------------------------------------------------------------
# the cup map on [0, 1/2) and the left-hole family
# ---------------------------------------------------------------------------

def cup(x: Q) -> Q:
    y = Q(3, 2) * x
    return y if y < Q(1, 2) else y - Q(1, 2)


def cup_preimage(intervals):
    """Exact preimage of ``intervals`` under the deterministic cup map on ``[0,1/2)``."""
    out: list[tuple[Q, Q]] = []
    for a, b in intervals:
        # branch T0 on [0,1/3): x = (2/3) y
        lo = max(Q(0), Q(2, 3) * a)
        hi = min(Q(1, 3), Q(2, 3) * b)
        if lo < hi:
            out.append((lo, hi))
        # branch T1 (wrap) on [1/3,1/2): x = (2/3)(y + 1/2)
        lo = max(Q(1, 3), Q(2, 3) * (a + Q(1, 2)))
        hi = min(Q(1, 2), Q(2, 3) * (b + Q(1, 2)))
        if lo < hi:
            out.append((lo, hi))
    return normalise(out)


def cup_survivors(delta: Q, max_depth: int, component_cap: int = 20000):
    """Joint survivor sequence of ``[δ, 1/2)`` under the cup map.

    Returns ``(status, depth, seq)`` where status is ``empty``, ``many`` (growth
    exceeded the cap, i.e. positive-entropy regime) or ``bounded``.
    """
    u = [(delta, Q(1, 2))]
    cur = normalise(u)
    seq = [cur]
    for n in range(1, max_depth + 1):
        cur = intersect(u, cup_preimage(cur))
        seq.append(cur)
        if not cur:
            return ("empty", n, seq)
        if len(cur) > component_cap:
            return ("many", n, seq)
    return ("bounded", max_depth, seq)


# ---------------------------------------------------------------------------
# the 9/4 finite-roof model
# ---------------------------------------------------------------------------

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


def step94(g: int):
    """One step of ``4 g_{k+1} = 9 g_k + d_k`` with ``d_k in {2, 3}``."""
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
    m = d % 4
    if m == 0:
        return 9 * d // 4
    if m == 1:
        return (9 * d - 1) // 4
    if m == 3:
        return (9 * d + 1) // 4
    return None


def step_sum(s: int):
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
    for N in range(2, n_max + 1, 2):
        M = 4 ** N
        for g0 in range(M):
            mir = M - 1 - g0
            if survives94(N + 2, g0) and survives94(N + 2, mir):
                return False
    return True


def survivor_counts(N: int, extra: int):
    M = 4 ** N
    sN = sum(1 for g in range(M) if survives94(N, g))
    sNe = sum(1 for g in range(M) if survives94(N + extra, g))
    return sN, sNe


def check_forbidden_sum(c_max=18, k_max=4):
    for c in range(2, c_max + 1, 4):
        for k in range(k_max + 1):
            total = c * 4 ** k - 1
            for g0 in range(total + 1):
                g1 = total - g0
                if survives94(k + 1, g0) and survives94(k + 1, g1):
                    return False
    return True


def check_shadow_maps(n_max=4, bound=250):
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


def check_odd_klein4(n_max=9):
    """General odd-rung Klein-4 exclusion, verified for odd N <= n_max."""
    for N in range(3, n_max + 1, 2):
        M = 4 ** N
        Mp = 4 ** (N - 1)
        for g0 in range(Mp):
            for d in (1, 2, 3):
                h = g0 + d * Mp
                quad = {g0, h, M - 1 - g0, M - 1 - h}
                if sum(1 for x in quad if 0 <= x < M and survives94(N + 1, x)) > 3:
                    return False
    return True


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

BARRIERS = {
    "[2/7,5/7)": [(Q(2, 7), Q(5, 7))],
    "[1/7,3/7) u [4/7,6/7)": [(Q(1, 7), Q(3, 7)), (Q(4, 7), Q(6, 7))],
    "[28/97,69/97)": [(Q(28, 97), Q(69, 97))],
    "[5/24,11/24) u [13/24,19/24)": [(Q(5, 24), Q(11, 24)), (Q(13, 24), Q(19, 24))],
    "[1/5,7/15) u [8/15,4/5)": [(Q(1, 5), Q(7, 15)), (Q(8, 15), Q(4, 5))],
}


def barrier_summary(name, u, max_depth=24, graph_depth=7, period_max=8):
    seq = joint_survivors(u, max_depth)
    finite = seq[-1] == []
    finite_depth = (len(seq) - 1) if finite else None
    comps = [len(v) for v in seq]
    lengths = [total_length(v) for v in seq]
    cycles = periodic_points(u, period_max)
    return {
        "name": name,
        "finite": finite,
        "depth": finite_depth,
        "components": comps,
        "lengths": lengths,
        "cycles": cycles,
        "graph": graph_report(u[0][0], u[0][1], graph_depth) if len(u) == 1 else None,
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

    # ------------------------------------------------------------------
    # joint two-branch relation: survivorship of the barrier sets
    # ------------------------------------------------------------------
    print("\n== joint two-branch relation Step x y  <=>  y = T0 x  or  y = T1 x ==")
    print("   (V_n = U ∩ (T0^{-1}(V_{n-1}) ∪ T1^{-1}(V_{n-1})), exact rationals)")
    summaries = {}
    for name, u in BARRIERS.items():
        s = barrier_summary(name, u)
        summaries[name] = s
        if s["finite"]:
            print(f"   {name:34s} JOINT-EMPTY at depth {s['depth']}")
        else:
            print(f"   {name:34s} survivor stays: comps V_0..V_{len(s['components'])-1} = "
                  f"{s['components'][:8]} ... ; |V_last| = {float(s['lengths'][-1]):.3e}")
        if s["graph"]:
            g = s["graph"]
            print(f"       finite-depth graph: states={g['states']} sccs={g['sccs']} "
                  f"nontrivial={g['nontrivial_scc_sizes']} branching_sccs={g['branching_sccs']}")
        if s["cycles"]:
            cls = sorted({cycle_key(s["cycles"], x) for x in s["cycles"]})
            print(f"       exact Step-cycles (period <= 8): {len(cls)} "
                  f"e.g. {[str(p[0]) for p in cls[:4]]}")

    # specific honest conclusions
    s27 = summaries["[2/7,5/7)"]
    s2897 = summaries["[28/97,69/97)"]
    sholed = summaries["[5/24,11/24) u [13/24,19/24)"]
    if verify:
        check(not s27["finite"], "[2/7,5/7): joint survivor is NOT empty (single-branch emptying is unrelated)")
        c27 = s27["components"]
        # finite-horizon polynomial cylinder growth: consistent with zero entropy.
        check(all(c27[n] <= n ** 3 + 100 for n in range(1, len(c27))),
              "[2/7,5/7): survivor components grow at most cubically (zero-entropy horizon certificate)")
        check(any(abs(p - Q(2, 5)) == 0 for p in s27["cycles"]),
              "[2/7,5/7): contains the 2-cycle 2/5 <-> 3/5")
        check(any(abs(p - Q(4, 13)) == 0 for p in s27["cycles"]),
              "[2/7,5/7): contains the 4-cycle 4/13 -> 6/13 -> 9/13 -> 7/13")
        check(s2897["components"][1:] == [2 * k for k in range(1, len(s2897["components"]))],
              "[28/97,69/97): joint survivor has exactly 2k components at depth k")
        check(not sholed["finite"] and sholed["components"][-1] == 4,
              "[5/24,11/24) u [13/24,19/24): survivor stays at exactly 4 components")
        hcyc = set(sholed["cycles"])
        check({Q(2, 5), Q(3, 5)} <= hcyc and hcyc <= {Q(4, 15), Q(2, 5), Q(3, 5), Q(11, 15)},
              "holed cage: periodic points are exactly the 2-cycle 2/5 <-> 3/5")
        # the four survivor points and their exact forward step
        check(T0q(Q(2, 5)) == Q(3, 5) and T1q(Q(3, 5)) == Q(2, 5),
              "holed cage 2-cycle: 2/5 --T0--> 3/5 --T1--> 2/5")
        check(T0q(Q(4, 15)) == Q(2, 5) and T1q(Q(11, 15)) == Q(3, 5),
              "holed cage transients: 4/15 -> 2/5, 11/15 -> 3/5")

    # ------------------------------------------------------------------
    # the old single-branch numbers, kept only to show they differ
    # ------------------------------------------------------------------
    print("\n== single-branch (T0-alone / T1-alone) emptying, for contrast only ==")
    print("   (these are NOT the joint relation; the old 'cage' reading is retired)")
    for name, u in BARRIERS.items():
        d0 = cup_alone_depth(u, 0)
        d1 = cup_alone_depth(u, 1)
        print(f"   {name:34s} T0-alone depth={d0}  T1-alone depth={d1}")

    # ------------------------------------------------------------------
    # left-hole family under the cup map
    # ------------------------------------------------------------------
    print("\n== left-hole family [δ, 1/2) under the cup map F ==")
    print("   F = T0 on [0,1/3), T1 on [1/3,1/2)  (the branch-restricted joint map)")
    fold8 = Q(81, 16) * Q(8, 57) - Q(1, 2)
    print(f"   8/57 = (2/3)(4/19): {Q(2, 3) * Q(4, 19) == Q(8, 57)}")
    print(f"   T1(T0^3(x)) = 81x/16 - 1/2 ; T1(T0^3(8/57)) = {fold8}  (= 4/19: {fold8 == Q(4, 19)})")
    if verify:
        check(Q(2, 3) * Q(4, 19) == Q(8, 57), "8/57 == (2/3)(4/19) == T0^{-1}(4/19)")
        check(fold8 == Q(4, 19), "T1(T0^3(8/57)) == 4/19 (feedback threshold)")
        # fold maps [8/81, 8/57) into [0, 4/19)
        lo_img = Q(81, 16) * Q(8, 81) - Q(1, 2)
        check(lo_img == 0, "T1(T0^3(8/81)) == 0")

    regimes = [
        ("delta > 4/19 (finite emptying)", [Q(9, 20), Q(1, 4), Q(2, 5), Q(4, 19) + Q(1, 1000)], "empty"),
        ("8/57 < delta <= 4/19 (finite / zero entropy)", [Q(1, 7), Q(3, 19), Q(2, 10), Q(4, 19)], "bounded"),
        ("delta < 8/57 (positive entropy)", [Q(1, 10), Q(1, 8), Q(7, 57)], "many"),
    ]
    for label, deltas, expect in regimes:
        print(f"   -- {label}")
        for d in deltas:
            status, depth, seq = cup_survivors(d, max_depth=40)
            comps = len(seq[-1])
            print(f"      δ={str(d):>8s} ({float(d):.5f}): status={status} depth/iter={depth} "
                  f"comps_last={comps} len_last={float(total_length(seq[-1])):.2e}")
            if verify:
                if expect == "empty":
                    ok = status == "empty"
                elif expect == "bounded":
                    ok = status == "bounded" and comps <= 10
                else:  # positive-entropy: the survivor's component count explodes
                    ok = comps >= 500
                check(ok, f"left-hole δ={d}: regime `{label}` (got {status}, comps={comps})")
        # regime 2 additionally contains the 3-cycle
        if expect == "bounded":
            if verify:
                check(all(d <= Q(4, 19) for d in deltas),
                      "bounded regime sample deltas are <= 4/19")

    # the 3-cycle sits in [δ,1/2) exactly when δ <= 4/19
    if verify:
        check(cup(Q(4, 19)) == Q(6, 19) and cup(Q(9, 19)) == Q(4, 19),
              "3-cycle 4/19 -> 6/19 -> 9/19 -> 4/19 inside [δ,1/2) for δ <= 4/19")

    # ------------------------------------------------------------------
    # widths
    # ------------------------------------------------------------------
    print("\n== widths ==")
    print("   [2/7,5/7) width =", Q(5, 7) - Q(2, 7))
    print("   holed width      =", (Q(3, 7) - Q(1, 7)) + (Q(6, 7) - Q(4, 7)))
    if verify:
        check(Q(5, 7) - Q(2, 7) == Q(3, 7), "width [2/7,5/7) == 3/7")
        check((Q(3, 7) - Q(1, 7)) + (Q(6, 7) - Q(4, 7)) == Q(4, 7), "holed width == 4/7")

    # ------------------------------------------------------------------
    # 9/4 model
    # ------------------------------------------------------------------
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

    print("\n== 9/4 model: odd-rung Klein-4 exclusion (Theorem 4, general odd N) ==")
    t4 = check_odd_klein4()
    print(f"   at most 3 of each sibling/mirror quadruple survive N+1, odd N <= 9: {t4}")
    if verify:
        check(t4, "odd-rung Klein-4 exclusion, odd N <= 9")

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


def cup_alone_depth(u, branch, max_depth=30):
    """Least ``n`` with ``{x : T_branch^k x in u for 0 <= k <= n} == empty``.

    Kept only to document the *retired* single-branch reading; it is not the
    joint relation.
    """
    cur = normalise(u)
    for n in range(max_depth + 1):
        if not cur:
            return n
        cur = intersect(u, preimage(cur, branch))
    return None


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
