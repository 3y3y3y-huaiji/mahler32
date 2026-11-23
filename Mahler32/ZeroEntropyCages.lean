/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Zero-entropy exclusion cages for the Mahler `3/2` map

This module formalises the *finite, decidable* core of the "exclusion cage" story for the
Mahler map `T x = {3x/2}` on `[0, 1)`.  Three layers are distinguished:

* **The arithmetic engine** (`exclusion_integer`): an integer squeezed between a `2`-adic
  divisibility and an Archimedean size bound must vanish.  This is the `2`-adic half of every
  "all-real exclusion" argument: an orbit that is eventually periodic produces an integer
  divisible by arbitrarily high powers of `2`, hence equal to `0`.

* **The exact cage** (`cage_two_sevenths`): for the *even* branch `T0` of the Mahler circle map,
  the interval `[2/7, 5/7)` has *no* four-term orbit.  If `x, T0x, T0²x, T0³x` all lie in
  `[2/7, 5/7)`, contradiction.  This is proved by exact rational interval arithmetic, with no
  numerical approximation and no `native_decide`.

* **The two branches** (`T0`, `T1`): the Mahler circle map is studied through its two monotone
  branches `T0 x = {3x/2}` (even) and `T1 x = {3x/2 + 1/2}` (odd).  `cage_two_sevenths` is the
  even-branch statement; the companion odd-branch cage empties at the *same* finite depth, which is
  certified by `scripts/generate_certificates.py` (both branches are checked there) rather than
  re-proved here.

* **Width bookkeeping** (`width_three_sevenths`, `width_four_sevenths`): the widths that make
  the single-interval and the holed `4/7` barriers interesting.

The stronger claims for the other barrier sets quoted in `papers/paper2_zero_entropy_fluid`
(the `31`-state `[2/7,5/7)` automaton, the `128`-state holed `4/7` cage) are *computational
certificates*, reproduced by `scripts/generate_certificates.py`; they are not asserted here as
Lean theorems.  The constant `8/57 = T0⁻¹(4/19)` is an exact preimage of the cup `3`-cycle
`4/19 ↦ 6/19 ↦ 9/19`; exact computation shows it is *not* a critical emptying threshold for the
left-hole family `[δ, 1/2)`, which empties for every `δ > 0` tested.
-/

public section

namespace Mahler32.ZeroEntropyCages

/-- The Mahler map `T x = {3x/2}` on `[0, 1)`, written without `floor` (it is only ever used on
`[0, 1)`, where `3x/2 < 3/2`, so a single conditional subtraction reproduces the fractional
part exactly). -/
@[expose] public def Tq (x : ℚ) : ℚ :=
  if (3 * x) / 2 < 1 then (3 * x) / 2 else (3 * x) / 2 - 1

/-- Rewrite rule for the non-wrapping branch. -/
public theorem Tq_of_lt {x : ℚ} (h : (3 * x) / 2 < 1) : Tq x = (3 * x) / 2 := by
  simp [Tq, h]

/-- Rewrite rule for the wrapping branch. -/
public theorem Tq_of_ge {x : ℚ} (h : ¬ (3 * x) / 2 < 1) : Tq x = (3 * x) / 2 - 1 := by
  simp [Tq, h]

/-- The **even branch** of the Mahler circle map, `T0 x = {3x/2}` (the map `Tq`). -/
public def T0 (x : ℚ) : ℚ := Tq x

/-- The **odd branch** of the Mahler circle map, `T1 x = {3x/2 + 1/2}`. -/
@[expose] public def T1 (x : ℚ) : ℚ :=
  let y := (3 * x) / 2 + 1 / 2
  if y < 1 then y else if y < 2 then y - 1 else y - 2

/-! ### The arithmetic engine -/

/-- **Integer exclusion.**  If `2 ^ N ∣ M` and `|M| < 2 ^ N`, then `M = 0`.  This is the exact
step that turns "eventually periodic orbit" into "the initial point is `0`". -/
public theorem exclusion_integer {M : ℤ} {N : ℕ}
    (hdvd : (2 : ℤ) ^ N ∣ M) (hlt : |M| < (2 : ℤ) ^ N) : M = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  have hpos : (0 : ℤ) < (2 : ℤ) ^ N := by positivity
  have hk : |k| < 1 := by
    rw [abs_mul, abs_of_pos hpos] at hlt
    by_contra h
    have h1 : 1 ≤ |k| := by omega
    nlinarith [abs_nonneg k]
  have hk0 : k = 0 := by
    have h1 : -1 < k ∧ k < 1 := abs_lt.mp hk
    omega
  rw [hk0, mul_zero]

/-! ### The exact `[2/7, 5/7)` cage -/

/-- **The even-branch `[2/7, 5/7)` cage has no four-term orbit.**  For the even branch `T0 = Tq`
there is no rational `x` with `x, T0x, T0²x, T0³x` all in `[2/7, 5/7)`.  The proof tracks the exact
image interval step by step: `[2/7,5/7) → [3/7,5/7) → [9/14,5/7)`, and the fourth image misses the
cage entirely. -/
public theorem cage_two_sevenths : ∀ x : ℚ,
    2 / 7 ≤ x → x < 5 / 7 →
    ¬ (2 / 7 ≤ Tq x ∧ Tq x < 5 / 7 ∧
       2 / 7 ≤ Tq (Tq x) ∧ Tq (Tq x) < 5 / 7 ∧
       2 / 7 ≤ Tq (Tq (Tq x)) ∧ Tq (Tq (Tq x)) < 5 / 7) := by
  intro x hx0 hx1
  rintro ⟨h1a, h1b, h2a, h2b, h3a, h3b⟩
  -- Step 1: the wrap branch is impossible, so `x < 10/21` and `Tq x = 3x/2`.
  have hx10 : x < 10 / 21 := by
    by_cases hc : (3 * x) / 2 < 1
    · rw [Tq_of_lt hc] at h1b
      linarith
    · rw [Tq_of_ge hc] at h1a
      linarith
  have hTx : Tq x = (3 * x) / 2 := by
    apply Tq_of_lt
    linarith
  -- Step 2: again no wrap, so `Tq (Tq x) = 9x/4` and `x < 20/63`.
  have h9lt1 : 9 * x / 4 < 1 := by
    by_contra h
    have hge : ¬ (3 * (3 * x / 2)) / 2 < 1 := by
      intro hc
      linarith [not_lt.mp h]
    rw [hTx, Tq_of_ge hge] at h2a
    linarith
  have h2eq : Tq (Tq x) = 9 * x / 4 := by
    rw [hTx, Tq_of_lt (by linarith [h9lt1] : (3 * (3 * x / 2)) / 2 < 1)]
    ring
  have hx20 : x < 20 / 63 := by
    rw [h2eq] at h2b
    linarith
  -- Step 3: `Tq (Tq (Tq x)) = 27x/8` or `27x/8 - 1`, and both miss `[2/7, 5/7)`.
  by_cases hc : (3 * (9 * x / 4)) / 2 < 1
  · rw [h2eq, Tq_of_lt hc] at h3b
    -- `27x/8 < 5/7` contradicts `27x/8 ≥ 27/28`.
    linarith
  · rw [h2eq, Tq_of_ge hc] at h3a
    -- `27x/8 - 1 ≥ 2/7` contradicts `27x/8 - 1 < 1/14`.
    linarith

/-! ### Width bookkeeping -/

/-- The single interval `[2/7, 5/7)` has width `3/7`. -/
public theorem width_three_sevenths : (5 : ℚ) / 7 - 2 / 7 = 3 / 7 := by
  norm_num

/-- The holed union `[1/7, 3/7) ∪ [4/7, 6/7)` has total width `4/7`. -/
public theorem width_four_sevenths : ((3 : ℚ) / 7 - 1 / 7) + (6 / 7 - 4 / 7) = 4 / 7 := by
  norm_num

/-- The holed barrier is genuinely super-half: `4/7 > 1/2`. -/
public theorem four_sevenths_gt_half : (1 / 2 : ℚ) < 4 / 7 := by
  norm_num

end Mahler32.ZeroEntropyCages

end
