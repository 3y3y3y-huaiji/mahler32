/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Zero-topological-entropy symbolic obstructions for the Mahler `3/2` map

This module formalises the *finite, decidable* core of the symbolic-dynamical obstructions for
the Mahler map `T x = {3x/2}` on `[0, 1)`.  The distinction between the **deterministic** map
and the **two-branch joint relation** is the central modelling point of the file:

* **The arithmetic engine** (`exclusion_integer`): an integer squeezed between a `2`-adic
  divisibility and an Archimedean size bound must vanish.  This is the `2`-adic half of every
  "all-real exclusion" argument.

* **The deterministic even-branch obstruction** (`cage_two_sevenths`): for the map `Tq = T0`, the
  interval `[2/7, 5/7)` has *no* four-term orbit.  This is a genuine statement about iterating the
  single deterministic map `Tq`; it is proved by exact rational interval arithmetic, with no
  numerical approximation and no `native_decide`.  It is **not**, and must not be presented as, an
  exclusion theorem for the two-branch relation below.

* **The two-branch joint relation** (`Step x y ↔ y = T0 x ∨ y = T1 x`): a real Mahler orbit may
  switch between the two branches at every step, so the honest object is `Step`, not `Tq`.  Under
  `Step` the barrier `[2/7, 5/7)` is emphatically **not** emptied: `joint_orbit_two_sevenths`
  exhibits a six-term `Step`-orbit inside it, and `joint_cycle_two_fifths` /
  `joint_cycle_four_thirteenths` exhibit genuine periodic `Step`-cycles inside it.  In particular
  the single-branch emptying depth `3` of `Tq` says nothing about the joint relation.

* **The finite-state holed obstruction** (`holedCage`): the union `[5/24, 11/24) ∪ [13/24, 19/24)`
  has, under the joint relation, the exact finite survivor set `{4/15, 2/5, 3/5, 11/15}`
  (`holed_cage_two_cycle`, `holed_cage_transients`): a genuine `2`-cycle `2/5 ↔ 3/5` together with
  the two transients `4/15 ↦ 2/5` and `11/15 ↦ 3/5`.  This is the machine-checked "finite-state /
  zero-entropy" core obstruction; the *full* survivor-count and SCC analysis for the other barriers
  is reproduced by `scripts/generate_certificates.py`.

* **Width bookkeeping** (`width_three_sevenths`, `width_four_sevenths`): the widths that make the
  single-interval and the holed `4/7` barriers interesting.

The joint relation is analysed in `scripts/generate_certificates.py`: exact rational survivor sets
`V_n = U ∩ (T0⁻¹ Vₙ₋₁ ∪ T1⁻¹ Vₙ₋₁)`, finite-depth Markov partitions with SCC / branching tests, and
exact rational periodic cycles.  The computation shows `[28/97,69/97)` and `[2/7,5/7)` keep infinite
joint survivor sets of zero topological entropy (sub-exponential cylinder growth), while the holed
obstruction above has the finite survivor set proved here.  The general signed rational automaton
formalisation lives in `Mahler32.ZeroEntropyAutomaton`.  The constant `8/57 = T0⁻¹(4/19)` is the
exact preimage of the cup `3`-cycle `4/19 ↦ 6/19 ↦ 9/19`; it is *not* a single-branch emptying
threshold, and the left-hole family `[δ,1/2)` instead has the three exact regimes verified in the
script (`δ > 4/19` empties; `8/57 < δ ≤ 4/19` keeps a finite survivor set; `δ < 8/57` has positive
entropy via the fold `T1 ∘ T0³`).
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

/-- The **two-branch joint step relation**: a real Mahler orbit may take either branch at each
step, so `Step x y` means that `y` is one of the two possible successors of `x`.  This is the
honest replacement for the deterministic single-branch iteration `Tq`; it is *not* the same
relation, and `[2/7,5/7)` is not emptied under `Step` (see `joint_orbit_two_sevenths`). -/
@[expose] public def Step (x y : ℚ) : Prop := y = T0 x ∨ y = T1 x

/-- `T0` is the deterministic map `Tq`. -/
public theorem T0_of_lt {x : ℚ} (h : (3 * x) / 2 < 1) : T0 x = (3 * x) / 2 := Tq_of_lt h

public theorem T0_of_ge {x : ℚ} (h : ¬ (3 * x) / 2 < 1) : T0 x = (3 * x) / 2 - 1 := Tq_of_ge h

/-- Rewrite rule for the non-wrapping odd branch. -/
public theorem T1_of_lt {x : ℚ} (h : (3 * x) / 2 + 1 / 2 < 1) :
    T1 x = (3 * x) / 2 + 1 / 2 := by
  unfold T1
  dsimp only
  exact ite_eq_left h

/-- Rewrite rule for the wrapping odd branch (image still `< 2`). -/
public theorem T1_of_ge_lt {x : ℚ} (h1 : ¬ ((3 * x) / 2 + 1 / 2 < 1))
    (h2 : (3 * x) / 2 + 1 / 2 < 2) : T1 x = (3 * x) / 2 + 1 / 2 - 1 := by
  unfold T1
  dsimp only
  rw [ite_eq_right h1, ite_eq_left h2]

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

/-! ### The exact deterministic `[2/7, 5/7)` obstruction -/

/-- **The even-branch (deterministic) `[2/7, 5/7)` obstruction has no four-term orbit.**  For the
single deterministic map `T0 = Tq` there is no rational `x` with `x, T0x, T0²x, T0³x` all in
`[2/7, 5/7)`.  The proof tracks the exact image interval step by step:
`[2/7,5/7) → [3/7,5/7) → [9/14,5/7)`, and the fourth image misses the interval entirely.

This is a statement about `Tq` alone.  It does **not** exclude orbits of the two-branch joint
relation `Step`; see `joint_orbit_two_sevenths` for a six-term `Step`-orbit inside the same
interval. -/
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

/-! ### The two-branch joint relation: genuine non-emptiness and cycles -/

/-- The interval `[2/7, 5/7)` as a predicate on `ℚ` (kept as a definition so that the numerals in
the witness theorems are unambiguously rational). -/
@[expose] public def cage27 (x : ℚ) : Prop := 2 / 7 ≤ x ∧ x < 5 / 7

/-- **A six-term `Step`-orbit inside `[2/7, 5/7)`.**  This is the explicit witness that the
deterministic single-branch theorem `cage_two_sevenths` does *not* exclude orbits of the joint
relation: `3/7 ↦ 9/14 ↦ 13/28 ↦ 39/56 ↦ 61/112 ↦ 71/224`, alternating the two branches, stays in
the barrier for far more than the deterministic depth `3`. -/
public theorem joint_orbit_two_sevenths :
    Step (3 / 7) (9 / 14) ∧ Step (9 / 14) (13 / 28) ∧
      Step (13 / 28) (39 / 56) ∧ Step (39 / 56) (61 / 112) ∧
      Step (61 / 112) (71 / 224) ∧
      cage27 (3 / 7) ∧ cage27 (9 / 14) ∧ cage27 (13 / 28) ∧
      cage27 (39 / 56) ∧ cage27 (61 / 112) ∧ cage27 (71 / 224) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · left; rw [T0_of_lt (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  · left; rw [T0_of_lt (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  all_goals (unfold cage27; constructor <;> norm_num)

/-- **A genuine `2`-cycle inside `[2/7, 5/7)`**: `2/5 ↔ 3/5` under the joint relation. -/
public theorem joint_cycle_two_fifths :
    Step (2 / 5) (3 / 5) ∧ Step (3 / 5) (2 / 5) ∧
      cage27 (2 / 5) ∧ cage27 (3 / 5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · left; rw [T0_of_lt (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  · unfold cage27; constructor <;> norm_num
  · unfold cage27; constructor <;> norm_num

/-- **A genuine `4`-cycle inside `[2/7, 5/7)`**: `4/13 ↦ 6/13 ↦ 9/13 ↦ 7/13 ↦ 4/13`.  The script
`scripts/generate_certificates.py` confirms the same cycle also lies in `[28/97, 69/97)`; its
`2`-cycle companion is `joint_cycle_two_fifths`. -/
public theorem joint_cycle_four_thirteenths :
    Step (4 / 13) (6 / 13) ∧ Step (6 / 13) (9 / 13) ∧
      Step (9 / 13) (7 / 13) ∧ Step (7 / 13) (4 / 13) ∧
      cage27 (4 / 13) ∧ cage27 (6 / 13) ∧ cage27 (9 / 13) ∧ cage27 (7 / 13) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · left; rw [T0_of_lt (by norm_num)]; norm_num
  · left; rw [T0_of_lt (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  all_goals (unfold cage27; constructor <;> norm_num)

/-- The holed zero-entropy symbolic obstruction `U = [5/24, 11/24) ∪ [13/24, 19/24)`. -/
@[expose] public def holedCage (x : ℚ) : Prop :=
  (5 / 24 ≤ x ∧ x < 11 / 24) ∨ (13 / 24 ≤ x ∧ x < 19 / 24)

/-- **The holed obstruction contains a genuine `2`-cycle** `2/5 ↔ 3/5`. -/
public theorem holed_cage_two_cycle :
    Step (2 / 5) (3 / 5) ∧ Step (3 / 5) (2 / 5) ∧
      holedCage (2 / 5) ∧ holedCage (3 / 5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · left; rw [T0_of_lt (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  · left; constructor <;> norm_num
  · right; constructor <;> norm_num

/-- **The two transients of the holed obstruction**: `4/15 ↦ 2/5` and `11/15 ↦ 3/5`.  Together
with `holed_cage_two_cycle` these are the exact finite survivor set `{4/15, 2/5, 3/5, 11/15}` of
the joint relation on `[5/24,11/24) ∪ [13/24,19/24)` (the excludedness of any other point is the
script certificate of `scripts/generate_certificates.py`). -/
public theorem holed_cage_transients :
    Step (4 / 15) (2 / 5) ∧ Step (11 / 15) (3 / 5) ∧
      holedCage (4 / 15) ∧ holedCage (11 / 15) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · left; rw [T0_of_lt (by norm_num)]; norm_num
  · right; rw [T1_of_ge_lt (by norm_num) (by norm_num)]; norm_num
  · left; constructor <;> norm_num
  · right; constructor <;> norm_num

end Mahler32.ZeroEntropyCages

end
