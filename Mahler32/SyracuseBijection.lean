/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Task 10 — Mahler–Syracuse full-branch bijection

`T0 x = (3/2) x`, `T1 x = (3/2) x - 1/2`, and the accelerated map
`syracuseMap a x = (3/2)^(a+1) x - 1/2` is exactly "`a` even steps, then one odd step".

For `a ≥ 2` the map is a bijection from the branch interval
`I_a = [loTile a, hiTile a)` onto `[0, 1/4)`; for `a = 1` the interval is truncated at `1/4` and
the image is `[0, 1/16)`, which forces the next branch index to be at least `5`.
-/

public section

namespace Mahler32.SyracuseBijection

/-- Even Mahler step. -/
@[expose] public def T0 (x : ℚ) : ℚ := (3 / 2 : ℚ) * x

/-- Odd Mahler step. -/
@[expose] public def T1 (x : ℚ) : ℚ := (3 / 2 : ℚ) * x - (1 / 2 : ℚ)

/-- `a`-fold even step. -/
@[expose] public def iterT0 : ℕ → ℚ → ℚ
  | 0, x => x
  | a + 1, x => iterT0 a (T0 x)

/-- Left endpoint of the `a`-th branch interval. -/
@[expose] public def loTile (a : ℕ) : ℚ := (1 / 3 : ℚ) * ((2 / 3 : ℚ) ^ a)

/-- Right endpoint, truncated at `1/4`. -/
@[expose] public def hiTile (a : ℕ) : ℚ := min (1 / 4 : ℚ) ((1 / 2 : ℚ) * ((2 / 3 : ℚ) ^ a))

/-- Accelerated Mahler–Syracuse map. -/
@[expose] public def syracuseMap (a : ℕ) (x : ℚ) : ℚ := ((3 / 2 : ℚ) ^ (a + 1)) * x - (1 / 2 : ℚ)

/-- Explicit inverse of `syracuseMap a`. -/
@[expose] public def syracuseInv (a : ℕ) (y : ℚ) : ℚ :=
  ((2 / 3 : ℚ) ^ (a + 1)) * (y + (1 / 2 : ℚ))

/-! ### Elementary power identities -/

lemma pow_cancel (a : ℕ) : ((3 / 2 : ℚ) ^ a) * ((2 / 3 : ℚ) ^ a) = 1 := by
  rw [← mul_pow]
  norm_num

lemma pow_two_thirds_pos (a : ℕ) : (0 : ℚ) < (2 / 3) ^ a := pow_pos (by norm_num) a

lemma pow_two_thirds_le_one (a : ℕ) : (2 / 3 : ℚ) ^ a ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

lemma pow_two_thirds_anti {j a : ℕ} (h : j ≤ a) : (2 / 3 : ℚ) ^ a ≤ (2 / 3) ^ j :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

lemma key_lo (a : ℕ) : ((3 / 2 : ℚ) ^ (a + 1)) * loTile a = 1 / 2 := by
  unfold loTile
  rw [pow_succ]
  linear_combination (1 / 2) * pow_cancel a

lemma key_hi (a : ℕ) : ((3 / 2 : ℚ) ^ (a + 1)) * ((1 / 2 : ℚ) * ((2 / 3 : ℚ) ^ a)) = 3 / 4 := by
  rw [pow_succ]
  linear_combination (3 / 4) * pow_cancel a

/-! ### Theorem 1: exact one-step dynamics and the legality window -/

/-- `a`-fold even step is multiplication by `(3/2)^a`. -/
public theorem iterT0_eq (a : ℕ) (x : ℚ) : iterT0 a x = ((3 / 2 : ℚ) ^ a) * x := by
  induction a generalizing x with
  | zero => simp [iterT0]
  | succ a ih =>
    show iterT0 a (T0 x) = _
    rw [ih, T0, pow_succ]
    ring

/-- `a` even steps followed by one odd step is exactly `syracuseMap a`. -/
public theorem T1_iterT0 (a : ℕ) (x : ℚ) : T1 (iterT0 a x) = syracuseMap a x := by
  rw [iterT0_eq]
  unfold T1 syracuseMap
  rw [pow_succ]
  ring

/-- Inside the `a`-th branch interval the `a` even steps stay strictly below `1/3`, and the
`a`-th even step lands in `[1/3, 1/2)`, i.e. exactly where the odd step fires. -/
public theorem legality_window {a : ℕ} (ha : 1 ≤ a) {x : ℚ}
    (hlo : loTile a ≤ x) (hhi : x < hiTile a) :
    (∀ j, j < a → iterT0 j x < 1 / 3) ∧
      1 / 3 ≤ iterT0 a x ∧ iterT0 a x < 1 / 2 := by
  have hhi' : hiTile a ≤ (1 / 2) * ((2 / 3 : ℚ) ^ a) := min_le_right _ _
  have hkeyA : ((3 / 2 : ℚ) ^ a) * ((1 / 2) * ((2 / 3 : ℚ) ^ a)) = 1 / 2 := by
    linear_combination (1 / 2) * pow_cancel a
  have hkeyLo : ((3 / 2 : ℚ) ^ a) * loTile a = 1 / 3 := by
    unfold loTile
    linear_combination (1 / 3) * pow_cancel a
  have hmix (j : ℕ) (hj : j ≤ a) :
      ((3 / 2 : ℚ) ^ j) * ((2 / 3 : ℚ) ^ a) = (2 / 3) ^ (a - j) := by
    have hdecomp : (2 / 3 : ℚ) ^ a = (2 / 3) ^ j * (2 / 3) ^ (a - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hdecomp, ← mul_assoc, pow_cancel, one_mul]
  constructor
  · intro j hj
    have hja : j ≤ a - 1 := by omega
    have hxlt : iterT0 j x = ((3 / 2 : ℚ) ^ j) * x := iterT0_eq j x
    have hlt0 : iterT0 j x < ((3 / 2 : ℚ) ^ j) * hiTile a := by
      rw [hxlt]
      exact mul_lt_mul_of_pos_left hhi (pow_pos (by norm_num) j)
    have hle1 : ((3 / 2 : ℚ) ^ j) * hiTile a ≤
        ((3 / 2 : ℚ) ^ j) * ((1 / 2) * ((2 / 3 : ℚ) ^ a)) :=
      mul_le_mul_of_nonneg_left hhi' (le_of_lt (pow_pos (by norm_num) j))
    have hm : ((3 / 2 : ℚ) ^ j) * ((1 / 2) * ((2 / 3 : ℚ) ^ a)) =
        (1 / 2) * ((2 / 3) ^ (a - j)) := by
      have h1 := hmix j (by omega)
      have hr : ((3 / 2 : ℚ) ^ j) * ((1 / 2) * ((2 / 3 : ℚ) ^ a)) =
          (1 / 2) * (((3 / 2 : ℚ) ^ j) * ((2 / 3 : ℚ) ^ a)) := by ring
      rw [hr, h1]
    rcases eq_or_lt_of_le hja with h | h
    · have hexp : a - j = 1 := by omega
      rw [hexp, pow_one] at hm
      linarith
    · have hexp : 2 ≤ a - j := by omega
      have hp2 : (2 / 3 : ℚ) ^ (a - j) ≤ (2 / 3) ^ 2 := pow_two_thirds_anti hexp
      have hp2' : (2 / 3 : ℚ) ^ 2 = 4 / 9 := by norm_num
      rw [hp2'] at hp2
      linarith
  constructor
  · have hge : ((3 / 2 : ℚ) ^ a) * loTile a ≤ ((3 / 2 : ℚ) ^ a) * x :=
      mul_le_mul_of_nonneg_left hlo (le_of_lt (pow_pos (by norm_num) a))
    rw [iterT0_eq]
    linarith [hge, hkeyLo]
  · have hlt : ((3 / 2 : ℚ) ^ a) * x < ((3 / 2 : ℚ) ^ a) * hiTile a :=
      mul_lt_mul_of_pos_left hhi (pow_pos (by norm_num) a)
    have hfin : ((3 / 2 : ℚ) ^ a) * hiTile a ≤ 1 / 2 := by
      have hle1 := mul_le_mul_of_nonneg_left hhi'
        (le_of_lt (pow_pos (show (0 : ℚ) < 3 / 2 by norm_num) a))
      linarith [hle1, hkeyA]
    rw [iterT0_eq]
    linarith

/-! ### Theorem 2: seamless tiling of `(0, 1/4)` -/

/-- Adjacent branch intervals touch exactly. -/
public theorem hiTile_succ_eq_loTile {a : ℕ} (ha : 1 ≤ a) : hiTile (a + 1) = loTile a := by
  unfold hiTile loTile
  have hle : (1 / 2 : ℚ) * ((2 / 3 : ℚ) ^ (a + 1)) ≤ 1 / 4 := by
    have hp : (2 / 3 : ℚ) ^ (a + 1) ≤ (2 / 3) ^ 2 :=
      pow_two_thirds_anti (show 2 ≤ a + 1 by omega)
    have hp' : (2 / 3 : ℚ) ^ 2 = 4 / 9 := by norm_num
    rw [hp'] at hp
    nlinarith [pow_two_thirds_pos (a + 1), hp]
  rw [min_eq_right hle, pow_succ]
  ring

/-- Each branch interval is non-empty and contained in `(0, 1/4]`. -/
public theorem hiTile_le_quarter (a : ℕ) : hiTile a ≤ 1 / 4 := min_le_left _ _

public theorem loTile_pos (a : ℕ) : 0 < loTile a := by
  unfold loTile
  positivity

public theorem loTile_lt_hiTile {a : ℕ} (ha : 1 ≤ a) : loTile a < hiTile a := by
  unfold loTile hiTile
  have hX : (0 : ℚ) < (2 / 3) ^ a := pow_two_thirds_pos a
  have hXle : (2 / 3 : ℚ) ^ a ≤ 2 / 3 := by
    have := pow_two_thirds_anti (j := 1) (a := a) ha
    simpa using this
  rcases le_total ((1 / 2 : ℚ) * ((2 / 3) ^ a)) (1 / 4) with h | h
  · rw [min_eq_right h]
    nlinarith
  · rw [min_eq_left h]
    nlinarith

/-- For `a ≥ 2` the truncation at `1/4` is inactive. -/
public theorem hiTile_eq_of_two_le {a : ℕ} (ha : 2 ≤ a) :
    hiTile a = (1 / 2 : ℚ) * ((2 / 3) ^ a) := by
  unfold hiTile
  have hp : (2 / 3 : ℚ) ^ a ≤ (2 / 3) ^ 2 := pow_two_thirds_anti ha
  have hle : (1 / 2 : ℚ) * ((2 / 3) ^ a) ≤ 1 / 4 := by
    nlinarith [pow_two_thirds_pos a]
  rw [min_eq_right hle]

/-! ### Theorem 3: mutual inverses -/

public theorem syracuseInv_syracuseMap (a : ℕ) (x : ℚ) :
    syracuseInv a (syracuseMap a x) = x := by
  unfold syracuseInv syracuseMap
  have h : ((3 / 2 : ℚ) ^ (a + 1)) * x - 1 / 2 + 1 / 2 = ((3 / 2 : ℚ) ^ (a + 1)) * x := by
    ring
  rw [h]
  have hc : ((2 / 3 : ℚ) ^ (a + 1)) * ((3 / 2 : ℚ) ^ (a + 1)) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hc, one_mul]

public theorem syracuseMap_syracuseInv (a : ℕ) (y : ℚ) :
    syracuseMap a (syracuseInv a y) = y := by
  unfold syracuseInv syracuseMap
  have hc : ((3 / 2 : ℚ) ^ (a + 1)) * ((2 / 3 : ℚ) ^ (a + 1)) = 1 := pow_cancel (a + 1)
  rw [← mul_assoc, hc, one_mul]
  ring

/-! ### Theorem 4: the `a ≥ 2` full-branch bijection -/

/-- For `a ≥ 2`, `syracuseMap a` is a bijection `[loTile a, hiTile a) → [0, 1/4)`. -/
public theorem syracuse_bijective {a : ℕ} (ha : 2 ≤ a) :
    (∀ x : ℚ, loTile a ≤ x → x < hiTile a → 0 ≤ syracuseMap a x ∧ syracuseMap a x < 1 / 4) ∧
      (∀ y : ℚ, 0 ≤ y → y < 1 / 4 →
        loTile a ≤ syracuseInv a y ∧ syracuseInv a y < hiTile a) := by
  have hhi := hiTile_eq_of_two_le ha
  constructor
  · intro x hlo hhi'
    constructor
    · have hmono : ((3 / 2 : ℚ) ^ (a + 1)) * loTile a ≤ ((3 / 2 : ℚ) ^ (a + 1)) * x :=
        mul_le_mul_of_nonneg_left hlo (le_of_lt (pow_pos (by norm_num) (a + 1)))
      have hkey := key_lo a
      unfold syracuseMap
      linarith
    · have hmono : ((3 / 2 : ℚ) ^ (a + 1)) * x < ((3 / 2 : ℚ) ^ (a + 1)) * ((1 / 2) * ((2 / 3) ^ a)) := by
        rw [← hhi]
        exact mul_lt_mul_of_pos_left hhi' (pow_pos (by norm_num) (a + 1))
      have hkey := key_hi a
      unfold syracuseMap
      linarith
  · intro y hy0 hyq
    constructor
    · have hkey : ((2 / 3 : ℚ) ^ (a + 1)) * (1 / 2) = loTile a := by
        unfold loTile
        rw [pow_succ]
        ring
      have hmono : ((2 / 3 : ℚ) ^ (a + 1)) * (1 / 2) ≤ ((2 / 3 : ℚ) ^ (a + 1)) * (y + 1 / 2) := by
        nlinarith [pow_two_thirds_pos (a + 1)]
      unfold syracuseInv
      linarith
    · have hkey : ((2 / 3 : ℚ) ^ (a + 1)) * (3 / 4) = (1 / 2) * ((2 / 3) ^ a) := by
        rw [pow_succ]
        ring
      have hmono : ((2 / 3 : ℚ) ^ (a + 1)) * (y + 1 / 2) < ((2 / 3 : ℚ) ^ (a + 1)) * (3 / 4) := by
        nlinarith [pow_two_thirds_pos (a + 1)]
      unfold syracuseInv
      rw [hhi]
      linarith [hmono, hkey]

/-! ### Theorem 5: the truncated `a = 1` branch and the forced `b ≥ 5` gap -/

public theorem loTile_one : loTile 1 = 2 / 9 := by
  unfold loTile
  norm_num

public theorem hiTile_one : hiTile 1 = 1 / 4 := by
  unfold hiTile
  norm_num

/-- The `a = 1` branch maps `[2/9, 1/4)` bijectively onto `[0, 1/16)`. -/
public theorem one_branch_bijective :
    (∀ x : ℚ, 2 / 9 ≤ x → x < 1 / 4 → 0 ≤ syracuseMap 1 x ∧ syracuseMap 1 x < 1 / 16) ∧
      (∀ y : ℚ, 0 ≤ y → y < 1 / 16 → 2 / 9 ≤ syracuseInv 1 y ∧ syracuseInv 1 y < 1 / 4) := by
  constructor
  · intro x hlo hhi
    constructor <;> unfold syracuseMap <;> norm_num at * <;> linarith
  · intro y hy0 hy1
    constructor <;> unfold syracuseInv <;> norm_num at * <;> linarith

public theorem one_sixteenth_lt_loTile_four : (1 / 16 : ℚ) < loTile 4 := by
  unfold loTile
  norm_num

public theorem loTile_five_lt_one_sixteenth : loTile 5 < (1 / 16 : ℚ) := by
  unfold loTile
  norm_num

/-- **Forced gap**: after the truncated `a = 1` branch the image is still below `1/16`, while
`loTile b > 1/16` for every `b ∈ {1, 2, 3, 4}`; hence the next branch index cannot be `1..4`
and must be at least `5`. -/
public theorem force_b_ge_five {x : ℚ} (hlo : 2 / 9 ≤ x) (hhi : x < 1 / 4)
    {b : ℕ} (_hb1 : 1 ≤ b) (hb4 : b ≤ 4) : syracuseMap 1 x < loTile b := by
  have himg := (one_branch_bijective.1 x hlo hhi).2
  have hanti : loTile 4 ≤ loTile b := by
    unfold loTile
    have h := pow_two_thirds_anti hb4
    nlinarith [pow_two_thirds_pos b]
  have hlt := one_sixteenth_lt_loTile_four
  linarith

end Mahler32.SyracuseBijection

end
