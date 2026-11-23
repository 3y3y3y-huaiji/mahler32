/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mahler32.Basic

/-!
# Task 1 — the base-`6` light cone

This module restates the base-`6` state machine and the light-cone flip theorem using the
task-sheet definitions (`step a = (3*a+1)/2`, `iterStep`, `bstep y = (2*y)/3`, `good`), and
proves them against the corresponding results of `Mahler32.Basic`.

Naming is intentionally independent of `Mahler32.Basic` (`Mahler32.Base6LightCone.*`), so the
two files can coexist.
-/

public section

namespace Mahler32.Base6LightCone

/-- One step of the `3/2` map, in the ceiling-free integer form `(3a+1)/2`. -/
@[expose] public def step (a : ℕ) : ℕ := (3 * a + 1) / 2

/-- The `k`-fold iterate of `step`. -/
@[expose] public def iterStep : ℕ → ℕ → ℕ
  | 0, a => a
  | k + 1, a => iterStep k (step a)

/-- Reverse branch: undo one ternary digit. -/
@[expose] public def bstep (y : ℕ) : ℕ := (2 * y) / 3

/-- The reverse branch is legal for `k` steps when no intermediate value is `≡ 1 (mod 3)`. -/
@[expose] public def good (k y : ℕ) : Prop := ∀ j, j < k → (bstep^[j] y) % 3 ≠ 1

@[simp] public lemma iterStep_zero (a : ℕ) : iterStep 0 a = a := rfl

@[simp] public lemma iterStep_succ (k a : ℕ) : iterStep (k + 1) a = iterStep k (step a) := rfl

/-- The task-sheet `step` agrees with the ceiling form used in `Mahler32.Basic`. -/
public lemma step_eq (a : ℕ) : step a = Mahler32.step a := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Mahler32.two_cases a <;> unfold step Mahler32.step <;> omega

/-- `iterStep` is iteration of the same map. -/
public lemma iterStep_eq (k a : ℕ) : iterStep k a = Mahler32.step^[k] a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [iterStep_succ, step_eq a, ih (Mahler32.step a)]
    exact (Function.iterate_succ_apply Mahler32.step k a).symm

/-! ### Theorem 1: the ternary last-digit ban and the base-`6` split -/

/-- The next term is never `≡ 1 (mod 3)`. -/
public theorem step_mod_three_ne_one (a : ℕ) : step a % 3 ≠ 1 := by
  rw [step_eq, Mahler32.step_mod_three]
  omega

/-- The last base-`6` digit of the next term lies in `{0, 2, 3, 5}`. -/
public theorem step_mod_six_mem (a : ℕ) :
    step a % 6 = 0 ∨ step a % 6 = 2 ∨ step a % 6 = 3 ∨ step a % 6 = 5 := by
  have h3 : step a % 3 = 2 * (a % 2) := by rw [step_eq, Mahler32.step_mod_three]
  have hmod : step a % 6 % 3 = step a % 3 := Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 6)
  have hlt : step a % 6 < 6 := Nat.mod_lt _ (by norm_num)
  omega

/-- Even input forces the last base-`6` digit into `{0, 3}`. -/
public theorem step_mod_six_of_even {a : ℕ} (ha : a % 2 = 0) :
    step a % 6 = 0 ∨ step a % 6 = 3 := by
  have h3 : step a % 3 = 0 := by simp [step_eq, Mahler32.step_mod_three, ha]
  have hmod : step a % 6 % 3 = step a % 3 := Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 6)
  have hlt : step a % 6 < 6 := Nat.mod_lt _ (by norm_num)
  omega

/-- Odd input forces the last base-`6` digit into `{2, 5}`. -/
public theorem step_mod_six_of_odd {a : ℕ} (ha : a % 2 = 1) :
    step a % 6 = 2 ∨ step a % 6 = 5 := by
  have h3 : step a % 3 = 2 := by simp [step_eq, Mahler32.step_mod_three, ha]
  have hmod : step a % 6 % 3 = step a % 3 := Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 6)
  have hlt : step a % 6 < 6 := Nat.mod_lt _ (by norm_num)
  omega

/-! ### Theorem 2: the base-`6` local parity law -/

/-- With `d₀ = a % 6`, `t₀ = d₀ / 2`, `b₁ = (a / 6) % 2`, one has
`step a % 2 = (t₀ + b₁) % 2`. -/
public theorem step_parity_hex (a : ℕ) :
    step a % 2 = ((a % 6) / 2 + a / 6 % 2) % 2 := by
  rw [step_eq, Mahler32.step_parity_hex]

/-! ### Theorem 3: the light-cone flip -/

/-- Single-step affine law: shifting by `2*m` shifts `step` by `3*m`. -/
public theorem step_add_two_mul (a m : ℕ) : step (a + 2 * m) = step a + 3 * m := by
  rw [step_eq (a + 2 * m), step_eq a]
  simpa using Mahler32.step_shift 0 m a

/-- Multi-step affine law: shifting by `2^k*c` shifts `iterStep k` by `3^k*c`. -/
public theorem iterStep_add_two_pow (k a c : ℕ) :
    iterStep k (a + 2 ^ k * c) = iterStep k a + 3 ^ k * c := by
  rw [iterStep_eq, iterStep_eq, Mahler32.step_pow_shift k k le_rfl c a]
  simp

/-- Base-`6` growth: shifting by `6^k` shifts `iterStep k` by `9^k`. -/
public theorem iterStep_add_six_pow (k a : ℕ) :
    iterStep k (a + 6 ^ k) = iterStep k a + 9 ^ k := by
  rw [iterStep_eq, iterStep_eq, Mahler32.step_pow_add_six_pow]

/-- **Light-cone flip**: adding `6^k` always flips the parity after `k` steps. -/
public theorem light_cone_flip (k a : ℕ) :
    iterStep k (a + 6 ^ k) % 2 ≠ iterStep k a % 2 := by
  rw [iterStep_eq, iterStep_eq]
  exact Mahler32.light_cone_flip_hex k a

/-! ### Theorem 4: the 3-adic reverse window -/

/-- Reverse branch under a shift by `3*m`. -/
public lemma bstep_add_three_mul (y m : ℕ) : bstep (y + 3 * m) = bstep y + 2 * m := by
  unfold bstep
  have h : 2 * (y + 3 * m) = 2 * y + (2 * m) * 3 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 3)]

/-- Reverse branch under a shift by `3^(j+1)`. -/
public lemma bstep_add_three_pow (j t y : ℕ) :
    bstep (y + 3 ^ (j + 1) * t) = bstep y + 3 ^ j * (2 * t) := by
  have h : 3 ^ (j + 1) * t = 3 * (3 ^ j * t) := by rw [pow_succ]; ring
  rw [h, bstep_add_three_mul]
  ring

/-- Iterated reverse-branch shift. -/
public theorem bstep_pow_add_three_pow (m k : ℕ) (hk : k ≤ m) (t y : ℕ) :
    bstep^[k] (y + 3 ^ m * t) = bstep^[k] y + 3 ^ (m - k) * (2 ^ k * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ m := by omega
    rw [Function.iterate_succ_apply', ih hk', Function.iterate_succ_apply']
    have hshift := bstep_add_three_pow (m - k - 1) (2 ^ k * t) (bstep^[k] y)
    have hd : m - k - 1 + 1 = m - k := by omega
    rw [hd] at hshift
    rw [hshift]
    have harith : 3 ^ (m - k - 1) * (2 * (2 ^ k * t)) =
        3 ^ (m - (k + 1)) * (2 ^ (k + 1) * t) := by
      rw [show m - k - 1 = m - (k + 1) from by omega, pow_succ]
      ring
    rw [harith]

/-- The first `k` reverse digits are invariant under a shift by `3^k`. -/
public lemma bstep_pow_mod_three_of_lt {k j : ℕ} (hj : j < k) (t y : ℕ) :
    (bstep^[j] (y + 3 ^ k * t)) % 3 = (bstep^[j] y) % 3 := by
  rw [bstep_pow_add_three_pow k j (by omega) t y]
  obtain ⟨d, hd⟩ : ∃ d, k - j = d + 1 := ⟨k - j - 1, by omega⟩
  have hcomm : 3 ^ (k - j) * (2 ^ j * t) = (3 ^ d * (2 ^ j * t)) * 3 := by
    rw [hd, pow_succ]; ring
  rw [hcomm, Nat.add_mul_mod_self_right]

/-- `k`-step legality is invariant under shifts by `3^k`. -/
public theorem good_add_three_pow (k t y : ℕ) : good k (y + 3 ^ k * t) ↔ good k y := by
  constructor
  · intro h j hj
    have hmod := bstep_pow_mod_three_of_lt hj t y
    exact hmod ▸ h j hj
  · intro h j hj
    have hmod := bstep_pow_mod_three_of_lt hj t y
    exact hmod.symm ▸ h j hj

/-- Legality depends only on `y % 3^k`. -/
public theorem good_mod_iff (k y : ℕ) : good k y ↔ good k (y % 3 ^ k) := by
  conv_lhs => rw [← Nat.mod_add_div y (3 ^ k)]
  exact good_add_three_pow k (y / 3 ^ k) (y % 3 ^ k)

end Mahler32.Base6LightCone

end
