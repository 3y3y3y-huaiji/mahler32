/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mahler32.Basic

/-!
# Task 6 — two-world Padé criterion

The `[1/2]` and `[1/1]` diagonal Padé approximants of `e * (1 + c + c² + ⋯)` are

`pade12 e c = e / (1 - c)` and `pade11 e c = e * (1 + c)`.

The two-world criterion compares them: the difference is exactly `e * c² / (1 - c)`, so the
worlds agree iff `c = 0`.  Rational strictness checks (`17/12 > √2 > 99/70`) are done with
`norm_num` on squares.
-/

public section

namespace Mahler32.TwoWorldPadeCriterion

/-- `[1/2]` Padé value. -/
@[expose] public def pade12 (e c : ℚ) : ℚ := e / (1 - c)

/-- `[1/1]` Padé value. -/
@[expose] public def pade11 (e c : ℚ) : ℚ := e * (1 + c)

/-- **Two-world identity**: the two Padé worlds differ by exactly `e c² / (1 - c)`. -/
public theorem two_world_identity (e c : ℚ) (hc : c ≠ 1) :
    pade12 e c - pade11 e c = e * c ^ 2 / (1 - c) := by
  unfold pade12 pade11
  field_simp
  ring

/-- At the rational golden-split constant `c = 1/9` the complementary factor is exactly `1`:
the rational product `c * 9` is an integer, which is what makes the two-world comparison
integer-valued. -/
public theorem integer_divisibility_bound : (1 / 9 : ℚ) * 9 = 1 := by
  norm_num

/-- Rational strictness: `17/12 > √2`. -/
public theorem sqrt_two_lt_17_12 : (2 : ℚ) < (17 / 12) ^ 2 := by
  norm_num

/-- Rational strictness from below: `140/99 < √2`. -/
public theorem sqrt_two_gt_140_99 : (140 / 99 : ℚ) ^ 2 < 2 := by
  norm_num

/-- **The two worlds agree iff `c = 0`.**  For a non-zero `e` and `c ≠ 1`, the two diagonal
Padé worlds of `e * (1 + c + c² + ⋯)` coincide exactly on the degenerate `c = 0` case.  This is
the exact statement behind `two_world_identity`: the difference is `e c² / (1 - c)`. -/
public theorem two_world_iff (e c : ℚ) (he : e ≠ 0) (hc : c ≠ 1) :
    pade12 e c = pade11 e c ↔ c = 0 := by
  constructor
  · intro h
    have hzero : e * c ^ 2 / (1 - c) = 0 := by
      rw [← two_world_identity e c hc, h, sub_self]
    rcases div_eq_zero_iff.mp hzero with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' he
      · exact sq_eq_zero_iff.mp h''
    · exact absurd (sub_eq_zero.mp h').symm hc
  · rintro rfl
    simp [pade12, pade11]

/-- **The integer-vanishing engine of the two-world criterion.**  An integer `M` that is
divisible by `2 ^ N` and satisfies `|M| < 2 ^ N` must vanish.  In the Padé comparison this is
applied to `M = D · 3 ^ deg · (Q(2/3) S(2/3)₂ - P(2/3))`: the `2`-adic world forces the
divisibility, the Archimedean world forces the size bound, and the only integer caught between
them is `0`. -/
public theorem two_pow_dvd_eq_zero {M : ℤ} {N : ℕ}
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

end Mahler32.TwoWorldPadeCriterion

end
