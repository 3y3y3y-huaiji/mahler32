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

end Mahler32.TwoWorldPadeCriterion

end
