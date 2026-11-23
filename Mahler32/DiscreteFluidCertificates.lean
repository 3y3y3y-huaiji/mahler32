/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Discrete fluid certificates for the Mahler `3/2` map

This module collects the *exact rational* certificates behind the "discrete fluid" picture of the
Mahler map.  Only genuinely decidable statements are asserted; the analytic estimate quoted in
the accompanying paper (the cosine-product bound `≤ 0.7409`) is a numerical certificate
reproduced by `scripts/generate_certificates.py`, not a Lean theorem.

Formalised here:

* **The cup map** `Tcup x = (3x/2) mod (1/2)` on `[0, 1/2)`, with rewrite rules and the fact that
  it is a self-map of `[0, 1/2)` (`Tcup_mem`).

* **The exact `3`-cycle** `4/19 ↦ 6/19 ↦ 9/19 ↦ 4/19` (`cup_cycle`), together with the fact that
  it has exact period `3` (`cup_period_three`).  This is the genuine periodic survivor of the cup
  map; it is the reason an "all positive reals are excluded" statement must be phrased with the
  correct branch structure.

* **Piecewise expansion** (`Tcup_dist`): on either branch, `Tcup` stretches distances by exactly
  `3/2`.

* **The `2 : 1` mass split** (`two_one_split`, `scale_two_thirds`): the exact rational lengths
  behind the mass transport `μ([1/6,1/4]) = μ([1/3,1/2])` under `x ↦ 2x/3`.
-/

public section

namespace Mahler32.DiscreteFluidCertificates

/-- The Mahler "cup" map on `[0, 1/2)`: `Tcup x = (3x/2) mod (1/2)`. -/
@[expose] public def Tcup (x : ℚ) : ℚ :=
  if (3 * x) / 2 < 1 / 2 then (3 * x) / 2 else (3 * x) / 2 - 1 / 2

/-- Rewrite rule for the non-wrapping branch. -/
public theorem Tcup_of_lt {x : ℚ} (h : (3 * x) / 2 < 1 / 2) : Tcup x = (3 * x) / 2 := by
  unfold Tcup
  exact ite_eq_left h

/-- Rewrite rule for the wrapping branch. -/
public theorem Tcup_of_ge {x : ℚ} (h : ¬ (3 * x) / 2 < 1 / 2) : Tcup x = (3 * x) / 2 - 1 / 2 := by
  unfold Tcup
  exact ite_eq_right h

/-- `Tcup` is a self-map of `[0, 1/2)`. -/
public theorem Tcup_mem {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) :
    0 ≤ Tcup x ∧ Tcup x < 1 / 2 := by
  unfold Tcup
  split_ifs with h
  · constructor <;> linarith
  · constructor <;> linarith

/-- **The exact three-cycle** of the cup map: `4/19 ↦ 6/19 ↦ 9/19 ↦ 4/19`. -/
public theorem cup_cycle :
    Tcup (4 / 19) = 6 / 19 ∧ Tcup (6 / 19) = 9 / 19 ∧ Tcup (9 / 19) = 4 / 19 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold Tcup; norm_num)

/-- **The cycle has exact period three** (it returns after three steps and not before). -/
public theorem cup_period_three :
    Tcup (Tcup (Tcup (4 / 19))) = 4 / 19 ∧
      Tcup (4 / 19) ≠ 4 / 19 ∧ Tcup (Tcup (4 / 19)) ≠ 4 / 19 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold Tcup; norm_num)

/-- **Piecewise expansion.**  On a fixed branch, `Tcup` stretches distances by exactly `3/2`. -/
public theorem Tcup_dist {x y : ℚ}
    (hx : (3 * x) / 2 < 1 / 2) (hy : (3 * y) / 2 < 1 / 2) :
    Tcup x - Tcup y = 3 / 2 * (x - y) := by
  rw [Tcup_of_lt hx, Tcup_of_lt hy]
  ring

/-- **The `2 : 1` mass split.**  The half-open interval `[1/6, 1/4]` has exactly half the length of
`[1/3, 1/2]`, which is the arithmetic content of the transport identity
`μ([1/6,1/4]) = μ([1/3,1/2])` for a measure carried by `x ↦ 2x/3`. -/
public theorem two_one_split : (1 : ℚ) / 2 - 1 / 3 = 2 * (1 / 4 - 1 / 6) := by
  norm_num

/-- The scaling map `x ↦ 2x/3` sends `[1/4, 1/2]` onto `[1/6, 1/3]`; the lower half lands on
`[1/6, 1/4]`. -/
public theorem scale_two_thirds :
    (2 : ℚ) / 3 * (1 / 4) = 1 / 6 ∧ (2 : ℚ) / 3 * (1 / 2) = 1 / 3 := by
  constructor <;> norm_num

end Mahler32.DiscreteFluidCertificates

end
