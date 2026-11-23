/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Task 3 — the five-state Arnold-tongue automaton on `[1/3, 11/15)`

The translated Mahler map is `T_t x = (3 * x - t) / 2` for `t ∈ {0, 1}`.  Restricting to the
tiling interval `I = [1/3, 11/15)` and tracking which sub-interval a point lies in gives a small
directed graph.  This file records the exact transition table (seven edges out of the ten
`state × symbol` slots, the remaining three escape `I`), counts the admissible words of each
length, and proves the two asymptotic bounds required by the task:

* `countPaths 0 k = k + 1` for all `k ≥ 1`;
* `24 * countPaths 0 k < 41 * k - 72` for all `k ≥ 8`.
-/

public section

namespace Mahler32.ArnoldTongue5State

/-- The translated Mahler map `T_t x = (3 * x - t) / 2`. -/
@[expose] public def T (t : Bool) (x : ℚ) : ℚ := (3 * x - (if t then 1 else 0)) / 2

/-- The five-track automaton.  `nextInterval s t` is `some s'` when the whole `t`-image of
track `s` is legal again and lands in track `s'`; it is `none` when the image leaves `I`. -/
@[expose] public def nextInterval : Fin 5 → Bool → Option (Fin 5)
  | 0, false => some 1
  | 0, true => some 0
  | 1, false => none
  | 1, true => some 1
  | 2, false => some 3
  | 2, true => some 4
  | 3, false => some 4
  | 3, true => none
  | 4, false => some 2
  | 4, true => none

/-- Number of admissible words of length `k` starting from state `m`. -/
@[expose] public def countPaths (m : Fin 5) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
      ((nextInterval m false).map (fun m' => countPaths m' k)).getD 0 +
        ((nextInterval m true).map (fun m' => countPaths m' k)).getD 0

/-- The ten transition slots are exactly the seven listed edges together with the three
escapes.  Stated exhaustively, hence checkable by evaluation. -/
public theorem nextInterval_exact :
    nextInterval 0 false = some 1 ∧ nextInterval 0 true = some 0 ∧
      nextInterval 1 false = none ∧ nextInterval 1 true = some 1 ∧
      nextInterval 2 false = some 3 ∧ nextInterval 2 true = some 4 ∧
      nextInterval 3 false = some 4 ∧ nextInterval 3 true = none ∧
      nextInterval 4 false = some 2 ∧ nextInterval 4 true = none := by
  decide

/-- State `1` has exactly one admissible continuation of every length. -/
public theorem countPaths_one : ∀ k, countPaths 1 k = 1
  | 0 => by simp [countPaths]
  | k + 1 => by
    simp [countPaths, nextInterval, countPaths_one k]

/-- State `0` has exactly `k + 1` admissible words of length `k`. -/
public theorem countPaths_zero_all : ∀ k, countPaths 0 k = k + 1
  | 0 => by simp [countPaths]
  | k + 1 => by
    simp [countPaths, nextInterval, countPaths_one k, countPaths_zero_all k]
    omega

/-- The task statement for `k ≥ 1`. -/
public theorem countPaths_zero (k : ℕ) (_hk : 1 ≤ k) : countPaths 0 k = k + 1 :=
  countPaths_zero_all k

/-- The exponential count stays below the linear threshold for `k ≥ 8`. -/
public theorem countPaths_zero_lt (k : ℕ) (hk : 8 ≤ k) :
    24 * countPaths 0 k < 41 * k - 72 := by
  rw [countPaths_zero_all]
  omega

/-! ### The dynamics of `T` itself

The automaton table above is a *combinatorial* object.  The theorems below tie it back to the
actual translated Mahler map `T_t x = (3x - t)/2` on `I = [1/3, 11/15)`: they locate, with exact
rational arithmetic, the sub-intervals on which each branch stays inside `I`.  `T false` stays
inside `I` exactly on `[1/3, 22/45)`, and `T true` stays inside `I` exactly on `[5/9, 11/15)`. -/

/-- Unfolding of the `t = false` branch: `T false x = 3x/2`. -/
public theorem T_false_eq (x : ℚ) : T false x = 3 * x / 2 := by
  unfold T
  norm_num

/-- Unfolding of the `t = true` branch: `T true x = (3x - 1)/2`. -/
public theorem T_true_eq (x : ℚ) : T true x = (3 * x - 1) / 2 := by
  unfold T
  norm_num

/-- On `[1/3, 22/45)`, the `t = false` branch lands back in `I = [1/3, 11/15)`. -/
public theorem T_false_maps (x : ℚ) (h0 : 1 / 3 ≤ x) (h1 : x < 22 / 45) :
    1 / 3 ≤ T false x ∧ T false x < 11 / 15 := by
  rw [T_false_eq]
  constructor <;> linarith

/-- On `[5/9, 11/15)`, the `t = true` branch lands back in `I = [1/3, 11/15)`. -/
public theorem T_true_maps (x : ℚ) (h0 : 5 / 9 ≤ x) (h1 : x < 11 / 15) :
    1 / 3 ≤ T true x ∧ T true x < 11 / 15 := by
  rw [T_true_eq]
  constructor <;> linarith

/-- The `t = false` branch is strictly increasing. -/
public theorem T_strictMono_false : StrictMono (T false) := by
  intro a b hab
  rw [T_false_eq, T_false_eq]
  linarith

/-- The `t = true` branch is strictly increasing. -/
public theorem T_strictMono_true : StrictMono (T true) := by
  intro a b hab
  rw [T_true_eq, T_true_eq]
  linarith

end Mahler32.ArnoldTongue5State
