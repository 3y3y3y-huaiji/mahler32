/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Task 4 — the seven-state centred Arnold-tongue automaton on `[7/24, 17/24)`

For the centred interval `I = [7/24, 17/24)` and `T_t x = (3 * x - t) / 2`, the refined tiling
has seven tracks and ten directed edges.  The number of admissible words of length `k` starting
from the initial track grows exactly linearly:

`countPaths7 0 k = 2 * k`   for all `k ≥ 1`.
-/

public section

namespace Mahler32.ArnoldTongue7State

/-- The translated Mahler map `T_t x = (3 * x - t) / 2`. -/
@[expose] public def T (t : Bool) (x : ℚ) : ℚ := (3 * x - (if t then 1 else 0)) / 2

/-- The seven-track automaton with its ten edges. -/
@[expose] public def nextInterval7 : Fin 7 → Bool → Option (Fin 7)
  | 0, false => some 1
  | 0, true => some 0
  | 1, false => some 3
  | 1, true => some 2
  | 2, false => some 2
  | 2, true => none
  | 3, false => none
  | 3, true => some 3
  | 4, false => some 5
  | 4, true => some 6
  | 5, false => some 4
  | 5, true => none
  | 6, false => none
  | 6, true => some 5

/-- Number of admissible words of length `k` starting from state `m`. -/
@[expose] public def countPaths7 (m : Fin 7) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
      ((nextInterval7 m false).map (fun m' => countPaths7 m' k)).getD 0 +
        ((nextInterval7 m true).map (fun m' => countPaths7 m' k)).getD 0

/-- The fourteen transition slots of the seven tracks. -/
public theorem nextInterval7_exact :
    nextInterval7 0 false = some 1 ∧ nextInterval7 0 true = some 0 ∧
      nextInterval7 1 false = some 3 ∧ nextInterval7 1 true = some 2 ∧
      nextInterval7 2 false = some 2 ∧ nextInterval7 2 true = none ∧
      nextInterval7 3 false = none ∧ nextInterval7 3 true = some 3 ∧
      nextInterval7 4 false = some 5 ∧ nextInterval7 4 true = some 6 ∧
      nextInterval7 5 false = some 4 ∧ nextInterval7 5 true = none ∧
      nextInterval7 6 false = none ∧ nextInterval7 6 true = some 5 := by
  decide

public theorem countPaths7_two : ∀ k, countPaths7 2 k = 1
  | 0 => by simp [countPaths7]
  | k + 1 => by
    simp [countPaths7, nextInterval7, countPaths7_two k]

public theorem countPaths7_three : ∀ k, countPaths7 3 k = 1
  | 0 => by simp [countPaths7]
  | k + 1 => by
    simp [countPaths7, nextInterval7, countPaths7_three k]

/-- State `1` has exactly two admissible words of every positive length. -/
public theorem countPaths7_one : ∀ k, 1 ≤ k → countPaths7 1 k = 2
  | 0, hk => by omega
  | 1, _ => by decide
  | k + 2, _ => by
    have e : countPaths7 1 (k + 2) = countPaths7 3 (k + 1) + countPaths7 2 (k + 1) := rfl
    rw [e, countPaths7_three (k + 1), countPaths7_two (k + 1)]

/-- Main count: the initial track has exactly `2 * k` admissible words of length `k`. -/
public theorem countPaths7_zero : ∀ k, 1 ≤ k → countPaths7 0 k = 2 * k
  | 0, hk => by omega
  | 1, _ => by decide
  | k + 2, _ => by
    have e : countPaths7 0 (k + 2) = countPaths7 1 (k + 1) + countPaths7 0 (k + 1) := rfl
    rw [e, countPaths7_one (k + 1) (by omega), countPaths7_zero (k + 1) (by omega)]
    omega

/-! ### The dynamics of `T` itself

With `I = [7/24, 17/24)`, the translated Mahler branches `T_t x = (3x - t)/2` stay inside `I`
exactly on `[7/24, 17/36)` (`t = false`) and on `[19/36, 17/24)` (`t = true`).  These exact
rational windows are the dynamical content the automaton abstracts. -/

/-- Unfolding of the `t = false` branch: `T false x = 3x/2`. -/
public theorem T_false_eq (x : ℚ) : T false x = 3 * x / 2 := by
  unfold T
  norm_num

/-- Unfolding of the `t = true` branch: `T true x = (3x - 1)/2`. -/
public theorem T_true_eq (x : ℚ) : T true x = (3 * x - 1) / 2 := by
  unfold T
  norm_num

/-- On `[7/24, 17/36)`, the `t = false` branch lands back in `I = [7/24, 17/24)`. -/
public theorem T_false_maps (x : ℚ) (h0 : 7 / 24 ≤ x) (h1 : x < 17 / 36) :
    7 / 24 ≤ T false x ∧ T false x < 17 / 24 := by
  rw [T_false_eq]
  constructor <;> linarith

/-- On `[19/36, 17/24)`, the `t = true` branch lands back in `I = [7/24, 17/24)`. -/
public theorem T_true_maps (x : ℚ) (h0 : 19 / 36 ≤ x) (h1 : x < 17 / 24) :
    7 / 24 ≤ T true x ∧ T true x < 17 / 24 := by
  rw [T_true_eq]
  constructor <;> linarith

end Mahler32.ArnoldTongue7State
