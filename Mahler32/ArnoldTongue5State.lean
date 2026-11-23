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

end Mahler32.ArnoldTongue5State
