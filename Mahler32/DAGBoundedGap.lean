/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Task 5 — a bounded-gap DAG certificate modulo `128`

The Mahler `Z`-step on odd/even inputs is

`zStep g = (3 * g + g % 2) / 2`.

Working modulo `128`, the legal residue set `S7` of the seven-step `Z`-words has `27` elements,
and `R7 = {0, 4, 94, 120}` is the set of "collision" residues.  The orbit of any `g ∈ S7`
reaches `R7` in at most `11` steps.  The certificate is the explicit depth function
`dagDepth`, i.e. the first time the orbit meets `R7`; every claim is a finite computation and
is discharged by evaluation.
-/

public section

namespace Mahler32.DAGBoundedGap

/-- Embed a natural number into `Fin 128` by reduction. -/
@[expose] public def embed128 (n : ℕ) : Fin 128 := ⟨n % 128, Nat.mod_lt _ (by norm_num)⟩

/-- The Mahler `Z`-step on residues modulo `128`. -/
@[expose] public def zStep (g : Fin 128) : Fin 128 :=
  embed128 ((3 * g.val + g.val % 2) / 2)

/-- The collision set `R7 = {0, 4, 94, 120}`. -/
@[expose] public def R7 : Finset (Fin 128) :=
  ([0, 4, 94, 120].map embed128).toFinset

/-- The `27` legal seven-step `Z`-word residues modulo `128`. -/
@[expose] public def S7 : Finset (Fin 128) :=
  ([0, 4, 10, 15, 23, 28, 35, 42, 50, 53, 56, 61, 63, 69, 75, 80, 84, 85, 88, 92, 94, 95,
    104, 113, 120, 126, 127].map embed128).toFinset

/-- `n`-fold iteration of the `Z`-step. -/
@[expose] public def iterZ : ℕ → Fin 128 → Fin 128
  | 0, g => g
  | n + 1, g => iterZ n (zStep g)

/-- The first time the orbit meets `R7` (capped at `12`, a value never used inside `S7`). -/
@[expose] public def dagDepth (g : Fin 128) : ℕ :=
  ((List.range 12).find? (fun n => decide (iterZ n g ∈ R7))).getD 12

/-- `S7` really has `27` elements. -/
public theorem S7_card : S7.card = 27 := by
  decide

/-- `R7` really has `4` elements. -/
public theorem R7_card : R7.card = 4 := by
  decide

set_option maxRecDepth 100000

/-- Every element of `S7` reaches `R7` within `11` steps, and `dagDepth` is the exact hitting
time. -/
public theorem dag_depth_le :
    ∀ g : Fin 128, g ∈ S7 → dagDepth g ≤ 11 ∧ iterZ (dagDepth g) g ∈ R7 := by
  decide

/-- **Bounded gap.**  Any `Z`-orbit starting in `S7` collides with `R7` in at most `11` steps. -/
public theorem dag_bounded_gap (g : Fin 128) (hg : g ∈ S7) :
    ∃ n ≤ 11, iterZ n g ∈ R7 :=
  ⟨dagDepth g, (dag_depth_le g hg).1, (dag_depth_le g hg).2⟩

end Mahler32.DAGBoundedGap
