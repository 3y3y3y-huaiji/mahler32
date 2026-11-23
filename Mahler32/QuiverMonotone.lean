/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

-- Mirror of mathlib4#44885, replace with `import Mathlib.Combinatorics.Quiver.Monotone`
-- once upstream is merged.  The repository is pinned to Mathlib v4.36.0, which does not yet
-- contain that file, so this module reproduces its exact namespace and theorem signatures.
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Order.Defs.PartialOrder

/-!
# Monotonicity along quiver paths

This file defines `Quiver.Monotone` and `Quiver.StrictMono` for functions from the vertices
of a quiver into a preorder, and proves that `Quiver.Reachable` is a partial order when a
strictly monotone function exists.

`QuiverMonotone` is a *verbatim mirror* of `Mathlib/Combinatorics/Quiver/Monotone.lean` from
[mathlib4#44885](https://github.com/leanprover-community/mathlib4/pull/44885).  When that PR is
merged and the toolchain is bumped, delete this file and replace every `import Mahler32.QuiverMonotone`
by `import Mathlib.Combinatorics.Quiver.Monotone`.
-/

public section

namespace Quiver

variable {V : Type*} [Quiver V] {α : Type*} [Preorder α] {f : V → α}

/-- A function from the vertices of a quiver to a preorder is monotone if every arrow
`a ⟶ b` gives `f a ≤ f b`. -/
@[expose] public def Monotone (f : V → α) : Prop :=
  ∀ ⦃a b : V⦄, (a ⟶ b) → f a ≤ f b

/-- A function from the vertices of a quiver to a preorder is strictly monotone if every arrow
`a ⟶ b` gives `f a < f b`. -/
@[expose] public def StrictMono (f : V → α) : Prop :=
  ∀ ⦃a b : V⦄, (a ⟶ b) → f a < f b

public theorem StrictMono.monotone (hf : StrictMono f) : Monotone f :=
  fun _ _ e ↦ le_of_lt (hf e)

public theorem Monotone.le_of_path (hf : Monotone f) {a b : V} (p : Path a b) : f a ≤ f b := by
  induction p with
  | nil => rfl
  | cons _ e ih => exact le_trans ih (hf e)

public theorem StrictMono.lt_of_path (hf : StrictMono f) {a b : V} (p : Path a b)
    (hp : 0 < p.length) : f a < f b := by
  cases p with
  | nil => cases hp
  | cons q e => exact lt_of_le_of_lt (hf.monotone.le_of_path q) (hf e)

public theorem StrictMono.path_eq_nil (hf : StrictMono f) {a : V} (p : Path a a) : p = .nil := by
  cases p with
  | nil => rfl
  | cons q e => exact absurd (hf.lt_of_path (q.cons e) (Nat.succ_pos _)) (lt_irrefl _)

public theorem Monotone.le_of_reachable (hf : Monotone f) {a b : V} (hab : Reachable a b) :
    f a ≤ f b :=
  hab.elim hf.le_of_path

public theorem StrictMono.antisymm_reachable (hf : StrictMono f) {a b : V}
    (hab : Reachable a b) (hba : Reachable b a) : a = b := by
  obtain ⟨p⟩ := hab
  obtain ⟨q⟩ := hba
  have hlen : (p.comp q).length = 0 := congr_arg Path.length (hf.path_eq_nil (p.comp q))
  rw [Path.length_comp] at hlen
  exact p.eq_of_length_zero (Nat.eq_zero_of_add_eq_zero_right hlen)

public theorem StrictMono.isPartialOrder_reachable (hf : StrictMono f) : IsPartialOrder V Reachable where
  antisymm _ _ := hf.antisymm_reachable

end Quiver
