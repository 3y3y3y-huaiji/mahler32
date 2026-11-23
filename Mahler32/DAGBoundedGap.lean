/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib
public import Mahler32.QuiverMonotone

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

set_option maxRecDepth 1000

/-- Every element of `S7` reaches `R7` within `11` steps, and `dagDepth` is the exact hitting
time. -/
public theorem dag_depth_le :
    ∀ g : Fin 128, g ∈ S7 → dagDepth g ≤ 11 ∧ iterZ (dagDepth g) g ∈ R7 := by
  decide

/-- **Bounded gap.**  Any `Z`-orbit starting in `S7` collides with `R7` in at most `11` steps. -/
public theorem dag_bounded_gap (g : Fin 128) (hg : g ∈ S7) :
    ∃ n ≤ 11, iterZ n g ∈ R7 :=
  ⟨dagDepth g, (dag_depth_le g hg).1, (dag_depth_le g hg).2⟩

/-! ### The `g + 128` carry branch

The residue computation above lives in `Fin 128`.  On genuine naturals one `Z`-step below the
modulus shifts by `192 = 128 + 64` (`zStepNat_add_128`), so a successor residue is either
`zStep g` or `zStep g + 64`.  This carry branch does **not** preserve the single-branch residue
orbit: it can postpone the first `R7` residue well beyond `11` steps (see
`nat_uniform_eleven_fails`), and the two-branch residue relation has a self-loop
(`carry_self_loop_127`).  The deterministic quiver below is the correct reachability DAG; the
`ℕ` correction is stated explicitly rather than over-claimed. -/

/-- The `Z`-step on genuine naturals. -/
@[expose] public def zStepNat (g : ℕ) : ℕ := (3 * g + g % 2) / 2

/-- `3 * g + g % 2` is even, so the halving in `zStepNat` is exact. -/
public theorem two_dvd_three_mul_add_mod_two (g : ℕ) : 2 ∣ 3 * g + g % 2 := by
  have h : g % 2 = 0 ∨ g % 2 = 1 := by omega
  rcases h with h | h <;> omega

/-- **Carry branch.**  `zStepNat (g + 128) = zStepNat g + 192`. -/
public theorem zStepNat_add_128 (g : ℕ) : zStepNat (g + 128) = zStepNat g + 192 := by
  have hmod : (g + 128) % 2 = g % 2 := by omega
  obtain ⟨c, hc⟩ := two_dvd_three_mul_add_mod_two g
  unfold zStepNat
  rw [hmod]
  have : 3 * (g + 128) + g % 2 = 2 * (c + 192) := by omega
  rw [this]
  omega

/-- **Exact hitting set.**  `S7` is precisely the set of residues that reach `R7` within `11`
steps; there are no false positives.  This makes the certificate an exact characterisation, not
merely a sufficient condition. -/
public theorem S7_iff_hits : ∀ g : Fin 128, g ∈ S7 ↔ ∃ n ≤ 11, iterZ n g ∈ R7 := by
  decide

/-! ### The two carry branches `zStep g` and `zStep g + 64`

A genuine natural number reduces to a residue in `Fin 128`, but its `Z`-successor depends on the
lift: `zStepNat (g + 128) = zStepNat g + 192`, and `192 ≡ 64 (mod 128)`.  So the residue of a
successor is either `zStep g` or `zStep g + 64`.  We record this two-branch relation and show (by
an explicit machine-checked self-loop) that it is *not* acyclic; the misleading "branch DAG" is
therefore replaced by the deterministic quiver below. -/

/-- The residue successor set of the two carry branches: `zStep g` and `zStep g + 64` (mod 128). -/
@[expose] public def carrySucc (g : Fin 128) : Finset (Fin 128) :=
  {zStep g, embed128 ((zStep g).val + 64)}

/-- The two-branch carry relation on residues: `h` is one of the two carry successors of `g`. -/
@[expose] public def CarryStep (g h : Fin 128) : Prop := h ∈ carrySucc g

/-- **The naive two-branch residue graph is not acyclic.**  `zStep 127 = 63` and `63 + 64 ≡ 127`,
so `127` is a carry self-loop.  Hence no finite uniform depth bound exists for the two-branch
relation, and it cannot be presented as a DAG. -/
public theorem carry_self_loop_127 : CarryStep (embed128 127) (embed128 127) := by
  unfold CarryStep carrySucc
  decide

/-- `zStep` genuinely participates in the first carry branch. -/
public theorem carry_fst (g : Fin 128) : CarryStep g (zStep g) := by
  unfold CarryStep carrySucc
  simp

/-! ### The deterministic residue quiver on `S7`

Vertex set: the `27` legal residues `S7`.  An arrow `a ⟶ b` means `a` is not a collision residue
and one deterministic `zStep` sends `a` to `b`; the collision residues `R7` are the sinks.  This
is the actual reachability graph of the `Fin 128` certificate, and it *is* a DAG. -/

/-- The `27` legal residues, as a type. -/
@[expose] public def GapV := {g : Fin 128 // g ∈ S7}

/-- The deterministic residue quiver on `S7`.  Arrows are propositional, `PLift`ed because
`Quiver.Hom` must land in a `Type`. -/
instance gapQuiver : Quiver GapV where
  Hom a b := PLift (a.1 ∉ R7 ∧ b.1 = zStep a.1)

/-- Depth-to-`R7` potential, valued in `ℕᵒᵈ` so that arrows strictly decrease it. -/
@[expose] public def gapPot (v : GapV) : ℕᵒᵈ := OrderDual.toDual (dagDepth v.1)

/-- The deterministic step strictly decreases the depth inside `S7`.  This is a finite check on
the `128` residues, not a deep `11`-fold unfold. -/
public theorem dagDepth_step_decrease :
    ∀ g : Fin 128, g ∈ S7 → g ∉ R7 → dagDepth (zStep g) < dagDepth g := by
  decide

/-- **Strict monotonicity.**  Along every deterministic arrow the depth strictly decreases, so
`gapPot` is a `Quiver.StrictMono` potential. -/
public theorem gapPot_strictMono : Quiver.StrictMono gapPot := by
  intro a b e
  obtain ⟨ha, hb⟩ := e.down
  change dagDepth b.1 < dagDepth a.1
  rw [hb]
  exact dagDepth_step_decrease a.1 a.2 ha

/-- **The deterministic residue graph is acyclic** (no non-trivial path returns to its start),
by `Quiver.StrictMono.path_eq_nil` from mathlib4#44885. -/
public theorem gap_acyclic {a : GapV} (p : Quiver.Path a a) : p = .nil :=
  Quiver.StrictMono.path_eq_nil gapPot_strictMono p

/-- **`Quiver.Reachable` on the deterministic residue graph is a partial order**, again from
mathlib4#44885 (`Quiver.StrictMono.isPartialOrder_reachable`). -/
public theorem gap_reachable_isPartialOrder : IsPartialOrder GapV Quiver.Reachable :=
  Quiver.StrictMono.isPartialOrder_reachable gapPot_strictMono

/-! ### The genuine `ℕ`-orbit and the failure of a uniform bound

The actual map is `zStepNat : ℕ → ℕ`.  The single-branch `Fin 128` theorem bounds the residue
hitting time by `11` only for the `k`-even lift; genuine `ℕ` orbits that take the carry branch can
take longer.  We record the exact counterexample `g = 28`, whose first `R7` resident occurs at
step `25`, so the uniform `≤ 11` statement is *false* on `ℕ` and must be stated with its true
hypotheses rather than over-claimed. -/

/-- Iteration of `zStepNat` on genuine naturals. -/
@[expose] public def iterZNat : ℕ → ℕ → ℕ
  | 0, g => g
  | n + 1, g => iterZNat n (zStepNat g)

/-- The collision residues, as a set of naturals. -/
@[expose] public def R7Nat : Finset ℕ := {0, 4, 94, 120}

/-- The genuine `ℕ`-orbit of `28` misses every collision residue during its first `12` steps
(its first hit is at step `25`), so `28` is a concrete counterexample to the naive uniform
`≤ 11` bound on `ℕ`. -/
public theorem nat_counter_28 :
    ∀ n ∈ Finset.range 12, iterZNat n 28 % 128 ∉ R7Nat := by
  decide

/-- **No uniform `≤ 11` bound on `ℕ` orbits.**  The `Fin 128` bound does not lift verbatim to
`ℕ`: the carry branch can postpone the first `R7` residue beyond `11` steps (witness `28`). -/
public theorem nat_uniform_eleven_fails :
    ¬ (∀ g : ℕ, ∃ n ≤ 11, iterZNat n g % 128 ∈ R7Nat) := by
  intro h
  obtain ⟨n, hn, hmem⟩ := h 28
  exact nat_counter_28 n (Finset.mem_range.mpr (by omega)) hmem

end Mahler32.DAGBoundedGap
