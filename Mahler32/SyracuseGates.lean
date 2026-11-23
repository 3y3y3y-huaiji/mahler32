/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mahler32.Basic

/-!
# Task 2 — Mahler–Syracuse odd-step gates

`zStep` is the integer part of the Mahler `3/2` map: halve when already even, otherwise apply
the ceiling step.  The theorems isolate the two local gates used by the `11`-free pruning:

* an odd, `3`-divisible value whose next `zStep` is even satisfies `g % 12 = 9`
  (equivalently: an `11`-free odd step is `≡ 9 (mod 12)`);
* the eight-step parity pattern `1,0,1,0,0,0,0,0` is equivalent to `g % 256 = 9`;
* combining `g % 3 = 0` with `g % 256 = 9` gives `g % 768 = 9`.
-/

public section

namespace Mahler32.SyracuseGates

/-- Integer part of the Mahler `3/2` map. -/
@[expose] public def zStep (g : ℕ) : ℕ :=
  if g % 2 = 0 then (3 * g) / 2 else (3 * g + 1) / 2

/-- On an odd input, `zStep g` is even exactly on the class `g ≡ 9 (mod 12)` (among the odd,
`3`-divisible classes `3` and `9` modulo `12`).  This is the precise form of
"an `11`-free odd step satisfies `g ≡ 9 (mod 12)`": `11`-free forbids two consecutive odd
steps, so the odd value `g` must have an even successor. -/
public theorem odd_step_mod_twelve {g : ℕ} (hodd : g % 2 = 1) (hthree : g % 3 = 0) :
    zStep g % 2 = 0 ↔ g % 12 = 9 := by
  have hcases : g % 12 = 3 ∨ g % 12 = 9 := by
    have h123 : g % 12 % 3 = g % 3 := Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 12)
    have hlt : g % 12 < 12 := Nat.mod_lt _ (by norm_num)
    omega
  constructor
  · intro hz
    rcases hcases with h | h
    · exfalso
      simp [zStep, hodd] at hz
      obtain ⟨k, rfl⟩ : ∃ k, g = 12 * k + 3 := ⟨g / 12, by omega⟩
      have h1 : 3 * (12 * k + 3) + 1 = 2 * (18 * k + 5) := by ring
      rw [h1, Nat.mul_div_right _ (by norm_num : 0 < 2)] at hz
      omega
    · exact h
  · intro h
    simp [zStep, hodd]
    obtain ⟨k, rfl⟩ : ∃ k, g = 12 * k + 9 := ⟨g / 12, by omega⟩
    have h1 : 3 * (12 * k + 9) + 1 = 2 * (18 * k + 14) := by ring
    rw [h1, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    omega

/-- The eight-step short-jump gate: over the `256` residue classes, `256 ∣ 27g+13` holds for
exactly the class `g ≡ 9 (mod 256)`. -/
public theorem short_jump_mod_256 (g : ℕ) : 256 ∣ (27 * g + 13) ↔ g % 256 = 9 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

/-- Merging the `3`-adic and `2`-adic gates: `g ≡ 9 (mod 256)` together with `g ≡ 0 (mod 3)`
forces `g ≡ 9 (mod 768)`. -/
public theorem mod_768_gate {g : ℕ} (h3 : g % 3 = 0) (h256 : g % 256 = 9) :
    g % 768 = 9 := by
  omega

end Mahler32.SyracuseGates

end
