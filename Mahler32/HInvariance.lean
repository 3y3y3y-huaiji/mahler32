/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Task 9 — `2`-adic affine offsets and the `h`-invariance of local Fourier norms

This module formalises the suffix-window `2`-adic machinery of the task sheet on the genuine
arithmetic definitions:

* `wordA u` — the integer prefix sum `∑_{n=0}^{s-1} u_n · 2^n · 3^{s-1-n}` of a word `u`;
* `henselInvAux M a k` — Newton/Hensel iteration `x ↦ x · (2 - a · x)`, which inverts an odd
  `a` modulo `2^s`;
* `wordResidue s u` — the unique residue `r_u` with `3^s · r_u + A(u) ≡ 0 (mod 2^s)`;
* `affineDelta s u h p3` — the affine offset `Δ(u, h, p3)` used in the suffix-window Fourier
  decomposition.

The main results are:

* `henselInv_correct` — `a · invModPow2 s a ≡ 1 (mod 2^s)` for odd `a`;
* `wordResidue_correct`, `affineDelta_equation`, `affineDelta_shift`, `affineDelta_scale` — the
  exact congruences satisfied by the residue and the affine offset;
* `affine_phase_shift` — the pairwise phase difference is completely `h`-independent;
* `fourier_norm_invariant` — for any additive unit-modulus character `χ`, the local Fourier norm
  satisfies `‖Φ(m, h, p3)‖ = ‖Φ(m · invModPow2 s p3, 0, 1)‖`.
-/

public section

namespace Mahler32.HInvariance

open scoped ComplexConjugate

/-! ### The locked arithmetic definitions -/

/-- `wordA u = ∑_{n=0}^{s-1} u_n * 2^n * 3^{s-1-n}` for `u = [u_0, …, u_{s-1}]`. -/
@[expose] public def wordA : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) * 3 ^ rest.length + 2 * wordA rest

/-- Newton/Hensel iteration for the inverse of `a` modulo `M`:
`x_0 = 1`, `x_{i+1} = x_i * (2 - a * x_i) mod M`. -/
@[expose] public def henselInvAux (M a : Nat) : Nat → Nat
  | 0 => 1 % M
  | k + 1 =>
      let x := henselInvAux M a k
      (x * ((2 * M + 2 - (a * x) % M) % M)) % M

/-- The inverse of `a` modulo `2^s`, obtained by `s` Hensel steps. -/
@[expose] public def invModPow2 (s a : Nat) : Nat := henselInvAux (2 ^ s) a s

/-- The unique residue `r_u mod 2^s` with `3^s * r_u + A(u) ≡ 0 (mod 2^s)`. -/
@[expose] public def wordResidue (s : Nat) (u : List Bool) : Nat :=
  let M := 2 ^ s
  let inv3s := invModPow2 s (3 ^ s)
  (inv3s * (M - wordA u % M)) % M

/-- The suffix-window `2`-adic affine offset `Δ(u, h, p3) mod 2^s`. -/
@[expose] public def affineDelta (s : Nat) (u : List Bool) (h p3 : Nat) : Nat :=
  let M := 2 ^ s
  let r := wordResidue s u
  (invModPow2 s p3 * ((r + M - h % M) % M)) % M

/-! ### Casts to `ZMod (2^s)`

Every congruence below is proved by transporting a `Nat` equality modulo `2^s` into the ring
`ZMod (2^s)`; these cast lemmas are the workhorses. -/

/-- The Hensel successor step, in `ZMod M`. -/
private lemma hensel_succ {M : Nat} (hM : 0 < M) (a k : Nat) :
    ((henselInvAux M a (k + 1) : ℕ) : ZMod M)
      = ((henselInvAux M a k : ℕ) : ZMod M)
          * (2 - (a : ZMod M) * ((henselInvAux M a k : ℕ) : ZMod M)) := by
  rw [henselInvAux.eq_2]
  rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod]
  congr 1
  rw [Nat.cast_sub (by
    have h1 := Nat.mod_lt (a * henselInvAux M a k) hM
    omega)]
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, ZMod.natCast_mod, Nat.cast_mul]
  ring

/-- Closed form of the Hensel iteration: `a · x_k = 1 - (1 - a)^(2^k)` in `ZMod M`. -/
private lemma hensel_closed {M : Nat} (hM : 0 < M) (a k : Nat) :
    (a : ZMod M) * ((henselInvAux M a k : ℕ) : ZMod M)
      = 1 - (1 - (a : ZMod M)) ^ (2 ^ k) := by
  induction k with
  | zero =>
    rw [henselInvAux.eq_1, ZMod.natCast_mod]
    norm_num
  | succ k ih =>
    rw [hensel_succ hM a k, ← mul_assoc, ih]
    rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 by ring, pow_mul]
    ring

/-- The Hensel iteration really inverts an odd `a` modulo `2^s`. -/
private theorem hensel_mul_inv_cast (s a : Nat) (ha : a % 2 = 1) :
    (a : ZMod (2 ^ s)) * ((invModPow2 s a : ℕ) : ZMod (2 ^ s)) = 1 := by
  have hM : 0 < 2 ^ s := by positivity
  show (a : ZMod (2 ^ s)) * ((henselInvAux (2 ^ s) a s : ℕ) : ZMod (2 ^ s)) = 1
  rw [hensel_closed hM a s]
  have ha' : a = 2 * (a / 2) + 1 := by
    have := Nat.mod_add_div a 2
    omega
  have hcast : ((a : ℕ) : ZMod (2 ^ s))
      = 2 * ((a / 2 : ℕ) : ZMod (2 ^ s)) + 1 := by
    conv_lhs => rw [ha']
    push_cast
    ring
  have h1a : (1 : ZMod (2 ^ s)) - (a : ZMod (2 ^ s))
      = - (2 * ((a / 2 : ℕ) : ZMod (2 ^ s))) := by
    rw [hcast]
    ring
  rw [h1a]
  have hs2 : s ≤ 2 ^ s := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow0 : ((2 ^ (2 ^ s) : ℕ) : ZMod (2 ^ s)) = 0 := by
    obtain ⟨c, hc⟩ := Nat.pow_dvd_pow 2 hs2
    rw [hc, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have h2 : ((2 : ZMod (2 ^ s)) ^ (2 ^ s)) = 0 := by
    have h := hpow0
    push_cast at h
    simpa using h
  have hpow : (- (2 * ((a / 2 : ℕ) : ZMod (2 ^ s)))) ^ (2 ^ s) = 0 := by
    rw [show (- (2 * ((a / 2 : ℕ) : ZMod (2 ^ s))))
        = (-1) * ((2 : ZMod (2 ^ s)) * ((a / 2 : ℕ) : ZMod (2 ^ s))) by ring]
    rw [mul_pow, mul_pow, h2]
    simp
  rw [hpow]
  ring

/-- Cast form of `wordResidue`. -/
private lemma wordResidue_cast (s : Nat) (u : List Bool) :
    ((wordResidue s u : ℕ) : ZMod (2 ^ s))
      = (invModPow2 s (3 ^ s) : ZMod (2 ^ s)) * (- (wordA u : ZMod (2 ^ s))) := by
  unfold wordResidue
  rw [ZMod.natCast_mod, Nat.cast_mul]
  rw [Nat.cast_sub (by
    have h1 := Nat.mod_lt (wordA u) (by positivity : 0 < 2 ^ s)
    omega)]
  rw [ZMod.natCast_self, ZMod.natCast_mod]
  ring

/-- Cast form of `affineDelta`. -/
private lemma affineDelta_cast (s : Nat) (u : List Bool) (h p3 : Nat) :
    ((affineDelta s u h p3 : ℕ) : ZMod (2 ^ s))
      = (invModPow2 s p3 : ZMod (2 ^ s))
          * ((wordResidue s u : ZMod (2 ^ s)) - (h : ZMod (2 ^ s))) := by
  unfold affineDelta
  rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod]
  rw [Nat.cast_sub (by
    have h1 := Nat.mod_lt h (by positivity : 0 < 2 ^ s)
    omega)]
  rw [Nat.cast_add, ZMod.natCast_self, ZMod.natCast_mod]
  ring

/-- `invModPow2 s 1` is `1`. -/
private lemma invModPow2_one (s : Nat) : (invModPow2 s 1 : ZMod (2 ^ s)) = 1 := by
  have h := hensel_mul_inv_cast s 1 (by norm_num : 1 % 2 = 1)
  simpa using h

/-- `3^s` is odd. -/
private lemma three_pow_odd (s : Nat) : 3 ^ s % 2 = 1 := by
  rw [Nat.pow_mod]
  norm_num

/-! ### Theorem 1: correctness of the Hensel inverse -/

/-- **Theorem 1.**  For odd `a`, `invModPow2 s a` is a multiplicative inverse of `a` modulo `2^s`. -/
theorem henselInv_correct (s a : Nat) (ha : a % 2 = 1) :
    (a * invModPow2 s a) % 2 ^ s = 1 % 2 ^ s := by
  rw [← ZMod.natCast_eq_natCast_iff' _ _ (2 ^ s)]
  rw [Nat.cast_mul, Nat.cast_one]
  exact hensel_mul_inv_cast s a ha

/-! ### Theorem 2: residue and affine-offset congruences -/

/-- **Theorem 2 (residue equation).**  `3^s · r_u + A(u) ≡ 0 (mod 2^s)`. -/
theorem wordResidue_correct (s : Nat) (u : List Bool) :
    (3 ^ s * wordResidue s u + wordA u) % 2 ^ s = 0 := by
  rw [show (0 : Nat) = 0 % 2 ^ s by simp]
  rw [← ZMod.natCast_eq_natCast_iff' _ _ (2 ^ s)]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_zero, wordResidue_cast]
  have h3 : ((3 ^ s : ℕ) : ZMod (2 ^ s)) * (invModPow2 s (3 ^ s) : ZMod (2 ^ s)) = 1 :=
    hensel_mul_inv_cast s (3 ^ s) (three_pow_odd s)
  rw [← mul_assoc, h3, one_mul]
  ring

/-- **Theorem 2 (affine equation).**  `p3 · Δ(u, h, p3) + h ≡ r_u (mod 2^s)`. -/
theorem affineDelta_equation (s : Nat) (u : List Bool) (h p3 : Nat) (hp3 : p3 % 2 = 1) :
    (p3 * affineDelta s u h p3 + h) % 2 ^ s = wordResidue s u % 2 ^ s := by
  rw [← ZMod.natCast_eq_natCast_iff' _ _ (2 ^ s)]
  push_cast
  rw [affineDelta_cast]
  have hinv : (p3 : ZMod (2 ^ s)) * (invModPow2 s p3 : ZMod (2 ^ s)) = 1 :=
    hensel_mul_inv_cast s p3 hp3
  rw [← mul_assoc, hinv, one_mul]
  ring

/-- **Theorem 2 (`h`-shift).**  Shifting `h` shifts `Δ` by `-invModPow2 s p3 · h`. -/
theorem affineDelta_shift (s : Nat) (u : List Bool) (h p3 : Nat) (_hp3 : p3 % 2 = 1) :
    (affineDelta s u h p3 + invModPow2 s p3 * h) % 2 ^ s
      = affineDelta s u 0 p3 % 2 ^ s := by
  rw [← ZMod.natCast_eq_natCast_iff' _ _ (2 ^ s)]
  push_cast
  rw [affineDelta_cast s u h p3, affineDelta_cast s u 0 p3]
  ring

/-- **Theorem 2 (`p3`-scaling).**  `m · Δ(u, 0, p3) ≡ m · invModPow2 s p3 · Δ(u, 0, 1)`. -/
theorem affineDelta_scale (s : Nat) (u : List Bool) (m p3 : Nat) (_hp3 : p3 % 2 = 1) :
    (m * affineDelta s u 0 p3) % 2 ^ s
      = ((m * invModPow2 s p3) * affineDelta s u 0 1) % 2 ^ s := by
  rw [← ZMod.natCast_eq_natCast_iff' _ _ (2 ^ s)]
  push_cast
  rw [affineDelta_cast s u 0 p3, affineDelta_cast s u 0 1, invModPow2_one]
  ring

/-! ### Theorem 3: the pairwise phase difference is `h`-invariant -/

/-- **Theorem 3.**  For any two words `u`, `v`, integer frequency `m`, offset `h` and odd `p3`,
the phase difference `m (Δ_u - Δ_v)` modulo `2^s` is independent of `h`. -/
theorem affine_phase_shift (s : Nat) (u v : List Bool) (m : Int) (h p3 : Nat)
    (_hp3 : p3 % 2 = 1) :
    ((m * (affineDelta s u h p3 : Int) - m * (affineDelta s v h p3 : Int)) % (2 ^ s : Int))
      = (((m * (invModPow2 s p3 : Int))
            * ((affineDelta s u 0 1 : Int) - (affineDelta s v 0 1 : Int))) % (2 ^ s : Int)) := by
  have hmod : ((2 : ℤ) ^ s) = ((2 ^ s : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    norm_num
  rw [hmod]
  rw [← ZMod.intCast_eq_intCast_iff' _ _ (2 ^ s)]
  push_cast
  rw [affineDelta_cast s u h p3, affineDelta_cast s v h p3,
    affineDelta_cast s u 0 1, affineDelta_cast s v 0 1, invModPow2_one]
  ring

/-! ### Theorem 4: `h`-invariance of the local Fourier norm -/

/-- The local Fourier sum `Φ_s(m, h, p3) = ∑_{u ∈ W} χ(m · Δ(u, h, p3))`, for an additive
character `χ` on `ZMod (2^s)`. -/
@[expose] public def localFourier (s : Nat) (W : List (List Bool)) (m h p3 : Nat)
    (χ : ZMod (2 ^ s) → ℂ) : ℂ :=
  (W.map fun u => χ ((m : ZMod (2 ^ s)) * ((affineDelta s u h p3 : ℕ) : ZMod (2 ^ s)))).sum

/-- The squared norm `|Φ_s(m, h, p3)|^2` of the local Fourier sum. -/
noncomputable def localFourierNormSq (s : Nat) (W : List (List Bool)) (m h p3 : Nat)
    (χ : ZMod (2 ^ s) → ℂ) : ℝ :=
  ‖localFourier s W m h p3 χ‖ ^ 2

@[simp] lemma localFourier_nil (s : Nat) (m h p3 : Nat) (χ : ZMod (2 ^ s) → ℂ) :
    localFourier s [] m h p3 χ = 0 := rfl

@[simp] lemma localFourier_cons (s : Nat) (u : List Bool) (W : List (List Bool))
    (m h p3 : Nat) (χ : ZMod (2 ^ s) → ℂ) :
    localFourier s (u :: W) m h p3 χ
      = χ ((m : ZMod (2 ^ s)) * ((affineDelta s u h p3 : ℕ) : ZMod (2 ^ s)))
        + localFourier s W m h p3 χ := by
  simp [localFourier]

/-- The pointwise phase identity: the `h`-dependence factors out as one constant phase. -/
private lemma chi_shift_point (s : Nat) (u : List Bool) (h p3 m : Nat)
    (_hp3 : p3 % 2 = 1) (χ : ZMod (2 ^ s) → ℂ)
    (hadd : ∀ a b, χ (a + b) = χ a * χ b) :
    χ ((m : ZMod (2 ^ s)) * ((affineDelta s u h p3 : ℕ) : ZMod (2 ^ s)))
      = χ (-((m : ZMod (2 ^ s)) * (invModPow2 s p3 : ZMod (2 ^ s))
              * (h : ZMod (2 ^ s))))
        * χ (((m * invModPow2 s p3 : Nat) : ZMod (2 ^ s))
              * ((affineDelta s u 0 1 : ℕ) : ZMod (2 ^ s))) := by
  have harg : (m : ZMod (2 ^ s)) * ((affineDelta s u h p3 : ℕ) : ZMod (2 ^ s))
      = -((m : ZMod (2 ^ s)) * (invModPow2 s p3 : ZMod (2 ^ s)) * (h : ZMod (2 ^ s)))
        + (((m * invModPow2 s p3 : Nat) : ZMod (2 ^ s))
            * ((affineDelta s u 0 1 : ℕ) : ZMod (2 ^ s))) := by
    rw [affineDelta_cast s u h p3, affineDelta_cast s u 0 1, invModPow2_one]
    push_cast
    ring
  rw [harg, hadd]

/-- **Theorem 4.**  If `χ` is additive on `ZMod (2^s)` and has unit norm, then the local Fourier
norm is unchanged when `h` is moved into the frequency. -/
theorem fourier_norm_invariant (s : Nat) (W : List (List Bool)) (m h p3 : Nat)
    (hp3 : p3 % 2 = 1) (χ : ZMod (2 ^ s) → ℂ)
    (hadd : ∀ a b, χ (a + b) = χ a * χ b) (hnorm : ∀ a, ‖χ a‖ = 1) :
    localFourierNormSq s W m h p3 χ
      = localFourierNormSq s W (m * invModPow2 s p3) 0 1 χ := by
  have hf : localFourier s W m h p3 χ
      = χ (-((m : ZMod (2 ^ s)) * (invModPow2 s p3 : ZMod (2 ^ s))
              * (h : ZMod (2 ^ s))))
        * localFourier s W (m * invModPow2 s p3) 0 1 χ := by
    induction W with
    | nil => simp
    | cons u W ih =>
      rw [localFourier_cons, ih, localFourier_cons]
      rw [chi_shift_point s u h p3 m hp3 χ hadd]
      ring
  unfold localFourierNormSq
  rw [hf, norm_mul, hnorm, one_mul]

end Mahler32.HInvariance

end
