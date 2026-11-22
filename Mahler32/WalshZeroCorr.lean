/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mahler32.Base6LightCone

/-!
# Task 8 — Walsh top-bit locking and the zero-correlation theorem

This module binds the Walsh character of the *real* `k`-step orbit
`(iterStep k x) % 2` of `Mahler32.Base6LightCone` and proves that the
Walsh–Hadamard coefficient over the `(k+1)`-bit input cube `[0, 2^(k+1))`
vanishes whenever the frequency mask has no top bit (`u < 2^k`), while the
frequency with the top bit set doubles the lower-dimensional coefficient.

The key inputs are the light-cone translation law
`iterStep_add_two_pow` (shifting the input by `2^k` shifts the orbit by `3^k`,
which is odd) and the exact response of the binary dot product to that shift.
-/

public section

namespace Mahler32.WalshZeroCorr

open Mahler32.Base6LightCone

/-- The parity bit of the `k`-step orbit (bound directly to
`Mahler32.Base6LightCone.iterStep`). -/
@[expose] public def fk (k : Nat) (x : Nat) : Nat := (iterStep k x) % 2

/-- Binary digit-wise inner product modulo `2`, with an explicit fuel argument
(the fourth argument is an ignored dummy so that every recursion call site has
a uniform shape).  `bitDotAux n u x = ∑_{i<n} u_i · x_i (mod 2)`. -/
@[expose] public def bitDotAux (n : Nat) (u : Nat) (x : Nat) (_hp : Nat := 0) : Nat :=
  match n with
  | 0 => 0
  | n+1 => ((u % 2) * (x % 2) + bitDotAux n (u / 2) (x / 2)) % 2

/-- The sign character `b ↦ (-1)^b`. -/
@[expose] public def signBit (b : Nat) : Int := if b % 2 = 0 then 1 else -1

/-- The exact Walsh–Hadamard coefficient of `fk k` on the `(k+1)`-bit cube,
with frequency mask `u`. -/
@[expose] public def walshCoeff (k u : Nat) : Int :=
  ((List.range (2 ^ (k + 1))).map (fun x => signBit (fk k x + bitDotAux (k + 1) u x))).sum

/-! ### Elementary unfolding and bounds for `bitDotAux` -/

@[simp] lemma bitDotAux_zero (u x : Nat) (d : Nat) : bitDotAux 0 u x d = 0 := by
  simp [bitDotAux]

@[simp] lemma bitDotAux_succ (n u x : Nat) (d : Nat) :
    bitDotAux (n + 1) u x d = ((u % 2) * (x % 2) + bitDotAux n (u / 2) (x / 2)) % 2 := by
  simp [bitDotAux]

/-- `bitDotAux` always returns a bit. -/
lemma bitDotAux_lt_two : ∀ n u x (d : Nat), bitDotAux n u x d < 2
  | 0, u, x, d => by simp [bitDotAux_zero]
  | n+1, u, x, d => by
      rw [bitDotAux_succ]
      omega

/-- Once the fuel exceeds the number of significant bits, one more step adds
nothing. -/
lemma bitDotAux_stabilize : ∀ k u x, u < 2 ^ k → x < 2 ^ k →
    bitDotAux (k + 1) u x = bitDotAux k u x
  | 0, u, x, hu, hx => by
      have hu0 : u = 0 := by omega
      have hx0 : x = 0 := by omega
      subst hu0; subst hx0
      simp [bitDotAux]
  | k + 1, u, x, hu, hx => by
      rw [pow_succ] at hu hx
      conv_lhs => rw [bitDotAux_succ]
      conv_rhs => rw [bitDotAux_succ]
      have hu' : u / 2 < 2 ^ k := by omega
      have hx' : x / 2 < 2 ^ k := by omega
      rw [bitDotAux_stabilize k (u / 2) (x / 2) hu' hx']

/-- A mask bit above the input's significant bits does not affect the dot
product. -/
lemma bitDotAux_mask_top : ∀ k u x, x < 2 ^ k →
    bitDotAux (k + 1) (u + 2 ^ k) x = bitDotAux (k + 1) u x
  | 0, u, x, hx => by
      have hx0 : x = 0 := by omega
      subst hx0
      simp [bitDotAux]
  | k + 1, u, x, hx => by
      rw [pow_succ] at hx ⊢
      conv_lhs => rw [bitDotAux_succ]
      conv_rhs => rw [bitDotAux_succ]
      have hmod : (u + 2 ^ k * 2) % 2 = u % 2 := by omega
      have hdiv : (u + 2 ^ k * 2) / 2 = u / 2 + 2 ^ k := by omega
      rw [hmod, hdiv]
      have hx' : x / 2 < 2 ^ k := by omega
      rw [bitDotAux_mask_top k (u / 2) (x / 2) hx']

/-- The top mask bit is inactive when the input has no top bit. -/
lemma bitDotAux_high_zero (k u y : Nat) (hu : u < 2 ^ k) (hy : y < 2 ^ k) :
    bitDotAux (k + 1) (u + 2 ^ k) y % 2 = bitDotAux k u y % 2 := by
  rw [bitDotAux_mask_top k u y hy, bitDotAux_stabilize k u y hu hy]

/-- Stabilised form for the mask `u` itself. -/
lemma bitDotAux_self_stable (k u y : Nat) (hu : u < 2 ^ k) (hy : y < 2 ^ k) :
    bitDotAux (k + 1) u y % 2 = bitDotAux k u y % 2 := by
  rw [bitDotAux_stabilize k u y hu hy]

/-! ### Theorem 1: shifting the input by `2^k` flips the parity -/

theorem fk_add_two_pow (k x : Nat) : fk k (x + 2 ^ k) = (fk k x + 1) % 2 := by
  unfold fk
  rw [show x + 2 ^ k = x + 2 ^ k * 1 by rw [Nat.mul_one]]
  rw [iterStep_add_two_pow, Nat.mul_one]
  have h3 : 3 ^ k % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [Nat.add_mod, h3]

/-- `signBit` depends only on the parity of its argument. -/
lemma signBit_eq_of_mod {a b : Nat} (h : a % 2 = b % 2) : signBit a = signBit b := by
  unfold signBit
  rw [h]

/-- Incrementing the argument flips the sign. -/
lemma signBit_succ (a : Nat) : signBit (a + 1) = - signBit a := by
  unfold signBit
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have h2 : (a + 1) % 2 = 1 := by omega
    rw [h2, h]; norm_num
  · have h2 : (a + 1) % 2 = 0 := by omega
    rw [h2, h]; norm_num

theorem signBit_fk_add_two_pow (k x : Nat) :
    signBit (fk k (x + 2 ^ k)) = - signBit (fk k x) := by
  rw [fk_add_two_pow]
  have h : ((fk k x + 1) % 2) % 2 = (fk k x + 1) % 2 := by omega
  rw [show signBit ((fk k x + 1) % 2) = signBit (fk k x + 1) from signBit_eq_of_mod h]
  exact signBit_succ (fk k x)

/-! ### Theorem 2: the exact response of the binary dot product -/

/-- Low-mask invariance under adding the top bit to the input. -/
lemma bitDotAux_low_shift_eq : ∀ k u x, u < 2 ^ k → x < 2 ^ k →
    bitDotAux (k + 1) u (x + 2 ^ k) = bitDotAux (k + 1) u x
  | 0, u, x, hu, hx => by
      have hu0 : u = 0 := by omega
      have hx0 : x = 0 := by omega
      subst hu0; subst hx0
      simp [bitDotAux]
  | k + 1, u, x, hu, hx => by
      rw [pow_succ] at hu hx ⊢
      conv_lhs => rw [bitDotAux_succ]
      conv_rhs => rw [bitDotAux_succ]
      have hmod : (x + 2 ^ k * 2) % 2 = x % 2 := by omega
      have hdiv : (x + 2 ^ k * 2) / 2 = x / 2 + 2 ^ k := by omega
      rw [hmod, hdiv]
      have hu' : u / 2 < 2 ^ k := by omega
      have hx' : x / 2 < 2 ^ k := by omega
      rw [bitDotAux_low_shift_eq k (u / 2) (x / 2) hu' hx']

/-- Top-bit activation flips the dot product. -/
lemma bitDotAux_top_shift_eq : ∀ k u x, u < 2 ^ k → x < 2 ^ k →
    bitDotAux (k + 1) (u + 2 ^ k) (x + 2 ^ k) = (bitDotAux (k + 1) u x + 1) % 2
  | 0, u, x, hu, hx => by
      have hu0 : u = 0 := by omega
      have hx0 : x = 0 := by omega
      subst hu0; subst hx0
      simp [bitDotAux]
  | k + 1, u, x, hu, hx => by
      rw [pow_succ] at hu hx ⊢
      conv_lhs => rw [bitDotAux_succ]
      conv_rhs => rw [bitDotAux_succ]
      have hu_m : (u + 2 ^ k * 2) % 2 = u % 2 := by omega
      have hu_d : (u + 2 ^ k * 2) / 2 = u / 2 + 2 ^ k := by omega
      have hx_m : (x + 2 ^ k * 2) % 2 = x % 2 := by omega
      have hx_d : (x + 2 ^ k * 2) / 2 = x / 2 + 2 ^ k := by omega
      rw [hu_m, hu_d, hx_m, hx_d]
      have hu' : u / 2 < 2 ^ k := by omega
      have hx' : x / 2 < 2 ^ k := by omega
      rw [bitDotAux_top_shift_eq k (u / 2) (x / 2) hu' hx']
      omega

theorem bitDot_low_shift (k u x : Nat) (hu : u < 2 ^ k) (hx : x < 2 ^ k) :
    bitDotAux (k + 1) u (x + 2 ^ k) % 2 = bitDotAux (k + 1) u x % 2 := by
  rw [bitDotAux_low_shift_eq k u x hu hx]

theorem bitDot_top_shift (k u x : Nat) (hu : u < 2 ^ k) (hx : x < 2 ^ k) :
    bitDotAux (k + 1) (u + 2 ^ k) (x + 2 ^ k) % 2 = (bitDotAux (k + 1) u x + 1) % 2 := by
  rw [bitDotAux_top_shift_eq k u x hu hx]
  omega

/-! ### Theorem 3: the list-pairing lemma -/

/-- Splitting the range `[0, 2N)` into two halves and summing pointwise. -/
lemma sum_range_two_mul (g : Nat → Int) (N : Nat) :
    ((List.range (2 * N)).map g).sum =
      ((List.range N).map (fun x => g x + g (x + N))).sum := by
  have hN : 2 * N = N + N := by ring
  rw [hN, List.range_add, List.map_append, List.sum_append, List.map_map]
  rw [List.sum_map_add]
  have hmap : (List.map (g ∘ (fun x => N + x)) (List.range N)) =
      (List.map (fun x => g (x + N)) (List.range N)) := by
    apply List.map_congr_left
    intro x _
    rw [Function.comp_apply, Nat.add_comm]
  rw [hmap]

/-- Each paired term vanishes for a top-bit-zero mask. -/
lemma signBit_pair_zero (f f' b c : Nat) (hf : f' = (f + 1) % 2) (hc : c % 2 = b % 2) :
    signBit (f + b) + signBit (f' + c) = 0 := by
  have h1 : (f' + c) % 2 = (f + c + 1) % 2 := by rw [hf]; omega
  have h2 : (f + c) % 2 = (f + b) % 2 := by omega
  have e1 : signBit (f' + c) = signBit (f + c + 1) := signBit_eq_of_mod h1
  have e2 : signBit (f + c) = signBit (f + b) := signBit_eq_of_mod h2
  have e3 : signBit (f + c + 1) = - signBit (f + c) := signBit_succ (f + c)
  rw [e1, e3, e2]
  ring

theorem walsh_top_bit_zero (k u : Nat) (hu : u < 2 ^ k) : walshCoeff k u = 0 := by
  unfold walshCoeff
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, Nat.mul_comm]]
  rw [sum_range_two_mul]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  have hy' : y < 2 ^ k := List.mem_range.mp hy
  exact signBit_pair_zero (fk k y) (fk k (y + 2 ^ k))
    (bitDotAux (k + 1) u y) (bitDotAux (k + 1) u (y + 2 ^ k))
    (fk_add_two_pow k y) (bitDot_low_shift k u y hu hy')

/-! ### Theorem 4: the top-bit frequency doubles the lower coefficient -/

/-- Summing a constant multiple over a list. -/
lemma sum_map_two_mul (l : List Nat) (h : Nat → Int) :
    (l.map (fun y => (2 : Int) * h y)).sum = 2 * (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
      ring

/-- Each paired term doubles the lower-dimensional character. -/
lemma signBit_pair_double (k u y : Nat) (hu : u < 2 ^ k) (hy : y < 2 ^ k) :
    signBit (fk k y + bitDotAux (k + 1) (u + 2 ^ k) y) +
      signBit (fk k (y + 2 ^ k) + bitDotAux (k + 1) (u + 2 ^ k) (y + 2 ^ k)) =
        2 * signBit (fk k y + bitDotAux k u y) := by
  have h1 : bitDotAux (k + 1) (u + 2 ^ k) y % 2 = bitDotAux k u y % 2 :=
    bitDotAux_high_zero k u y hu hy
  have h2 : bitDotAux (k + 1) (u + 2 ^ k) (y + 2 ^ k) % 2 =
      (bitDotAux (k + 1) u y + 1) % 2 := bitDot_top_shift k u y hu hy
  have h3 : bitDotAux (k + 1) u y % 2 = bitDotAux k u y % 2 :=
    bitDotAux_self_stable k u y hu hy
  have hf : fk k (y + 2 ^ k) = (fk k y + 1) % 2 := fk_add_two_pow k y
  have e1 : signBit (fk k y + bitDotAux (k + 1) (u + 2 ^ k) y) =
      signBit (fk k y + bitDotAux k u y) := by
    apply signBit_eq_of_mod
    omega
  have e2 : signBit (fk k (y + 2 ^ k) + bitDotAux (k + 1) (u + 2 ^ k) (y + 2 ^ k)) =
      signBit (fk k y + bitDotAux k u y) := by
    apply signBit_eq_of_mod
    omega
  rw [e1, e2]
  ring

theorem walsh_top_bit_double (k u : Nat) (hu : u < 2 ^ k) :
    walshCoeff k (u + 2 ^ k) =
      2 * ((List.range (2 ^ k)).map (fun x => signBit (fk k x + bitDotAux k u x))).sum := by
  unfold walshCoeff
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, Nat.mul_comm]]
  rw [sum_range_two_mul]
  have hmap : (List.map (fun x =>
        signBit (fk k x + bitDotAux (k + 1) (u + 2 ^ k) x) +
          signBit (fk k (x + 2 ^ k) + bitDotAux (k + 1) (u + 2 ^ k) (x + 2 ^ k)))
        (List.range (2 ^ k))) =
      (List.map (fun x => (2 : Int) * signBit (fk k x + bitDotAux k u x))
        (List.range (2 ^ k))) := by
    apply List.map_congr_left
    intro y hy
    exact signBit_pair_double k u y hu (List.mem_range.mp hy)
  rw [hmap, sum_map_two_mul]

end Mahler32.WalshZeroCorr

end
