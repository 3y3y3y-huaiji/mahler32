/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib
public import Mahler32.TwoWorldPadeCriterion
public import Mahler32.Model94GlobalDecay
public import Mahler32.RationalBaseDefs

/-!
# General `(p, q)` Repetition-Exponent Exclusion, Tunnel Fourier Decay & Karp Certificates

This module generalises the `9/4` unconditional results of `Mahler32.TwoWorldPadeCriterion` and
`Mahler32.Model94GlobalDecay` to arbitrary coprime rational bases `p / q` (`2 ≤ q < p`), building on
the pure definitions in `Mahler32.RationalBaseDefs`:

1. **General `(p, q)` repetition-exponent exclusion (`repetition_exponent_bound_pq`)**:
   Simultaneous Archimedean and `q`-adic evaluation along any eventually periodic symbolic word
   `U V^w` yields the critical threshold `log p / log q`:
   `w < log p / log q + (log p / log q - 1) * (|U| / |V|) + log(g₀ + dmax / (p - q)) / (|V| log q)`.
2. **General `(p, q)` tunnel Fourier decay & quantitative Weyl equidistribution**:
   For any consecutive-digit two-branch model `q g' = p g + d` (`d ∈ {d₀, d₀ + 1}`, `gcd p q = 1`),
   we prove exact `q`-contraction, the `p`-multiplication cosine product, the general tunnel decay
   `‖μ̂_K(u)‖ ≤ C · K^{-c}` for `q ∤ u` (lifting via `q`-contraction), and instantiate it on
   `(3, 2), (4, 3), (5, 4), (5, 3), (7, 4), (8, 3)`.
3. **Karp dual-potential cycle bound & 44-vertex certificate (`cert44`)**:
   Extends `DualPotentialCert` with `karp_cycle_bound` along cycles and instantiates `cert44`.
-/

public section

open scoped BigOperators

namespace Mahler32.GeneralPQDecay

open Mahler32
open Mahler32.TwoWorldPadeCriterion
open Mahler32.Model94GlobalDecay

/-! ### 1. General `(p, q)` repetition-exponent exclusion (`log_q p` threshold) -/

public lemma wordWeightPQ_append (p q : ℕ) (U V : List ℕ) :
    wordWeightPQ p q (U ++ V) =
      p ^ V.length * wordWeightPQ p q U + q ^ U.length * wordWeightPQ p q V := by
  induction U with
  | nil => simp [wordWeightPQ]
  | cons d rest ih =>
    simp only [List.cons_append, wordWeightPQ, List.length_append, List.length_cons, ih]
    rw [pow_add, pow_succ]
    ring

public lemma wordWeightPQ_repeat_int (p q : ℕ) (V : List ℕ) (w : ℕ) :
    ((p : ℤ) ^ V.length - q ^ V.length) * (wordWeightPQ p q (repeatWord V w) : ℤ) =
      ((p : ℤ) ^ (w * V.length) - q ^ (w * V.length)) * (wordWeightPQ p q V : ℤ) := by
  induction w with
  | zero => simp [repeatWord, wordWeightPQ]
  | succ w ih =>
    have hadd : (p : ℤ) ^ ((w + 1) * V.length) = (p : ℤ) ^ V.length * p ^ (w * V.length) := by
      rw [← pow_add, add_mul, one_mul, add_comm]
    have hqadd : (q : ℤ) ^ ((w + 1) * V.length) = (q : ℤ) ^ V.length * q ^ (w * V.length) := by
      rw [← pow_add, add_mul, one_mul, add_comm]
    simp only [repeatWord]
    have hwt : (wordWeightPQ p q (V ++ repeatWord V w) : ℤ) =
        (p : ℤ) ^ (w * V.length) * wordWeightPQ p q V +
          (q : ℤ) ^ V.length * wordWeightPQ p q (repeatWord V w) := by
      exact_mod_cast (by
        rw [wordWeightPQ_append, repeatWord_length])
    calc
      ((p : ℤ) ^ V.length - q ^ V.length) * (wordWeightPQ p q (V ++ repeatWord V w) : ℤ)
          = ((p : ℤ) ^ V.length - q ^ V.length) *
              ((p : ℤ) ^ (w * V.length) * wordWeightPQ p q V) +
            (q : ℤ) ^ V.length *
              (((p : ℤ) ^ V.length - q ^ V.length) *
                (wordWeightPQ p q (repeatWord V w) : ℤ)) := by
            rw [hwt]; ring
      _ = ((p : ℤ) ^ V.length - q ^ V.length) *
            ((p : ℤ) ^ (w * V.length) * wordWeightPQ p q V) +
          (q : ℤ) ^ V.length *
            (((p : ℤ) ^ (w * V.length) - q ^ (w * V.length)) * (wordWeightPQ p q V : ℤ)) := by
            rw [ih]
      _ = ((p : ℤ) ^ ((w + 1) * V.length) - q ^ ((w + 1) * V.length)) *
            (wordWeightPQ p q V : ℤ) := by
            rw [hadd, hqadd]; ring

public lemma wordWeightPQ_bounds_int {p q dmin dmax : ℕ} (hpq : q ≤ p) {W : List ℕ}
    (hW : validWordPQ dmin dmax W) :
    (dmin : ℤ) * ((p : ℤ) ^ W.length - q ^ W.length) ≤
        ((p : ℤ) - q) * (wordWeightPQ p q W : ℤ) ∧
      ((p : ℤ) - q) * (wordWeightPQ p q W : ℤ) ≤
        (dmax : ℤ) * ((p : ℤ) ^ W.length - q ^ W.length) := by
  induction W with
  | nil => simp [wordWeightPQ]
  | cons d rest ih =>
    have hd : dmin ≤ d ∧ d ≤ dmax := hW d (by simp)
    have hrest : validWordPQ dmin dmax rest := fun x hx => hW x (by simp [hx])
    obtain ⟨ih1, ih2⟩ := ih hrest
    have hp_ge : (0 : ℤ) ≤ (p : ℤ) ^ rest.length := pow_nonneg (by grind) _
    have hq_pos : (0 : ℤ) ≤ q := by grind
    have hpq_nn : (0 : ℤ) ≤ (p : ℤ) - q := by grind
    have hlo1 : (dmin : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length ≤
        (d : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hd.1) hpq_nn) hp_ge
    have hhi1 : (d : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length ≤
        (dmax : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hd.2) hpq_nn) hp_ge
    have hlo2 : (q : ℤ) * ((dmin : ℤ) * ((p : ℤ) ^ rest.length - q ^ rest.length)) ≤
        (q : ℤ) * (((p : ℤ) - q) * wordWeightPQ p q rest) :=
      mul_le_mul_of_nonneg_left ih1 hq_pos
    have hhi2 : (q : ℤ) * (((p : ℤ) - q) * wordWeightPQ p q rest) ≤
        (q : ℤ) * ((dmax : ℤ) * ((p : ℤ) ^ rest.length - q ^ rest.length)) :=
      mul_le_mul_of_nonneg_left ih2 hq_pos
    simp only [wordWeightPQ, List.length_cons, pow_succ]
    push_cast
    have hstepL : ((p : ℤ) - q) * (d * ((p : ℤ) ^ rest.length * p) +
        q * wordWeightPQ p q rest) =
        d * ((p : ℤ) - q) * (p : ℤ) ^ rest.length * p +
          q * (((p : ℤ) - q) * wordWeightPQ p q rest) := by ring
    have hp_nn : (0 : ℤ) ≤ p := by grind
    have hlo1p : (dmin : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length * p ≤
        (d : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length * p :=
      mul_le_mul_of_nonneg_right hlo1 hp_nn
    have hhi1p : (d : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length * p ≤
        (dmax : ℤ) * ((p : ℤ) - q) * (p : ℤ) ^ rest.length * p :=
      mul_le_mul_of_nonneg_right hhi1 hp_nn
    constructor <;> linarith

/-- Bounds on `qStarPQ`: `-dmax / (p - q) ≤ qStarPQ p q U V ≤ -dmin / (p - q)`. -/
public theorem qStarPQ_bounds {p q dmin dmax : ℕ} (hpq : q < p) {U V : List ℕ}
    (hU : validWordPQ dmin dmax U) (hV : validWordPQ dmin dmax V) (hs : 0 < V.length) :
    -((dmax : ℚ) / ((p : ℚ) - q)) ≤ qStarPQ p q U V ∧
      qStarPQ p q U V ≤ -((dmin : ℚ) / ((p : ℚ) - q)) := by
  have hpq' : q ≤ p := hpq.le
  obtain ⟨hU1, hU2⟩ := wordWeightPQ_bounds_int hpq' hU
  obtain ⟨hV1, hV2⟩ := wordWeightPQ_bounds_int hpq' hV
  set A : ℤ := (p : ℤ) ^ V.length - q ^ V.length
  set B : ℤ := (p : ℤ) ^ U.length
  set C : ℤ := (q : ℤ) ^ U.length
  have hpqZ : (0 : ℤ) < (p : ℤ) - q := by grind
  have hApos : 0 < A := by
    have hnat : q ^ V.length < p ^ V.length := Nat.pow_lt_pow_left hpq hs.ne'
    have hz : (q : ℤ) ^ V.length < (p : ℤ) ^ V.length := by exact_mod_cast hnat
    exact sub_pos.mpr hz
  have hBpos : 0 < B := pow_pos (by grind) _
  have hCpos : 0 ≤ C := pow_nonneg (by grind) _
  have hcomb_lo : (dmin : ℤ) * B * A ≤
      ((p : ℤ) - q) * (A * (wordWeightPQ p q U : ℤ) + C * (wordWeightPQ p q V : ℤ)) := by
    have hmul1 : (dmin : ℤ) * ((p : ℤ) ^ U.length - C) * A ≤
        (((p : ℤ) - q) * (wordWeightPQ p q U : ℤ)) * A :=
      mul_le_mul_of_nonneg_right hU1 hApos.le
    have hmul2 : C * ((dmin : ℤ) * A) ≤ C * (((p : ℤ) - q) * (wordWeightPQ p q V : ℤ)) :=
      mul_le_mul_of_nonneg_left hV1 hCpos
    linarith
  have hcomb_hi :
      ((p : ℤ) - q) * (A * (wordWeightPQ p q U : ℤ) + C * (wordWeightPQ p q V : ℤ)) ≤
        (dmax : ℤ) * B * A := by
    have hmul1 : (((p : ℤ) - q) * (wordWeightPQ p q U : ℤ)) * A ≤
        (dmax : ℤ) * ((p : ℤ) ^ U.length - C) * A :=
      mul_le_mul_of_nonneg_right hU2 hApos.le
    have hmul2 : C * (((p : ℤ) - q) * (wordWeightPQ p q V : ℤ)) ≤ C * ((dmax : ℤ) * A) :=
      mul_le_mul_of_nonneg_left hV2 hCpos
    linarith
  have hBAposQ : (0 : ℚ) < ((p : ℚ) ^ U.length * ((p : ℚ) ^ V.length - (q : ℚ) ^ V.length)) := by
    have : (0 : ℚ) < (B : ℚ) * (A : ℚ) := by exact_mod_cast mul_pos hBpos hApos
    simpa [B, A] using this
  have hpqQ : (0 : ℚ) < (p : ℚ) - q := sub_pos.mpr (by exact_mod_cast hpq)
  set sumUV : ℤ :=
    ((p : ℤ) ^ V.length - q ^ V.length) * (wordWeightPQ p q U : ℤ) +
      (q : ℤ) ^ U.length * (wordWeightPQ p q V : ℤ)
  have hcomb_loQ : ((dmin : ℚ) * (p : ℚ) ^ U.length * ((p : ℚ) ^ V.length - q ^ V.length)) ≤
      ((p : ℚ) - q) * (sumUV : ℚ) := by
    have hthis : (dmin : ℤ) * B * A ≤ ((p : ℤ) - q) * sumUV := hcomb_lo
    have hcast := (Int.cast_le (R := ℚ)).mpr hthis
    simpa [B, A] using hcast
  have hcomb_hiQ : ((p : ℚ) - q) * (sumUV : ℚ) ≤
      ((dmax : ℚ) * (p : ℚ) ^ U.length * ((p : ℚ) ^ V.length - q ^ V.length)) := by
    have hthis : ((p : ℤ) - q) * sumUV ≤ (dmax : ℤ) * B * A := hcomb_hi
    have hcast := (Int.cast_le (R := ℚ)).mpr hthis
    simpa [B, A] using hcast
  have hqeq : qStarPQ p q U V =
      -(sumUV : ℚ) / ((p : ℚ) ^ U.length * ((p : ℚ) ^ V.length - (q : ℚ) ^ V.length)) := rfl
  rw [hqeq]
  constructor
  · rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hBAposQ hpqQ]
    linarith [hcomb_hiQ]
  · rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hpqQ hBAposQ]
    linarith [hcomb_loQ]

/-- **Two-place isolation for general `(p, q)`**: if `q < p` are coprime (`1 ≤ q`) and `g₀ ≥ 1`
matches `U V^w` (`|U| = r`, `|V| = s ≥ 1`), then
`q^{r + ws} ≤ (g₀ - q*) · p^r · (p^s - q^s) < (g₀ + dmax / (p - q)) · p^{r + s}`. -/
public theorem two_place_isolation_pq {p q dmin dmax g0 : ℕ} (hq : 1 ≤ q) (hpq : q < p)
    (hcop : Nat.Coprime p q) (hg0 : 1 ≤ g0) {U V : List ℕ}
    (hU : validWordPQ dmin dmax U) (hV : validWordPQ dmin dmax V) (hs : 0 < V.length) (w : ℕ)
    (hmatch : matchesWordPQ p q g0 (U ++ repeatWord V w)) :
    (q : ℚ) ^ (U.length + w * V.length) ≤
        ((g0 : ℚ) - qStarPQ p q U V) * (p : ℚ) ^ U.length *
          ((p : ℚ) ^ V.length - (q : ℚ) ^ V.length) ∧
      ((g0 : ℚ) - qStarPQ p q U V) * (p : ℚ) ^ U.length *
          ((p : ℚ) ^ V.length - (q : ℚ) ^ V.length) <
        ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ (U.length + V.length) := by
  obtain ⟨gL, hgL⟩ := hmatch
  set r := U.length
  set s := V.length
  have hlen : (U ++ repeatWord V w).length = r + w * s := by
    rw [List.length_append, repeatWord_length]
  rw [hlen, wordWeightPQ_append, repeatWord_length] at hgL
  rw [show U.length = r from rfl, show V.length = s from rfl] at hgL
  set N : ℤ :=
    (g0 : ℤ) * p ^ r * (p ^ s - q ^ s) +
      (p ^ s - q ^ s) * (wordWeightPQ p q U : ℤ) + (q : ℤ) ^ r * (wordWeightPQ p q V : ℤ)
  have hkey : (p : ℤ) ^ (w * s) * N =
      (q : ℤ) ^ (r + w * s) * (((p : ℤ) ^ s - q ^ s) * (gL : ℤ) + wordWeightPQ p q V) := by
    have hgLZ : (q : ℤ) ^ (r + w * s) * gL =
        (p : ℤ) ^ (r + w * s) * g0 +
          ((p : ℤ) ^ (w * s) * wordWeightPQ p q U +
            (q : ℤ) ^ r * wordWeightPQ p q (repeatWord V w)) := by
      exact_mod_cast hgL
    have hrep := wordWeightPQ_repeat_int p q V w
    have hgLZ' : ((p : ℤ) ^ s - q ^ s) * ((q : ℤ) ^ (r + w * s) * gL) =
        ((p : ℤ) ^ s - q ^ s) * ((p : ℤ) ^ (r + w * s) * g0) +
          ((p : ℤ) ^ s - q ^ s) * ((p : ℤ) ^ (w * s) * wordWeightPQ p q U) +
          (q : ℤ) ^ r * (((p : ℤ) ^ s - q ^ s) * wordWeightPQ p q (repeatWord V w)) := by
      rw [hgLZ]
      ring
    rw [hrep] at hgLZ'
    have hps : (p : ℤ) ^ (r + w * s) = (p : ℤ) ^ (w * s) * (p : ℤ) ^ r := by
      rw [add_comm, pow_add]
    have hqr : (q : ℤ) ^ (r + w * s) = (q : ℤ) ^ r * (q : ℤ) ^ (w * s) := by
      rw [pow_add]
    calc
      (p : ℤ) ^ (w * s) * N
          = (p : ℤ) ^ (w * s) * ((g0 : ℤ) * p ^ r * (p ^ s - q ^ s)) +
            (p : ℤ) ^ (w * s) * ((p ^ s - q ^ s) * wordWeightPQ p q U) +
            (p : ℤ) ^ (w * s) * ((q : ℤ) ^ r * wordWeightPQ p q V) := by
            dsimp [N]; ring
      _ = ((p : ℤ) ^ s - q ^ s) * ((p : ℤ) ^ (r + w * s) * g0) +
          ((p : ℤ) ^ s - q ^ s) * ((p : ℤ) ^ (w * s) * wordWeightPQ p q U) +
          (q : ℤ) ^ r * ((p : ℤ) ^ (w * s) * wordWeightPQ p q V) := by
            rw [hps]; ring
      _ = ((p : ℤ) ^ s - q ^ s) * ((q : ℤ) ^ (r + w * s) * gL) -
          (q : ℤ) ^ r * (((p : ℤ) ^ (w * s) - q ^ (w * s)) * wordWeightPQ p q V) +
          (q : ℤ) ^ r * ((p : ℤ) ^ (w * s) * wordWeightPQ p q V) := by
            linarith
      _ = (q : ℤ) ^ (r + w * s) * (((p : ℤ) ^ s - q ^ s) * (gL : ℤ) + wordWeightPQ p q V) := by
            rw [hqr]; ring
  have hdvd_nat : q ^ (r + w * s) ∣ p ^ (w * s) * N.natAbs := by
    have hdvdZ : (q : ℤ) ^ (r + w * s) ∣ (p : ℤ) ^ (w * s) * N :=
      ⟨((p : ℤ) ^ s - q ^ s) * (gL : ℤ) + wordWeightPQ p q V, hkey⟩
    simpa [Int.natAbs_mul, Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hdvdZ
  have hcop_pow : Nat.Coprime (q ^ (r + w * s)) (p ^ (w * s)) :=
    (hcop.symm.pow_left (r + w * s)).pow_right (w * s)
  have hq_dvd_N : q ^ (r + w * s) ∣ N.natAbs := hcop_pow.dvd_of_dvd_mul_left hdvd_nat
  have hp_gt : (q : ℤ) ^ s < (p : ℤ) ^ s := by
    exact_mod_cast Nat.pow_lt_pow_left hpq hs.ne'
  have hN_pos : 0 < N := by
    have hps_pos : (0 : ℤ) < (p : ℤ) ^ s - q ^ s := by linarith
    have hpr_pos : (0 : ℤ) < (p : ℤ) ^ r := pow_pos (by grind) _
    have hg_pos : (0 : ℤ) < (g0 : ℤ) * (p : ℤ) ^ r * ((p : ℤ) ^ s - q ^ s) :=
      mul_pos (mul_pos (by exact_mod_cast hg0) hpr_pos) hps_pos
    have hW1 : (0 : ℤ) ≤ (p ^ s - q ^ s) * (wordWeightPQ p q U : ℤ) :=
      mul_nonneg hps_pos.le (by positivity)
    have hW2 : (0 : ℤ) ≤ (q : ℤ) ^ r * (wordWeightPQ p q V : ℤ) := by positivity
    dsimp [N]
    linarith
  have hN_ge : (q : ℤ) ^ (r + w * s) ≤ N := by
    have hpos_nat : 0 < N.natAbs := by grind
    have hle_nat := Nat.le_of_dvd hpos_nat hq_dvd_N
    have hN_eq : (N.natAbs : ℤ) = N := Int.natAbs_of_nonneg hN_pos.le
    rw [← hN_eq]
    exact_mod_cast hle_nat
  have hN_id : (N : ℚ) =
      ((g0 : ℚ) - qStarPQ p q U V) * (p : ℚ) ^ r * ((p : ℚ) ^ s - (q : ℚ) ^ s) := by
    have hp_pos : (0 : ℚ) < (p : ℚ) ^ r :=
      pow_pos (by exact_mod_cast (by grind : 0 < p)) _
    have hsub_pos : (0 : ℚ) < (p : ℚ) ^ s - (q : ℚ) ^ s := by
      exact_mod_cast sub_pos.mpr hp_gt
    have hpq_diff : ((p : ℚ) ^ r * ((p : ℚ) ^ s - (q : ℚ) ^ s)) ≠ 0 :=
      (mul_pos hp_pos hsub_pos).ne'
    dsimp [N]
    unfold qStarPQ
    rw [show U.length = r from rfl, show V.length = s from rfl]
    field_simp [hpq_diff]
    push_cast
    ring
  have hloQ : (q : ℚ) ^ (r + w * s) ≤ (N : ℚ) := by exact_mod_cast hN_ge
  obtain ⟨hqlo, _⟩ := qStarPQ_bounds hpq hU hV hs
  have hdiff_lt : (p : ℚ) ^ s - (q : ℚ) ^ s < (p : ℚ) ^ s := by
    have : (0 : ℚ) < (q : ℚ) ^ s := pow_pos (by exact_mod_cast hq) _
    linarith
  have hgq_pos : 0 < (g0 : ℚ) - qStarPQ p q U V := by
    have hq_nonpos : qStarPQ p q U V ≤ 0 := by
      obtain ⟨_, hqup⟩ := qStarPQ_bounds hpq hU hV hs
      have hpq_pos : (0 : ℚ) < (p : ℚ) - q := sub_pos.mpr (by exact_mod_cast hpq)
      have hdiv_nn : 0 ≤ (dmin : ℚ) / ((p : ℚ) - q) := div_nonneg (by positivity) hpq_pos.le
      linarith
    have hg1 : (1 : ℚ) ≤ g0 := by exact_mod_cast hg0
    linarith
  have hp_pos : (0 : ℚ) < (p : ℚ) ^ r :=
    pow_pos (by exact_mod_cast (by grind : 0 < p)) _
  have hmul_lt : ((g0 : ℚ) - qStarPQ p q U V) * (p : ℚ) ^ r * ((p : ℚ) ^ s - (q : ℚ) ^ s) <
      ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ (r + s) := by
    have h1 : ((g0 : ℚ) - qStarPQ p q U V) * (p : ℚ) ^ r * ((p : ℚ) ^ s - (q : ℚ) ^ s) ≤
        ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ r * ((p : ℚ) ^ s - (q : ℚ) ^ s) := by
      have hsub_nn : 0 ≤ (p : ℚ) ^ s - (q : ℚ) ^ s := by exact_mod_cast sub_nonneg.mpr hp_gt.le
      gcongr
      linarith
    have h2 : ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ r *
          ((p : ℚ) ^ s - (q : ℚ) ^ s) <
        ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ r * (p : ℚ) ^ s := by
      have hpq_pos : (0 : ℚ) < (p : ℚ) - q := sub_pos.mpr (by exact_mod_cast hpq)
      have hfac_pos : 0 < ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ r := by
        have : (0 : ℚ) < g0 := by exact_mod_cast hg0
        exact mul_pos (by positivity) hp_pos
      exact mul_lt_mul_of_pos_left hdiff_lt hfac_pos
    calc
      ((g0 : ℚ) - qStarPQ p q U V) * (p : ℚ) ^ r * ((p : ℚ) ^ s - (q : ℚ) ^ s)
          ≤ ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ r *
              ((p : ℚ) ^ s - (q : ℚ) ^ s) := h1
      _ < ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ r * (p : ℚ) ^ s := h2
      _ = ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ (r + s) := by
            rw [pow_add]; ring
  rw [hN_id] at hloQ
  exact ⟨hloQ, hmul_lt⟩

/-- **Unconditional exclusion of eventually periodic `(p, q)` orbits** (`2 ≤ q < p`, coprime). -/
public theorem no_eventually_periodic_pq {p q dmin dmax g0 : ℕ} (hq : 2 ≤ q) (hpq : q < p)
    (hcop : Nat.Coprime p q) (hg0 : 1 ≤ g0) {U V : List ℕ}
    (hU : validWordPQ dmin dmax U) (hV : validWordPQ dmin dmax V) (hs : 0 < V.length) :
    ¬ ∀ w : ℕ, matchesWordPQ p q g0 (U ++ repeatWord V w) := by
  intro hall
  set w := (g0 + dmax + 1) * p ^ (U.length + V.length)
  obtain ⟨hlo, hhi⟩ := two_place_isolation_pq (by grind) hpq hcop hg0 hU hV hs w (hall w)
  have hcmp :
      (q : ℚ) ^ (U.length + w * V.length) <
        ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ (U.length + V.length) :=
    lt_of_le_of_lt hlo hhi
  have hpq_ge1 : (1 : ℚ) ≤ (p : ℚ) - q := by
    have : (q : ℚ) + 1 ≤ p := by exact_mod_cast hpq
    linarith
  have hdiv_le : (dmax : ℚ) / ((p : ℚ) - q) ≤ dmax :=
    div_le_self (by positivity) hpq_ge1
  have hnat : q ^ (U.length + w * V.length) < (g0 + dmax + 1) * p ^ (U.length + V.length) := by
    have hp_pos : (0 : ℚ) < (p : ℚ) ^ (U.length + V.length) :=
      pow_pos (by exact_mod_cast (by grind : 0 < p)) _
    have hq_lt : ((q ^ (U.length + w * V.length) : ℕ) : ℚ) <
        (((g0 + dmax + 1) * p ^ (U.length + V.length) : ℕ) : ℚ) := by
      push_cast
      nlinarith
    exact_mod_cast hq_lt
  have hw_lt_qw : w < q ^ w := by
    have h2 : w < 2 ^ w := Nat.lt_two_pow_self
    have h2q : 2 ^ w ≤ q ^ w := Nat.pow_le_pow_left hq w
    grind
  have hqw_le : q ^ w ≤ q ^ (U.length + w * V.length) := by
    refine Nat.pow_le_pow_right (by grind) ?_
    have h1 : w ≤ w * V.length := Nat.le_mul_of_pos_right w hs
    grind
  grind

/-- **General `(p, q)` repetition-exponent bound (critical threshold `log_q p`)**:
if `g₀` matches `U V^w`, then
`w < log p / log q + (log p / log q - 1) * (r / s) + log(g₀ + dmax / (p - q)) / (s * log q)`. -/
public theorem repetition_exponent_bound_pq {p q dmin dmax g0 w : ℕ} (hq : 2 ≤ q) (hpq : q < p)
    (hcop : Nat.Coprime p q) (hg0 : 1 ≤ g0) {U V : List ℕ}
    (hU : validWordPQ dmin dmax U) (hV : validWordPQ dmin dmax V) (hs : 0 < V.length)
    (hmatch : matchesWordPQ p q g0 (U ++ repeatWord V w)) :
    (w : ℝ) < Real.log p / Real.log q +
      (Real.log p / Real.log q - 1) * ((U.length : ℝ) / (V.length : ℝ)) +
      Real.log ((g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q)) /
        ((V.length : ℝ) * Real.log q) := by
  obtain ⟨hlo, hhi⟩ := two_place_isolation_pq (by grind) hpq hcop hg0 hU hV hs w hmatch
  have hcmpQ :
      (q : ℚ) ^ (U.length + w * V.length) <
        ((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ (U.length + V.length) :=
    lt_of_le_of_lt hlo hhi
  have hcmpR :
      (q : ℝ) ^ (U.length + w * V.length) <
        ((g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q)) * (p : ℝ) ^ (U.length + V.length) := by
    have hcast : (((q : ℚ) ^ (U.length + w * V.length) : ℚ) : ℝ) <
        ((((g0 : ℚ) + (dmax : ℚ) / ((p : ℚ) - q)) * (p : ℚ) ^ (U.length + V.length) : ℚ) : ℝ) :=
      by exact_mod_cast hcmpQ
    simpa using hcast
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by grind : 0 < q)
  have hppos : (0 : ℝ) < p := by exact_mod_cast (by grind : 0 < p)
  have hq_pow_pos : (0 : ℝ) < (q : ℝ) ^ (U.length + w * V.length) := pow_pos hqpos _
  have hpqR : (0 : ℝ) < (p : ℝ) - q := sub_pos.mpr (by exact_mod_cast hpq)
  have hg_pos : (0 : ℝ) < (g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q) := by
    have : (1 : ℝ) ≤ g0 := by exact_mod_cast hg0
    have : 0 ≤ (dmax : ℝ) / ((p : ℝ) - q) := div_nonneg (by positivity) hpqR.le
    linarith
  have hp_pow_pos : (0 : ℝ) < (p : ℝ) ^ (U.length + V.length) := pow_pos hppos _
  have hlog_lt :
      Real.log ((q : ℝ) ^ (U.length + w * V.length)) <
        Real.log (((g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q)) * (p : ℝ) ^ (U.length + V.length)) :=
    Real.log_lt_log hq_pow_pos hcmpR
  rw [Real.log_pow, Real.log_mul hg_pos.ne' hp_pow_pos.ne', Real.log_pow] at hlog_lt
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by grind : 1 < q))
  have hs_pos : (0 : ℝ) < V.length := by exact_mod_cast hs
  have hden_pos : 0 < (V.length : ℝ) * Real.log q := mul_pos hs_pos hlogq_pos
  rw [← sub_pos]
  have hscaled :
      0 < (Real.log p / Real.log q +
        (Real.log p / Real.log q - 1) * ((U.length : ℝ) / (V.length : ℝ)) +
        Real.log ((g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q)) /
          ((V.length : ℝ) * Real.log q) - (w : ℝ)) * ((V.length : ℝ) * Real.log q) := by
    have hid :
        (Real.log p / Real.log q +
          (Real.log p / Real.log q - 1) * ((U.length : ℝ) / (V.length : ℝ)) +
          Real.log ((g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q)) /
            ((V.length : ℝ) * Real.log q) - (w : ℝ)) * ((V.length : ℝ) * Real.log q) =
          (Real.log ((g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q)) +
            ((U.length + V.length : ℕ) : ℝ) * Real.log p) -
            ((U.length + w * V.length : ℕ) : ℝ) * Real.log q := by
      push_cast
      field_simp [hs_pos.ne', hlogq_pos.ne']
      ring
    linarith
  exact pos_of_mul_pos_left hscaled hden_pos.le


/-! ### 2. General `(p, q)` tunnel Fourier decay & quantitative Weyl equidistribution -/

private lemma prod_le_prod_nat (s : Finset ℕ) (f g : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hle : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    have hps : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hfs
    exact mul_le_mul hle (ih hfs hfgs) hps (le_trans hfa hle)

private lemma prod_le_one_nat (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := by
  simpa using prod_le_prod_nat s f (fun _ => 1) hf h1

/-- Construct a `TunnelModelPQ` canonically for any coprime `p > q ≥ 2` and digit baseline `d0`. -/
@[expose] public def TunnelModelPQ.mkConsecutive (p q d0 : ℕ) (hq : 2 ≤ q) (hpq : q < p)
    (hcop : Nat.Coprime p q) : TunnelModelPQ :=
  letI : NeZero q := ⟨by grind⟩
  let r1z : ZMod q := (-(d0 + 1 : ℕ) : ZMod q) * ((p : ZMod q)⁻¹)
  let r2z : ZMod q := (-(d0 : ℕ) : ZMod q) * ((p : ZMod q)⁻¹)
  { p := p
    q := q
    d0 := d0
    r1 := r1z.val
    r2 := r2z.val
    hq := hq
    hpq := hpq
    hcop := hcop
    hr1_lt := ZMod.val_lt r1z
    hr2_lt := ZMod.val_lt r2z
    hr_ne := by
      intro heq
      have hz : r1z = r2z := by
        rw [← ZMod.natCast_zmod_val r1z, ← ZMod.natCast_zmod_val r2z, heq]
      have hmul := congrArg (fun x => (p : ZMod q) * x) hz
      have hinv : (p : ZMod q) * (p : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one p hcop
      have hdiff : ((1 : ℕ) : ZMod q) = 0 := by
        dsimp [r1z, r2z] at hmul
        calc
          ((1 : ℕ) : ZMod q)
              = ((d0 + 1 : ℕ) : ZMod q) * 1 - ((d0 : ℕ) : ZMod q) * 1 := by
                  push_cast; ring
          _ = ((d0 + 1 : ℕ) : ZMod q) * ((p : ZMod q) * (p : ZMod q)⁻¹) -
                ((d0 : ℕ) : ZMod q) * ((p : ZMod q) * (p : ZMod q)⁻¹) := by
                  rw [hinv]
          _ = (p : ZMod q) * (-((d0 : ℕ) : ZMod q) * (p : ZMod q)⁻¹) -
                (p : ZMod q) * (-((d0 + 1 : ℕ) : ZMod q) * (p : ZMod q)⁻¹) := by ring
          _ = 0 := by rw [← hmul, sub_self]
      have hq1 : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).mp hdiff
      have hqle : q ≤ 1 := Nat.le_of_dvd (by norm_num) hq1
      grind
    hmod1 := by
      have hz : ((p * r1z.val + (d0 + 1) : ℕ) : ZMod q) = 0 := by
        rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
        dsimp [r1z]
        calc
          (p : ZMod q) * (-((d0 + 1 : ℕ) : ZMod q) * (p : ZMod q)⁻¹) + ((d0 + 1 : ℕ) : ZMod q)
              = -((d0 + 1 : ℕ) : ZMod q) * ((p : ZMod q) * (p : ZMod q)⁻¹) +
                  ((d0 + 1 : ℕ) : ZMod q) := by ring
          _ = -((d0 + 1 : ℕ) : ZMod q) * 1 + ((d0 + 1 : ℕ) : ZMod q) := by
                rw [ZMod.coe_mul_inv_eq_one p hcop]
          _ = 0 := by ring
      exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ q).mp hz)
    hmod2 := by
      have hz : ((p * r2z.val + d0 : ℕ) : ZMod q) = 0 := by
        rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
        dsimp [r2z]
        calc
          (p : ZMod q) * (-((d0 : ℕ) : ZMod q) * (p : ZMod q)⁻¹) + ((d0 : ℕ) : ZMod q)
              = -((d0 : ℕ) : ZMod q) * ((p : ZMod q) * (p : ZMod q)⁻¹) +
                  ((d0 : ℕ) : ZMod q) := by ring
          _ = -((d0 : ℕ) : ZMod q) * 1 + ((d0 : ℕ) : ZMod q) := by
                rw [ZMod.coe_mul_inv_eq_one p hcop]
          _ = 0 := by ring
      exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ q).mp hz) }

private lemma eChar_add (a b : ℝ) : eChar (a + b) = eChar a * eChar b := by
  unfold eChar
  push_cast
  rw [mul_add, Complex.exp_add]

private lemma eChar_add_int (a : ℝ) (n : ℤ) : eChar (a + n) = eChar a := by
  rw [eChar_add]
  have h1 : eChar n = 1 := by
    unfold eChar
    push_cast
    have hmul : 2 * ↑Real.pi * Complex.I * (n : ℂ) = ↑n * (2 * ↑Real.pi * Complex.I) := by ring
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  rw [h1, mul_one]

private lemma norm_eChar (θ : ℝ) : ‖eChar θ‖ = 1 := by
  unfold eChar
  have h : 2 * ↑Real.pi * Complex.I * (θ : ℂ) = ↑(2 * Real.pi * θ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma eChar_consec_pair_norm (d0 : ℕ) (θ : ℝ) :
    ‖eChar (-((d0 + 1 : ℕ) : ℝ) * θ) + eChar (-(d0 : ℝ) * θ)‖ =
      2 * |Real.cos (Real.pi * θ)| := by
  have hfac :
      eChar (-((d0 + 1 : ℕ) : ℝ) * θ) + eChar (-(d0 : ℝ) * θ) =
        eChar (-(d0 : ℝ) * θ) * (eChar (-θ) + 1) := by
    have hsum : (-((d0 + 1 : ℕ) : ℝ) * θ) = -(d0 : ℝ) * θ + (-θ) := by
      push_cast; ring
    rw [hsum, eChar_add]
    ring
  have hnorm_main : ‖eChar (-θ) + 1‖ = 2 * |Real.cos (Real.pi * θ)| := by
    have hexp : eChar (-θ) = Complex.cos (2 * Real.pi * θ) -
        Complex.sin (2 * Real.pi * θ) * Complex.I := by
      unfold eChar
      have h : 2 * ↑Real.pi * Complex.I * ((-θ : ℝ) : ℂ) =
          (-(2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [h, Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg]
      ring
    have hsq : ‖eChar (-θ) + 1‖ ^ 2 = (2 * |Real.cos (Real.pi * θ)|) ^ 2 := by
      have h2pi : (2 : ℂ) * ↑Real.pi * ↑θ = ↑(2 * Real.pi * θ) := by push_cast; ring
      rw [hexp, h2pi, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.add_im,
        Complex.sub_im, Complex.mul_im, Complex.one_im]
      have h2m : Real.cos (2 * Real.pi * θ) = 2 * Real.cos (Real.pi * θ) ^ 2 - 1 := by
        rw [show 2 * Real.pi * θ = 2 * (Real.pi * θ) from by ring, Real.cos_two_mul]
      have hpyth := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
      nlinarith [sq_abs (Real.cos (Real.pi * θ))]
    have hnn1 : 0 ≤ ‖eChar (-θ) + 1‖ := norm_nonneg _
    have hnn2 : 0 ≤ 2 * |Real.cos (Real.pi * θ)| := by positivity
    nlinarith [sq_nonneg (‖eChar (-θ) + 1‖ - 2 * |Real.cos (Real.pi * θ)|)]
  rw [hfac, norm_mul, norm_eChar, one_mul, hnorm_main]

private lemma tunnel_step_add_q (M : TunnelModelPQ) (g t : ℕ) :
    M.step (g + M.q * t) = (M.step g).map (· + M.p * t) := by
  unfold TunnelModelPQ.step
  have hmod : (g + M.q * t) % M.q = g % M.q := Nat.add_mul_mod_self_left g M.q t
  rw [hmod]
  split_ifs with h1 h2
  · have hdvd1 : M.q ∣ (M.p * g + (M.d0 + 1)) := by
      have hm := Nat.dvd_of_mod_eq_zero M.hmod1
      rw [← Nat.mod_add_div g M.q, h1]
      have : M.p * (M.r1 + M.q * (g / M.q)) + (M.d0 + 1) =
          (M.p * M.r1 + (M.d0 + 1)) + M.q * (M.p * (g / M.q)) := by ring
      rw [this]
      exact dvd_add hm (dvd_mul_right _ _)
    have hdiv : (M.p * (g + M.q * t) + (M.d0 + 1)) / M.q =
        (M.p * g + (M.d0 + 1)) / M.q + M.p * t := by
      have : M.p * (g + M.q * t) + (M.d0 + 1) =
          (M.p * g + (M.d0 + 1)) + M.q * (M.p * t) := by ring
      have hqpos : 0 < M.q := by have := M.hq; grind
      rw [this, Nat.add_mul_div_left _ _ hqpos]
    simp [hdiv]
  · have hdvd2 : M.q ∣ (M.p * g + M.d0) := by
      have hm := Nat.dvd_of_mod_eq_zero M.hmod2
      rw [← Nat.mod_add_div g M.q, h2]
      have : M.p * (M.r2 + M.q * (g / M.q)) + M.d0 =
          (M.p * M.r2 + M.d0) + M.q * (M.p * (g / M.q)) := by ring
      rw [this]
      exact dvd_add hm (dvd_mul_right _ _)
    have hdiv : (M.p * (g + M.q * t) + M.d0) / M.q =
        (M.p * g + M.d0) / M.q + M.p * t := by
      have : M.p * (g + M.q * t) + M.d0 =
          (M.p * g + M.d0) + M.q * (M.p * t) := by ring
      have hqpos : 0 < M.q := by have := M.hq; grind
      rw [this, Nat.add_mul_div_left _ _ hqpos]
    simp [hdiv]
  · rfl

private lemma tunnel_iter_add_q_pow (M : TunnelModelPQ) (k t g : ℕ) :
    M.iter k (g + M.q ^ k * t) = (M.iter k g).map (· + M.p ^ k * t) := by
  induction k generalizing t g with
  | zero => simp [TunnelModelPQ.iter]
  | succ k ih =>
    simp only [TunnelModelPQ.iter]
    have hs : M.step (g + M.q ^ (k + 1) * t) =
        (M.step g).map (· + M.p * (M.q ^ k * t)) := by
      rw [show M.q ^ (k + 1) * t = M.q * (M.q ^ k * t) from by rw [pow_succ]; ring,
        tunnel_step_add_q]
    rw [hs]
    cases hsg : M.step g with
    | none => simp
    | some y =>
      simp only [Option.map_some, Option.bind_some]
      have hy : y + M.p * (M.q ^ k * t) = y + M.q ^ k * (M.p * t) := by ring
      rw [hy, ih]
      cases hiy : M.iter k y with
      | none => simp
      | some z =>
        simp only [Option.map_some]
        rw [pow_succ']
        ring_nf

private lemma tunnel_survives_add_q_pow (M : TunnelModelPQ) (k t g : ℕ) :
    M.survives k (g + M.q ^ k * t) ↔ M.survives k g := by
  simp [TunnelModelPQ.survives, tunnel_iter_add_q_pow]

private lemma tunnel_iter_add (M : TunnelModelPQ) (k m g : ℕ) :
    M.iter (k + m) g = (M.iter k g).bind (M.iter m) := by
  induction k generalizing g with
  | zero => simp [TunnelModelPQ.iter]
  | succ k ih =>
    simp only [Nat.succ_add, TunnelModelPQ.iter]
    cases M.step g <;> simp [ih]

private lemma tunnel_step_lt_of_mod (M : TunnelModelPQ) {g : ℕ}
    (h : g % M.q = M.r1 ∨ g % M.q = M.r2) :
    ∃ h1 : ℕ, M.step g = some h1 ∧
      ((g % M.q = M.r1 ∧ M.q * h1 = M.p * g + (M.d0 + 1)) ∨
        (g % M.q = M.r2 ∧ M.q * h1 = M.p * g + M.d0)) := by
  unfold TunnelModelPQ.step
  rcases h with h1 | h2
  · rw [ite_eq_left h1]
    have hdvd : M.q ∣ (M.p * g + (M.d0 + 1)) := by
      have hm := Nat.dvd_of_mod_eq_zero M.hmod1
      rw [← Nat.mod_add_div g M.q, h1]
      have : M.p * (M.r1 + M.q * (g / M.q)) + (M.d0 + 1) =
          (M.p * M.r1 + (M.d0 + 1)) + M.q * (M.p * (g / M.q)) := by ring
      rw [this]
      exact dvd_add hm (dvd_mul_right _ _)
    exact ⟨_, rfl, Or.inl ⟨h1, Nat.mul_div_cancel' hdvd⟩⟩
  · have hne : g % M.q ≠ M.r1 := fun he => M.hr_ne (he.symm.trans h2)
    rw [ite_eq_right hne, ite_eq_left h2]
    have hdvd : M.q ∣ (M.p * g + M.d0) := by
      have hm := Nat.dvd_of_mod_eq_zero M.hmod2
      rw [← Nat.mod_add_div g M.q, h2]
      have : M.p * (M.r2 + M.q * (g / M.q)) + M.d0 =
          (M.p * M.r2 + M.d0) + M.q * (M.p * (g / M.q)) := by ring
      rw [this]
      exact dvd_add hm (dvd_mul_right _ _)
    exact ⟨_, rfl, Or.inr ⟨h2, Nat.mul_div_cancel' hdvd⟩⟩

private lemma tunnel_survives_succ_add_q_pow (M : TunnelModelPQ) {K g0 : ℕ}
    (hg0 : M.survives K g0) :
    ∃ h : ℕ, M.iter K g0 = some h ∧
      ∀ t : ℕ, (M.survives (K + 1) (g0 + M.q ^ K * t) ↔
        (M.p ^ K * t + h) % M.q = M.r1 ∨ (M.p ^ K * t + h) % M.q = M.r2) := by
  obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hg0
  refine ⟨h, hh, fun t => ?_⟩
  have hadd : M.iter (K + 1) (g0 + M.q ^ K * t) =
      (M.iter K (g0 + M.q ^ K * t)).bind M.step := by
    rw [tunnel_iter_add]
    congr 1
    funext y
    simp [TunnelModelPQ.iter]
  have hiter : M.iter K (g0 + M.q ^ K * t) = some (h + M.p ^ K * t) := by
    rw [tunnel_iter_add_q_pow, hh, Option.map_some]
  unfold TunnelModelPQ.survives
  rw [hadd, hiter, Option.bind_some]
  have hcomm : h + M.p ^ K * t = M.p ^ K * t + h := add_comm _ _
  rw [hcomm]
  unfold TunnelModelPQ.step
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · simp [h1, h2]

private lemma tunnel_fiber_card_eq_two (M : TunnelModelPQ) (K g0 : ℕ) (hg0 : M.survives K g0) :
    ((Finset.range M.q).filter (fun t => M.survives (K + 1) (g0 + M.q ^ K * t))).card = 2 := by
  obtain ⟨h, _, hiff⟩ := tunnel_survives_succ_add_q_pow M hg0
  have hne : NeZero M.q := ⟨by have := M.hq; grind⟩
  have hcop : Nat.Coprime (M.p ^ K) M.q := M.hcop.pow_left K
  let t1 : ZMod M.q := ((M.r1 : ZMod M.q) - (h : ZMod M.q)) * ((M.p : ZMod M.q) ^ K)⁻¹
  let t2 : ZMod M.q := ((M.r2 : ZMod M.q) - (h : ZMod M.q)) * ((M.p : ZMod M.q) ^ K)⁻¹
  have hsol : ∀ t ∈ Finset.range M.q,
      ((M.p ^ K * t + h) % M.q = M.r1 ∨ (M.p ^ K * t + h) % M.q = M.r2) ↔
        t = t1.val ∨ t = t2.val := by
    intro t ht
    have htq : t < M.q := Finset.mem_range.mp ht
    have hz_iff : ∀ r : ℕ, r < M.q →
        ((M.p ^ K * t + h) % M.q = r ↔ (t : ZMod M.q) =
          ((r : ZMod M.q) - (h : ZMod M.q)) * ((M.p : ZMod M.q) ^ K)⁻¹) := by
      intro r hr
      have hinv : ((M.p : ZMod M.q) ^ K) * ((M.p : ZMod M.q) ^ K)⁻¹ = 1 := by
        rw [← Nat.cast_pow]
        exact ZMod.coe_mul_inv_eq_one (M.p ^ K) hcop
      constructor
      · intro hmod
        have hz : ((M.p ^ K * t + h : ℕ) : ZMod M.q) = (r : ZMod M.q) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by rw [Nat.ModEq, hmod, Nat.mod_eq_of_lt hr])
        push_cast at hz
        calc
          (t : ZMod M.q) = (t : ZMod M.q) * (((M.p : ZMod M.q) ^ K) *
              ((M.p : ZMod M.q) ^ K)⁻¹) := by rw [hinv, mul_one]
          _ = (((M.p : ZMod M.q) ^ K * (t : ZMod M.q) + (h : ZMod M.q)) - (h : ZMod M.q)) *
              ((M.p : ZMod M.q) ^ K)⁻¹ := by ring
          _ = ((r : ZMod M.q) - (h : ZMod M.q)) * ((M.p : ZMod M.q) ^ K)⁻¹ := by rw [hz]
      · intro hteq
        have hz : ((M.p ^ K * t + h : ℕ) : ZMod M.q) = (r : ZMod M.q) := by
          push_cast
          rw [hteq]
          calc
            (M.p : ZMod M.q) ^ K * (((r : ZMod M.q) - (h : ZMod M.q)) *
                ((M.p : ZMod M.q) ^ K)⁻¹) + (h : ZMod M.q)
                = ((r : ZMod M.q) - (h : ZMod M.q)) *
                    ((M.p : ZMod M.q) ^ K * ((M.p : ZMod M.q) ^ K)⁻¹) + (h : ZMod M.q) := by ring
            _ = (r : ZMod M.q) := by rw [hinv, mul_one]; ring
        have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hr] at hmod
    rw [hz_iff M.r1 M.hr1_lt, hz_iff M.r2 M.hr2_lt]
    constructor
    · rintro (h1 | h2)
      · exact Or.inl ((ZMod.val_natCast_of_lt htq).symm.trans (congrArg ZMod.val h1))
      · exact Or.inr ((ZMod.val_natCast_of_lt htq).symm.trans (congrArg ZMod.val h2))
    · rintro (rfl | rfl)
      · exact Or.inl (ZMod.natCast_zmod_val t1)
      · exact Or.inr (ZMod.natCast_zmod_val t2)
  have hfilter : (Finset.range M.q).filter (fun t => M.survives (K + 1) (g0 + M.q ^ K * t)) =
      ({t1.val, t2.val} : Finset ℕ) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hs⟩
      exact (hsol t (Finset.mem_range.mpr ht)).mp ((hiff t).mp hs)
    · rintro (rfl | rfl)
      · refine ⟨ZMod.val_lt t1, (hiff t1.val).mpr ?_⟩
        exact (hsol t1.val (Finset.mem_range.mpr (ZMod.val_lt t1))).mpr (Or.inl rfl)
      · refine ⟨ZMod.val_lt t2, (hiff t2.val).mpr ?_⟩
        exact (hsol t2.val (Finset.mem_range.mpr (ZMod.val_lt t2))).mpr (Or.inr rfl)
  have hne_val : t1.val ≠ t2.val := by
    intro heq
    have hz : t1 = t2 := by
      rw [← ZMod.natCast_zmod_val t1, ← ZMod.natCast_zmod_val t2, heq]
    have hmul := congrArg (fun x => (M.p : ZMod M.q) ^ K * x) hz
    have hinv : ((M.p : ZMod M.q) ^ K) * ((M.p : ZMod M.q) ^ K)⁻¹ = 1 := by
      rw [← Nat.cast_pow]
      exact ZMod.coe_mul_inv_eq_one (M.p ^ K) hcop
    have hr_eq : (M.r1 : ZMod M.q) = (M.r2 : ZMod M.q) := by
      dsimp [t1, t2] at hmul
      linear_combination hmul + ((M.r2 : ZMod M.q) - (M.r1 : ZMod M.q)) * hinv
    have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hr_eq
    rw [Nat.ModEq, Nat.mod_eq_of_lt M.hr1_lt, Nat.mod_eq_of_lt M.hr2_lt] at hm
    exact M.hr_ne hm
  rw [hfilter, Finset.card_pair hne_val]

private lemma sum_tunnel_survivors_succ {α : Type*} [AddCommMonoid α] (M : TunnelModelPQ)
    (K : ℕ) (f : ℕ → α) :
    ∑ g ∈ M.survivorsSet (K + 1), f g =
      ∑ g0 ∈ M.survivorsSet K,
        ∑ t ∈ (Finset.range M.q).filter (fun t => M.survives (K + 1) (g0 + M.q ^ K * t)),
          f (g0 + M.q ^ K * t) := by
  have hqpos : 0 < M.q ^ K := pow_pos (by have := M.hq; grind) K
  have hprod : M.survivorsSet (K + 1) =
      (((M.survivorsSet K ×ˢ Finset.range M.q).image
        (fun p => p.1 + M.q ^ K * p.2)).filter (fun g => M.survives (K + 1) g)) := by
    ext g
    simp only [TunnelModelPQ.survivorsSet, Finset.mem_filter, Finset.mem_range,
      Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨hg, hs⟩
      refine ⟨⟨(g % M.q ^ K, g / M.q ^ K), ⟨⟨Nat.mod_lt g hqpos, ?_⟩, ?_⟩, ?_⟩, hs⟩
      · have hsK : M.survives K g := by
          unfold TunnelModelPQ.survives at hs ⊢
          rw [tunnel_iter_add] at hs
          intro hnone
          rw [hnone, Option.bind_none] at hs
          exact hs rfl
        have hsplit := (Nat.mod_add_div g (M.q ^ K)).symm
        rwa [hsplit, tunnel_survives_add_q_pow] at hsK
      · rw [Nat.div_lt_iff_lt_mul hqpos, ← pow_succ']
        exact hg
      · dsimp only
        exact Nat.mod_add_div g (M.q ^ K)
    · rintro ⟨⟨⟨g0, t⟩, ⟨⟨hg0, _⟩, ht⟩, rfl⟩, hs⟩
      have hlt : g0 + M.q ^ K * t < M.q ^ (K + 1) := by
        rw [pow_succ']
        have h1 : t + 1 ≤ M.q := ht
        nlinarith
      exact ⟨hlt, hs⟩
  rw [hprod]
  have hmap : (((M.survivorsSet K ×ˢ Finset.range M.q).image
      (fun p => p.1 + M.q ^ K * p.2)).filter (fun g => M.survives (K + 1) g)) =
      (((M.survivorsSet K ×ˢ Finset.range M.q).filter
        (fun p => M.survives (K + 1) (p.1 + M.q ^ K * p.2))).image
        (fun p => p.1 + M.q ^ K * p.2)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hs⟩
      exact ⟨p, ⟨hp, hs⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hs⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hs⟩
  rw [hmap, Finset.sum_image]
  · rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun g0 _ => ?_
    rw [← Finset.sum_filter]
  · intro p1 hp1 p2 hp2 heq
    have h1 := ((Finset.mem_product.mp (Finset.mem_filter.mp hp1).1).1 |> Finset.mem_filter.mp).1
      |> Finset.mem_range.mp
    have h2 := ((Finset.mem_product.mp (Finset.mem_filter.mp hp2).1).1 |> Finset.mem_filter.mp).1
      |> Finset.mem_range.mp
    have hm : p1.1 = p2.1 := by
      have hmod := congrArg (· % M.q ^ K) heq
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
      exact hmod
    have ht : p1.2 = p2.2 := by
      dsimp only at heq
      rw [hm] at heq
      have hmul : M.q ^ K * p1.2 = M.q ^ K * p2.2 := Nat.add_left_cancel heq
      exact Nat.mul_left_cancel hqpos hmul
    exact Prod.ext hm ht

/-- Cardinality of `M.survivorsSet K` is `2^K`. -/
public theorem card_survivorsSetPQ (M : TunnelModelPQ) (K : ℕ) :
    (M.survivorsSet K).card = 2 ^ K := by
  have hC : ((M.survivorsSet K).card : ℂ) = (2 : ℂ) ^ K := by
    induction K with
    | zero =>
      have : M.survivorsSet 0 = {0} := by
        ext g
        simp [TunnelModelPQ.survivorsSet, TunnelModelPQ.survives, TunnelModelPQ.iter]
      rw [this, Finset.card_singleton]
      norm_num
    | succ K ih =>
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [sum_tunnel_survivors_succ]
      have hterm : ∑ g0 ∈ M.survivorsSet K,
          ∑ _t ∈ (Finset.range M.q).filter (fun t => M.survives (K + 1) (g0 + M.q ^ K * t)),
            (1 : ℂ) = ∑ _g0 ∈ M.survivorsSet K, (2 : ℂ) := by
        refine Finset.sum_congr rfl fun g0 hg0 => ?_
        have hg0s : M.survives K g0 := (Finset.mem_filter.mp hg0).2
        simp [tunnel_fiber_card_eq_two M K g0 hg0s]
      rw [hterm, Finset.sum_const, nsmul_eq_mul, ih, ← pow_succ]
  exact_mod_cast hC

/-- **Exact `q`-contraction identity**: `μ̂_{K+1}(q u) = μ̂_K(u)`. -/
public theorem hatMuPQ_mul_q (M : TunnelModelPQ) (K : ℕ) (u : ℤ) :
    M.hatMu (K + 1) (M.q * u) = M.hatMu K u := by
  unfold TunnelModelPQ.hatMu
  rw [sum_tunnel_survivors_succ]
  simp only [Int.cast_mul, Int.cast_natCast]
  have hsum : ∑ g0 ∈ M.survivorsSet K,
      ∑ t ∈ (Finset.range M.q).filter (fun t => M.survives (K + 1) (g0 + M.q ^ K * t)),
        eChar (((M.q : ℝ) * (u : ℝ) * ((g0 + M.q ^ K * t : ℕ) : ℝ)) / (M.q : ℝ) ^ (K + 1)) =
      ∑ g0 ∈ M.survivorsSet K, 2 * eChar (((u : ℝ) * (g0 : ℝ)) / (M.q : ℝ) ^ K) := by
    refine Finset.sum_congr rfl fun g0 hg0 => ?_
    have hg0s : M.survives K g0 := (Finset.mem_filter.mp hg0).2
    have hconst : ∀ t ∈ (Finset.range M.q).filter (fun t => M.survives (K + 1) (g0 + M.q ^ K * t)),
        eChar (((M.q : ℝ) * (u : ℝ) * ((g0 + M.q ^ K * t : ℕ) : ℝ)) / (M.q : ℝ) ^ (K + 1)) =
          eChar (((u : ℝ) * (g0 : ℝ)) / (M.q : ℝ) ^ K) := by
      intro t _
      have harg :
          ((M.q : ℝ) * (u : ℝ) * ((g0 + M.q ^ K * t : ℕ) : ℝ)) / (M.q : ℝ) ^ (K + 1) =
            ((u : ℝ) * (g0 : ℝ)) / (M.q : ℝ) ^ K + ((u * (t : ℤ) : ℤ) : ℝ) := by
        have hq0_nat : M.q ≠ 0 := by have := M.hq; grind
        have hqK : (M.q : ℝ) ^ K ≠ 0 := pow_ne_zero K (by exact_mod_cast hq0_nat)
        have hq0 : (M.q : ℝ) ≠ 0 := by exact_mod_cast hq0_nat
        rw [pow_succ']
        push_cast
        field_simp [hqK, hq0]
      rw [harg, eChar_add_int]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, tunnel_fiber_card_eq_two M K g0 hg0s,
      nsmul_eq_mul]
    norm_num
  rw [hsum, ← Finset.mul_sum, pow_succ]
  have h2K : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero K (by norm_num)
  field_simp [h2K]

/-- Iterated `q`-contraction: `μ̂_K(q^v u) = μ̂_{K-v}(u)` for `v ≤ K`. -/
public theorem hatMuPQ_q_pow_mul (M : TunnelModelPQ) {K v : ℕ} (hv : v ≤ K) (u : ℤ) :
    M.hatMu K ((M.q : ℤ) ^ v * u) = M.hatMu (K - v) u := by
  induction v generalizing K with
  | zero => simp
  | succ v ih =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by grind⟩
    have hv' : v ≤ K' := by grind
    have hmul : (M.q : ℤ) ^ (v + 1) * u = M.q * ((M.q : ℤ) ^ v * u) := by
      rw [pow_succ']; ring
    rw [hmul, hatMuPQ_mul_q, ih hv', show K' + 1 - (v + 1) = K' - v from by grind]

/-- Iterated `q`-contraction in norm: `‖μ̂_K(q^v u)‖ = ‖μ̂_{K-v}(u)‖`. -/
public theorem norm_hatMuPQ_q_pow_mul (M : TunnelModelPQ) {K v : ℕ} (hv : v ≤ K) (u : ℤ) :
    ‖M.hatMu K ((M.q : ℤ) ^ v * u)‖ = ‖M.hatMu (K - v) u‖ := by
  rw [hatMuPQ_q_pow_mul M hv u]

private lemma zmod_p_inv_dvd (M : TunnelModelPQ) (K : ℕ) :
    (M.q : ℤ) ^ K ∣ ((M.p : ℤ) * (ZMod.val ((M.p : ZMod (M.q ^ K))⁻¹) : ℤ) - 1) := by
  have hne : NeZero (M.q ^ K) := ⟨(pow_pos (by have := M.hq; grind) K).ne'⟩
  have hcop : Nat.Coprime M.p (M.q ^ K) := M.hcop.pow_right K
  rw [← show ((M.q ^ K : ℕ) : ℤ) = (M.q : ℤ) ^ K from by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val,
    show (M.p : ZMod (M.q ^ K)) = ((M.p : ℕ) : ZMod (M.q ^ K)) from rfl,
    ZMod.coe_mul_inv_eq_one M.p hcop, sub_self]

private lemma linear_mod_q_pow_bij (M : TunnelModelPQ) (K d : ℕ) :
    ∀ h0v ∈ M.survivorsSet K, ∃ n < M.q ^ K, (M.p * n + d) % M.q ^ K = h0v := by
  intro h0v hh0
  have hne : NeZero (M.q ^ K) := ⟨(pow_pos (by have := M.hq; grind) K).ne'⟩
  have hcop : Nat.Coprime M.p (M.q ^ K) := M.hcop.pow_right K
  let zq : ZMod (M.q ^ K) :=
    (M.p : ZMod (M.q ^ K))⁻¹ * ((h0v : ZMod (M.q ^ K)) - (d : ZMod (M.q ^ K)))
  refine ⟨ZMod.val zq, ZMod.val_lt zq, ?_⟩
  have hz : ((M.p * zq.val + d : ℕ) : ZMod (M.q ^ K)) = (h0v : ZMod (M.q ^ K)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    dsimp [zq]
    calc
      (M.p : ZMod (M.q ^ K)) * ((M.p : ZMod (M.q ^ K))⁻¹ * ((h0v : ZMod (M.q ^ K)) - d)) + d
          = ((M.p : ZMod (M.q ^ K)) * (M.p : ZMod (M.q ^ K))⁻¹) *
              ((h0v : ZMod (M.q ^ K)) - d) + d := by ring
      _ = 1 * ((h0v : ZMod (M.q ^ K)) - d) + d := by
            rw [show (M.p : ZMod (M.q ^ K)) = ((M.p : ℕ) : ZMod (M.q ^ K)) from rfl,
              ZMod.coe_mul_inv_eq_one M.p hcop]
      _ = (h0v : ZMod (M.q ^ K)) := by ring
  have hlt : h0v < M.q ^ K := (Finset.mem_filter.mp hh0).1 |> Finset.mem_range.mp
  exact Eq.trans ((ZMod.natCast_eq_natCast_iff _ _ _).mp hz) (Nat.mod_eq_of_lt hlt)

private lemma sum_tunnel_branch_p_mul (M : TunnelModelPQ) (K : ℕ) (u : ℤ) (r c d : ℕ)
    (hbranch : (r = M.r1 ∧ c = M.d0 + 1 ∧ d = M.d0 + 1) ∨ (r = M.r2 ∧ c = M.d0 ∧ d = M.d0)) :
    ∑ g ∈ (M.survivorsSet (K + 1)).filter (fun g => g % M.q = r),
        eChar (((M.p : ℤ) * u * (g : ℤ) : ℝ) / (M.q : ℝ) ^ (K + 1)) =
      eChar (-((d : ℤ) * u : ℝ) / (M.q : ℝ) ^ (K + 1)) *
        ∑ h0v ∈ M.survivorsSet K, eChar ((u * (h0v : ℤ) : ℝ) / (M.q : ℝ) ^ K) := by
  have hqpos : 0 < M.q := by have := M.hq; grind
  have hdvd_c : M.q ∣ (M.p * r + c) := by
    rcases hbranch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Nat.dvd_of_mod_eq_zero M.hmod1
    · exact Nat.dvd_of_mod_eq_zero M.hmod2
  have hcop : Nat.Coprime M.p (M.q ^ K) := M.hcop.pow_right K
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun g _ => (M.p * (g / M.q) + (M.p * r + c) / M.q) % M.q ^ K) ?_ ?_ ?_ ?_
  · intro g hg
    have hgmem := Finset.mem_filter.mp (Finset.mem_filter.mp hg).1
    have hg4 : g % M.q = r := (Finset.mem_filter.mp hg).2
    have hstep_mod : g % M.q = M.r1 ∨ g % M.q = M.r2 := by
      rcases hbranch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact Or.inl hg4; exact Or.inr hg4]
    have hstep_eq : M.step g = some (M.p * (g / M.q) + (M.p * r + c) / M.q) := by
      obtain ⟨h1, hs1, hrel⟩ := tunnel_step_lt_of_mod M hstep_mod
      have hqh1 : M.q * h1 = M.q * (M.p * (g / M.q) + (M.p * r + c) / M.q) := by
        have hsum : M.p * g + c = M.q * (M.p * (g / M.q)) + (M.p * r + c) := by
          have := (Nat.mod_add_div g M.q).symm
          rw [hg4] at this
          calc
            M.p * g + c = M.p * (r + M.q * (g / M.q)) + c := by rw [← this]
            _ = M.q * (M.p * (g / M.q)) + (M.p * r + c) := by ring
        have hqh1' : M.q * h1 = M.p * g + c := by
          rcases hbranch with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
          · rcases hrel with ⟨_, h⟩ | ⟨h2, _⟩
            · exact h
            · exact absurd h2 (fun he => M.hr_ne (hg4.symm.trans he))
          · rcases hrel with ⟨h1', _⟩ | ⟨_, h⟩
            · exact absurd h1' (fun he => M.hr_ne (he.symm.trans hg4))
            · exact h
        rw [hqh1', hsum, mul_add, Nat.mul_div_cancel' hdvd_c]
      have hh1_eq : h1 = M.p * (g / M.q) + (M.p * r + c) / M.q :=
        Nat.mul_left_cancel hqpos hqh1
      rwa [hh1_eq] at hs1
    have hsK : M.survives K (M.p * (g / M.q) + (M.p * r + c) / M.q) := by
      have hs := hgmem.2
      unfold TunnelModelPQ.survives at hs ⊢
      simpa [TunnelModelPQ.iter, hstep_eq] using hs
    have hsplit := (Nat.mod_add_div (M.p * (g / M.q) + (M.p * r + c) / M.q) (M.q ^ K)).symm
    rw [hsplit, tunnel_survives_add_q_pow] at hsK
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos hqpos K)), hsK⟩
  · intro g₁ hg₁ g₂ hg₂ heq
    have hg₁4 : g₁ % M.q = r := (Finset.mem_filter.mp hg₁).2
    have hg₂4 : g₂ % M.q = r := (Finset.mem_filter.mp hg₂).2
    have hg₁' := Finset.mem_filter.mp (Finset.mem_filter.mp hg₁).1
    have hg₂' := Finset.mem_filter.mp (Finset.mem_filter.mp hg₂).1
    have hdvd : M.q ^ K ∣ (((g₁ / M.q : ℕ) : ℤ) - ((g₂ / M.q : ℕ) : ℤ)).natAbs := by
      set k1 := M.p * (g₁ / M.q) + (M.p * r + c) / M.q
      set k2 := M.p * (g₂ / M.q) + (M.p * r + c) / M.q
      have hmod : k1 % M.q ^ K = k2 % M.q ^ K := heq
      have hdiff_nat : ((k1 : ℤ) - k2) % (M.q ^ K : ℕ) = 0 := by
        have h12 : (k1 : ℤ) % ((M.q ^ K : ℕ) : ℤ) = (k2 : ℤ) % ((M.q ^ K : ℕ) : ℤ) := by
          exact_mod_cast hmod
        rw [Int.sub_emod, h12, sub_self, Int.zero_emod]
      have hd : ((M.q ^ K : ℕ) : ℤ) ∣ (k1 : ℤ) - k2 := Int.dvd_of_emod_eq_zero hdiff_nat
      have hdiff : (k1 : ℤ) - k2 = (M.p : ℤ) * (((g₁ / M.q : ℕ) : ℤ) - ((g₂ / M.q : ℕ) : ℤ)) := by
        dsimp [k1, k2]; ring
      have hnat : M.q ^ K ∣ ((M.p : ℤ) * (((g₁ / M.q : ℕ) : ℤ) - ((g₂ / M.q : ℕ) : ℤ))).natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr (hdiff ▸ hd)
        simpa using this
      have : M.q ^ K ∣ M.p * (((g₁ / M.q : ℕ) : ℤ) - ((g₂ / M.q : ℕ) : ℤ)).natAbs := by
        rwa [Int.natAbs_mul] at hnat
      exact hcop.symm.dvd_of_dvd_mul_left this
    have hq1 : g₁ / M.q < M.q ^ K := by
      rw [Nat.div_lt_iff_lt_mul hqpos, ← pow_succ]
      exact Finset.mem_range.mp hg₁'.1
    have hq2 : g₂ / M.q < M.q ^ K := by
      rw [Nat.div_lt_iff_lt_mul hqpos, ← pow_succ]
      exact Finset.mem_range.mp hg₂'.1
    have hle : (((g₁ / M.q : ℕ) : ℤ) - ((g₂ / M.q : ℕ) : ℤ)).natAbs < M.q ^ K := by
      rcases le_or_gt (g₁ / M.q) (g₂ / M.q) with h12 | h12
      · have : ((g₁ / M.q : ℕ) : ℤ) - ((g₂ / M.q : ℕ) : ℤ) =
            -(((g₂ / M.q - g₁ / M.q : ℕ) : ℤ)) := by grind
        rw [this, Int.natAbs_neg, Int.natAbs_natCast]
        exact lt_of_le_of_lt (Nat.sub_le _ _) hq2
      · have : ((g₁ / M.q : ℕ) : ℤ) - ((g₂ / M.q : ℕ) : ℤ) =
            ((g₁ / M.q - g₂ / M.q : ℕ) : ℤ) := by grind
        rw [this, Int.natAbs_natCast]
        exact lt_of_le_of_lt (Nat.sub_le _ _) hq1
    have hzero := Nat.eq_zero_of_dvd_of_lt hdvd hle
    have hqeq : g₁ / M.q = g₂ / M.q := by grind [Int.natAbs_eq_zero]
    have hg1_eq : g₁ % M.q + M.q * (g₁ / M.q) = g₁ := Nat.mod_add_div g₁ M.q
    have hg2_eq : g₂ % M.q + M.q * (g₂ / M.q) = g₂ := Nat.mod_add_div g₂ M.q
    rw [← hg1_eq, ← hg2_eq, hg₁4, hg₂4, hqeq]
  · intro h0v hh0
    obtain ⟨n, hnlt, hnmod⟩ := linear_mod_q_pow_bij M K ((M.p * r + c) / M.q) h0v hh0
    refine ⟨M.q * n + r, ?_, ?_⟩
    · simp only [TunnelModelPQ.survivorsSet, Finset.mem_filter, Finset.mem_range] at hh0 ⊢
      have hrq : r < M.q := by
        rcases hbranch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact M.hr1_lt; exact M.hr2_lt]
      have hlt : M.q * n + r < M.q ^ (K + 1) := by rw [pow_succ']; nlinarith
      have hmod_r : (M.q * n + r) % M.q = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrq]
      have hstep_mod : (M.q * n + r) % M.q = M.r1 ∨ (M.q * n + r) % M.q = M.r2 := by
        rcases hbranch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact Or.inl hmod_r; exact Or.inr hmod_r]
      obtain ⟨h1, hs1, hrel⟩ := tunnel_step_lt_of_mod M hstep_mod
      have hh1_eq : h1 = M.p * n + (M.p * r + c) / M.q := by
        have hsum : M.p * (M.q * n + r) + c = M.q * (M.p * n) + (M.p * r + c) := by ring
        have hqh1' : M.q * h1 = M.p * (M.q * n + r) + c := by
          rcases hbranch with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
          · rcases hrel with ⟨_, h⟩ | ⟨h2, _⟩
            · exact h
            · exact absurd h2 (fun he => M.hr_ne (hmod_r.symm.trans he))
          · rcases hrel with ⟨h1', _⟩ | ⟨_, h⟩
            · exact absurd h1' (fun he => M.hr_ne (he.symm.trans hmod_r))
            · exact h
        have hqh1 : M.q * h1 = M.q * (M.p * n + (M.p * r + c) / M.q) := by
          rw [hqh1', hsum, mul_add, Nat.mul_div_cancel' hdvd_c]
        exact Nat.mul_left_cancel hqpos hqh1
      have hs : M.survives (K + 1) (M.q * n + r) := by
        unfold TunnelModelPQ.survives
        rw [TunnelModelPQ.iter, hs1, hh1_eq, Option.bind_some]
        change M.survives K (M.p * n + (M.p * r + c) / M.q)
        have hsplit := (Nat.mod_add_div (M.p * n + (M.p * r + c) / M.q) (M.q ^ K)).symm
        rw [hsplit, tunnel_survives_add_q_pow, hnmod]
        exact hh0.2
      exact ⟨⟨hlt, hs⟩, hmod_r⟩
    · have hrq : r < M.q := by
        rcases hbranch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact M.hr1_lt; exact M.hr2_lt]
      have hdiv : (M.q * n + r) / M.q = n := by
        rw [Nat.mul_add_div hqpos, Nat.div_eq_of_lt hrq, add_zero]
      rw [hdiv, hnmod]
  · intro g hg
    have hg4 : g % M.q = r := (Finset.mem_filter.mp hg).2
    have hstep_id : M.q * (M.p * (g / M.q) + (M.p * r + c) / M.q) = M.p * g + d := by
      have hc_eq : c = d := by rcases hbranch with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> rfl
      have hmodg : r + M.q * (g / M.q) = g := by rw [← hg4, Nat.mod_add_div]
      rw [mul_add, Nat.mul_div_cancel' hdvd_c, hc_eq]
      calc
        M.q * (M.p * (g / M.q)) + (M.p * r + d)
            = M.p * (r + M.q * (g / M.q)) + d := by ring
        _ = M.p * g + d := by rw [hmodg]
    set h := M.p * (g / M.q) + (M.p * r + c) / M.q
    have hdiv_mod : h = h % M.q ^ K + M.q ^ K * (h / M.q ^ K) := (Nat.mod_add_div h (M.q ^ K)).symm
    have harg : (((M.p : ℤ) * u) * (g : ℤ) : ℝ) / (M.q : ℝ) ^ (K + 1) =
        (-((d : ℤ) * u : ℝ) / (M.q : ℝ) ^ (K + 1) +
          (u * ((h % M.q ^ K : ℕ) : ℤ) : ℝ) / (M.q : ℝ) ^ K) +
          ((u * ((h / M.q ^ K : ℕ) : ℤ) : ℤ) : ℝ) := by
      have hqK : (M.q : ℝ) ^ K ≠ 0 := pow_ne_zero K (by exact_mod_cast hqpos.ne')
      have hq0 : (M.q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
      have hpg : (M.p : ℝ) * (g : ℝ) = (M.q : ℝ) * ((h : ℕ) : ℝ) - (d : ℝ) := by
        have : ((M.q * h : ℕ) : ℝ) = ((M.p * g + d : ℕ) : ℝ) := by exact_mod_cast hstep_id
        push_cast at this
        linarith
      have hdiv_r : ((h : ℕ) : ℝ) =
          ((h % M.q ^ K : ℕ) : ℝ) + (M.q : ℝ) ^ K * ((h / M.q ^ K : ℕ) : ℝ) := by
        exact_mod_cast hdiv_mod
      rw [pow_succ']
      simp only [Int.cast_mul, Int.cast_natCast]
      field_simp [hqK, hq0]
      rw [show (M.p : ℝ) * (u : ℝ) * (g : ℝ) = (u : ℝ) * ((M.p : ℝ) * (g : ℝ)) from by ring, hpg,
        hdiv_r]
      ring
    rw [harg, eChar_add_int, eChar_add]

/-- One-step `p`-multiplication formula for `M.hatMu`. -/
public theorem hatMuPQ_p_mul (M : TunnelModelPQ) (K : ℕ) (u : ℤ) :
    M.hatMu (K + 1) (M.p * u) =
      ((eChar (-((M.d0 + 1 : ℕ) : ℝ) * (u : ℝ) / (M.q : ℝ) ^ (K + 1)) +
        eChar (-(M.d0 : ℝ) * (u : ℝ) / (M.q : ℝ) ^ (K + 1))) / 2) * M.hatMu K u := by
  have hpart : ∑ g ∈ M.survivorsSet (K + 1),
        eChar (((M.p : ℤ) * u * (g : ℤ) : ℝ) / (M.q : ℝ) ^ (K + 1)) =
      (∑ g ∈ (M.survivorsSet (K + 1)).filter (fun g => g % M.q = M.r1),
        eChar (((M.p : ℤ) * u * (g : ℤ) : ℝ) / (M.q : ℝ) ^ (K + 1))) +
      ∑ g ∈ (M.survivorsSet (K + 1)).filter (fun g => g % M.q = M.r2),
        eChar (((M.p : ℤ) * u * (g : ℤ) : ℝ) / (M.q : ℝ) ^ (K + 1)) := by
    have hsplit : M.survivorsSet (K + 1) =
        (M.survivorsSet (K + 1)).filter (fun g => g % M.q = M.r1) ∪
          (M.survivorsSet (K + 1)).filter (fun g => g % M.q = M.r2) := by
      ext g
      simp only [Finset.mem_union, Finset.mem_filter, TunnelModelPQ.survivorsSet, Finset.mem_range]
      constructor
      · rintro ⟨hg, hs⟩
        have hstep : M.step g ≠ none := by
          unfold TunnelModelPQ.survives at hs
          intro hnone
          rw [TunnelModelPQ.iter, hnone, Option.bind_none] at hs
          exact hs rfl
        have h12 : g % M.q = M.r1 ∨ g % M.q = M.r2 := by
          by_contra hcon
          push Not at hcon
          apply hstep
          simp [TunnelModelPQ.step, hcon.1, hcon.2]
        rcases h12 with h1 | h2
        · exact Or.inl ⟨⟨hg, hs⟩, h1⟩
        · exact Or.inr ⟨⟨hg, hs⟩, h2⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hdisj : Disjoint ((M.survivorsSet (K + 1)).filter (fun g => g % M.q = M.r1))
        ((M.survivorsSet (K + 1)).filter (fun g => g % M.q = M.r2)) := by
      rw [Finset.disjoint_filter]
      intro g _ h1 h2
      exact M.hr_ne (h1.symm.trans h2)
    conv_lhs => rw [hsplit, Finset.sum_union hdisj]
  have h1 := sum_tunnel_branch_p_mul M K u M.r1 (M.d0 + 1) (M.d0 + 1) (Or.inl ⟨rfl, rfl, rfl⟩)
  have h2 := sum_tunnel_branch_p_mul M K u M.r2 M.d0 M.d0 (Or.inr ⟨rfl, rfl, rfl⟩)
  unfold TunnelModelPQ.hatMu
  simp only [Int.cast_mul, Int.cast_natCast] at hpart h1 h2 ⊢
  rw [hpart, h1, h2]
  have hcast1 :
      -(((M.d0 + 1 : ℕ) : ℝ) * (u : ℝ)) / (M.q : ℝ) ^ (K + 1) =
        -((M.d0 + 1 : ℕ) : ℝ) * (u : ℝ) / (M.q : ℝ) ^ (K + 1) := by ring
  have hcast2 :
      -(((M.d0 : ℕ) : ℝ) * (u : ℝ)) / (M.q : ℝ) ^ (K + 1) =
        -(M.d0 : ℝ) * (u : ℝ) / (M.q : ℝ) ^ (K + 1) := by ring
  rw [hcast1, hcast2, pow_succ]
  have h2K : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero K (by norm_num)
  field_simp [h2K]

/-- Norm recursion under `p`-multiplication:
`‖μ̂_{K+1}(p u)‖ = |cos (π u / q^{K+1})| · ‖μ̂_K(u)‖`. -/
public theorem norm_hatMuPQ_p_mul (M : TunnelModelPQ) (K : ℕ) (u : ℤ) :
    ‖M.hatMu (K + 1) (M.p * u)‖ =
      |Real.cos (Real.pi * (u : ℝ) / (M.q : ℝ) ^ (K + 1))| * ‖M.hatMu K u‖ := by
  rw [hatMuPQ_p_mul, norm_mul, norm_div]
  have harg1 :
      -((M.d0 + 1 : ℕ) : ℝ) * (u : ℝ) / (M.q : ℝ) ^ (K + 1) =
        -((M.d0 + 1 : ℕ) : ℝ) * ((u : ℝ) / (M.q : ℝ) ^ (K + 1)) := by ring
  have harg2 :
      -(M.d0 : ℝ) * (u : ℝ) / (M.q : ℝ) ^ (K + 1) =
        -(M.d0 : ℝ) * ((u : ℝ) / (M.q : ℝ) ^ (K + 1)) := by ring
  have hcos : Real.pi * ((u : ℝ) / (M.q : ℝ) ^ (K + 1)) =
      Real.pi * (u : ℝ) / (M.q : ℝ) ^ (K + 1) := by ring
  rw [harg1, harg2, eChar_consec_pair_norm, hcos]
  norm_num

/-- Frequency congruence invariance `u ≡ u' (mod q^K) → μ̂_K(u) = μ̂_K(u')`. -/
public theorem hatMuPQ_mod_q_pow (M : TunnelModelPQ) {K : ℕ} {u u' : ℤ}
    (h : (M.q : ℤ) ^ K ∣ (u - u')) :
    M.hatMu K u = M.hatMu K u' := by
  obtain ⟨m, hm⟩ := h
  unfold TunnelModelPQ.hatMu
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  have harg : (u * (g : ℤ) : ℝ) / (M.q : ℝ) ^ K =
      (u' * (g : ℤ) : ℝ) / (M.q : ℝ) ^ K + ((m * (g : ℤ) : ℤ) : ℝ) := by
    have hq0_nat : M.q ≠ 0 := by have := M.hq; grind
    have hqK : (M.q : ℝ) ^ K ≠ 0 := pow_ne_zero K (by exact_mod_cast hq0_nat)
    have hu : (u : ℝ) = (u' : ℝ) + (M.q : ℝ) ^ K * (m : ℝ) := by
      have : (u : ℝ) - (u' : ℝ) = (M.q : ℝ) ^ K * (m : ℝ) := by exact_mod_cast hm
      linarith
    push_cast
    rw [hu]
    field_simp [hqK]
  rw [harg, eChar_add_int]

private lemma norm_hatMuPQ_zero (M : TunnelModelPQ) (u : ℤ) : ‖M.hatMu 0 u‖ = 1 := by
  have hset : M.survivorsSet 0 = {0} := by
    ext g
    simp [TunnelModelPQ.survivorsSet, TunnelModelPQ.survives, TunnelModelPQ.iter]
  unfold TunnelModelPQ.hatMu
  rw [hset, pow_zero, inv_one, one_mul, Finset.sum_singleton, pow_zero, div_one]
  simp only [Nat.cast_zero, Int.cast_zero, mul_zero]
  exact norm_eChar 0

private lemma norm_hatMuPQ_cosine_product_aux (M : TunnelModelPQ) (k : ℕ) (w : ℤ)
    (hdvd : (M.q : ℤ) ^ k ∣ (M.p * w - 1)) (m : ℕ) (hm : m ≤ k) (v : ℤ) :
    ‖M.hatMu m v‖ =
      ∏ j ∈ Finset.range m,
        |Real.cos (Real.pi * ((w ^ (m - j) * v : ℤ) : ℝ) / (M.q : ℝ) ^ (j + 1))| := by
  induction m generalizing v with
  | zero => simp [norm_hatMuPQ_zero]
  | succ m ih =>
    have hcon : ((M.q : ℤ) ^ (m + 1)) ∣ (v - (M.p : ℤ) * (w * v)) := by
      have hsub : v - (M.p : ℤ) * (w * v) = -((M.p * w - 1) * v) := by ring
      rw [hsub]
      refine dvd_neg.mpr (dvd_mul_of_dvd_left ?_ v)
      exact dvd_trans (pow_dvd_pow (M.q : ℤ) hm) hdvd
    rw [hatMuPQ_mod_q_pow M hcon, norm_hatMuPQ_p_mul, ih (by grind) (w * v),
      Finset.prod_range_succ, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hj_lt : j < m := Finset.mem_range.mp hj
      have hexp : m + 1 - j = (m - j) + 1 := by grind
      congr 2
      have hz : w ^ (m - j) * (w * v) = w ^ (m + 1 - j) * v := by
        rw [hexp, pow_succ']; ring
      rw [hz]
    · simp

/-- **Closed-form `(p, q)` cosine product**: for `w = (p⁻¹ mod q^K)`,
`‖μ̂_K(u)‖ = ∏_{m=0}^{K-1} |cos (π · w^{K - m} u / q^{m + 1})|`. -/
public theorem norm_hatMuPQ_cosine_product (M : TunnelModelPQ) (K : ℕ) (u : ℤ) :
    ‖M.hatMu K u‖ =
      ∏ m ∈ Finset.range K,
        |Real.cos (Real.pi * ((((ZMod.val ((M.p : ZMod (M.q ^ K))⁻¹)) : ℤ) ^ (K - m) * u : ℤ) :
          ℝ) / (M.q : ℝ) ^ (m + 1))| :=
  norm_hatMuPQ_cosine_product_aux M K _ (zmod_p_inv_dvd M K) K le_rfl u

private lemma circleDist_ge_of_not_dvd {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) {v : ℤ}
    (hv : ¬ ((q : ℤ) ∣ v)) :
    (1 : ℝ) / (q : ℝ) ^ m ≤ circleDist ((v : ℝ) / (q : ℝ) ^ m) := by
  set n := round ((v : ℝ) / (q : ℝ) ^ m)
  have hqpos : (0 : ℝ) < (q : ℝ) ^ m := pow_pos (by exact_mod_cast (by grind : 0 < q)) m
  have hne : v - n * (q : ℤ) ^ m ≠ 0 := by
    intro h0
    have hdvd_m : (q : ℤ) ^ m ∣ v := ⟨n, by linarith⟩
    have hq_dvd_qm : (q : ℤ) ∣ (q : ℤ) ^ m := dvd_pow_self _ (by grind)
    exact hv (dvd_trans hq_dvd_qm hdvd_m)
  have habs1 : (1 : ℝ) ≤ |((v - n * (q : ℤ) ^ m : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |v - n * (q : ℤ) ^ m| := Int.one_le_abs hne
    exact_mod_cast this
  unfold circleDist
  have hrew : (v : ℝ) / (q : ℝ) ^ m - (n : ℝ) =
      ((v - n * (q : ℤ) ^ m : ℤ) : ℝ) / (q : ℝ) ^ m := by
    push_cast
    field_simp [hqpos.ne']
  rw [hrew, abs_div, abs_of_pos hqpos]
  exact div_le_div_of_nonneg_right habs1 hqpos.le

private lemma circleDist_step_exact_pq {p q : ℕ} (hq : 2 ≤ q) (hpq : q < p) {β β' : ℝ}
    {rInt : ℤ} (hrel : (p : ℝ) * β - (q : ℝ) * β' = rInt)
    (h1 : circleDist β < 1 / (2 * ((p : ℝ) + q)))
    (h2 : circleDist β' < 1 / (2 * ((p : ℝ) + q))) :
    circleDist β' = ((p : ℝ) / q) * circleDist β := by
  set r := β - (round β : ℝ)
  set r' := β' - (round β' : ℝ)
  have hden : (0 : ℝ) < (p : ℝ) + q := by
    have : 0 < p + q := by grind
    exact_mod_cast this
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (by grind : 0 < p)
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by grind : 0 < q)
  have hr : |r| < 1 / (2 * ((p : ℝ) + q)) := h1
  have hr' : |r'| < 1 / (2 * ((p : ℝ) + q)) := h2
  have hsmall : |(p : ℝ) * r - (q : ℝ) * r'| < 1 := by
    calc
      |(p : ℝ) * r - (q : ℝ) * r'| ≤ |(p : ℝ) * r| + |(q : ℝ) * r'| := abs_sub _ _
      _ = (p : ℝ) * |r| + (q : ℝ) * |r'| := by
          rw [abs_mul, abs_mul, abs_of_pos hp_pos, abs_of_pos hq_pos]
      _ < (p : ℝ) * (1 / (2 * ((p : ℝ) + q))) + (q : ℝ) * (1 / (2 * ((p : ℝ) + q))) := by
          gcongr
      _ = 1 / 2 := by
          field_simp [hden.ne']
      _ < 1 := by norm_num
  have hint : (p : ℝ) * r - (q : ℝ) * r' = ((rInt - p * round β + q * round β' : ℤ) : ℝ) := by
    dsimp [r, r']
    push_cast
    linarith
  have hzero : rInt - p * round β + q * round β' = 0 := by
    have hlt1 : ((|rInt - p * round β + q * round β'| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs, ← hint]
      exact hsmall
    have hltZ : |rInt - p * round β + q * round β'| < 1 := by exact_mod_cast hlt1
    grind
  have hr_eq : (p : ℝ) * r - (q : ℝ) * r' = 0 := by
    rw [hint, hzero, Int.cast_zero]
  have hr'_eq : r' = ((p : ℝ) / q) * r := by
    field_simp [hq_pos.ne']
    linarith
  change |r'| = ((p : ℝ) / q) * |r|
  rw [hr'_eq, abs_mul, abs_of_nonneg (div_nonneg (by positivity) (by positivity))]

private lemma abs_cos_pi_le_cos_pi_div {x δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hx : δ ≤ circleDist x) :
    |Real.cos (Real.pi * x)| ≤ Real.cos (Real.pi * δ) := by
  rw [abs_cos_pi_eq_cos_pi_circleDist]
  refine Real.strictAntiOn_cos.antitoneOn ?_ ?_ (mul_le_mul_of_nonneg_left hx Real.pi_pos.le)
  · refine ⟨mul_nonneg Real.pi_pos.le hδ0, ?_⟩
    nlinarith [Real.pi_pos]
  · refine ⟨mul_nonneg Real.pi_pos.le (circleDist_nonneg x), ?_⟩
    nlinarith [Real.pi_pos, circleDist_le_half x]

private lemma exists_tunnel_block_exp (p q : ℕ) (hq : 2 ≤ q) (hpq : q < p) :
    ∃ B : ℕ, 1 ≤ B ∧ 2 * (p + q) * q ^ (B + 1) ≤ p ^ B := by
  have hlt1 : (q : ℝ) / p < 1 := (div_lt_one (by exact_mod_cast (by grind : 0 < p))).mpr
    (by exact_mod_cast hpq)
  have hnn : 0 ≤ (q : ℝ) / p := by positivity
  have hden_pos : (0 : ℝ) < (2 * ((p : ℝ) + q) * q : ℝ) := by positivity
  obtain ⟨B, hB⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hden_pos) hlt1
  refine ⟨max B 1, le_max_right B 1, ?_⟩
  have hle : ((q : ℝ) / p) ^ (max B 1) ≤ ((q : ℝ) / p) ^ B :=
    pow_le_pow_of_le_one hnn hlt1.le (le_max_left B 1)
  have hlt' : ((q : ℝ) / p) ^ (max B 1) < (2 * ((p : ℝ) + q) * q : ℝ)⁻¹ :=
    lt_of_le_of_lt hle hB
  rw [div_pow, inv_eq_one_div, lt_div_iff₀ hden_pos, div_mul_eq_mul_div,
    div_lt_one (pow_pos (by exact_mod_cast (by grind : 0 < p)) _)] at hlt'
  have hreal : (2 * ((p : ℝ) + q) * (q : ℝ) ^ (max B 1 + 1)) < (p : ℝ) ^ (max B 1) := by
    rw [pow_succ]
    linarith
  exact_mod_cast hreal.le

private lemma tunnel_block_hit_pq {p q K B a : ℕ} (hq : 2 ≤ q) (hpq : q < p)
    (_hB1 : 1 ≤ B) (hB : 2 * (p + q) * q ^ (B + 1) ≤ p ^ B) (w u : ℤ)
    (hw_cop : Nat.Coprime w.natAbs q) (hu : ¬ ((q : ℤ) ∣ u))
    (hdvd : (q : ℤ) ^ K ∣ (p * w - 1))
    (ha1 : 1 ≤ a) (ha_top : (B + 1) * a ≤ K) :
    ∃ m ∈ Finset.Icc a ((B + 1) * a),
      (1 / (2 * ((p : ℝ) + q)) : ℝ) ≤
        circleDist (((w ^ (K + 1 - m) * u : ℤ) : ℝ) / (q : ℝ) ^ m) := by
  by_contra hnone
  push Not at hnone
  let β : ℕ → ℝ := fun m => ((w ^ (K + 1 - m) * u : ℤ) : ℝ) / (q : ℝ) ^ m
  have hstep : ∀ t ≤ B * a,
      circleDist (β (a + t)) = ((p : ℝ) / q) ^ t * circleDist (β a) := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have ht_le : t ≤ B * a := by grind
      have hle_top1 : a + t ≤ (B + 1) * a := by
        have : t + 1 ≤ B * a := by grind
        nlinarith
      have hle_top2 : a + t + 1 ≤ (B + 1) * a := by nlinarith
      have hm1 : a + t ∈ Finset.Icc a ((B + 1) * a) := Finset.mem_Icc.mpr ⟨by grind, hle_top1⟩
      have hm2 : a + t + 1 ∈ Finset.Icc a ((B + 1) * a) :=
        Finset.mem_Icc.mpr ⟨by grind, hle_top2⟩
      have hK_pow : K + 1 - (a + t + 1) + (a + t) ≤ K := by grind
      obtain ⟨rZ, hrZ⟩ := hdvd
      have hpwi : (p : ℤ) * w - 1 = (q : ℤ) ^ (a + t) * ((q : ℤ) ^ (K - (a + t)) * rZ) := by
        rw [hrZ, ← mul_assoc, ← pow_add]
        have heq : a + t + (K - (a + t)) = K := by grind
        rw [heq]
      set q0 := (q : ℤ) ^ (K - (a + t)) * rZ
      have hrel : (p : ℝ) * β (a + t) - (q : ℝ) * β (a + t + 1) =
          ((q0 * (w ^ (K - (a + t)) * u) : ℤ) : ℝ) := by
        dsimp [β]
        have hexp : K + 1 - (a + t) = (K - (a + t)) + 1 := by grind
        have hexp' : K + 1 - (a + t + 1) = K - (a + t) := by grind
        have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ (a + t) :=
          pow_pos (by exact_mod_cast (by grind : 0 < q)) _
        have hq0_pos : (q : ℝ) ≠ 0 := by exact_mod_cast (by grind : q ≠ 0)
        have hpwR : (p : ℝ) * (w : ℝ) - 1 = (q : ℝ) ^ (a + t) * (q0 : ℝ) := by
          exact_mod_cast hpwi
        have hcancel : (q : ℝ) * (((w ^ (K - (a + t)) * u : ℤ) : ℝ) / ((q : ℝ) ^ (a + t) * q)) =
            ((w ^ (K - (a + t)) * u : ℤ) : ℝ) / (q : ℝ) ^ (a + t) := by
          field_simp [hqpow_pos.ne', hq0_pos]
        rw [hexp, hexp', pow_succ (w : ℤ), pow_succ (q : ℝ) (a + t), hcancel]
        push_cast
        field_simp [hqpow_pos.ne']
        linear_combination (w : ℝ) ^ (K - (a + t)) * (u : ℝ) * hpwR
      have hexact :=
        circleDist_step_exact_pq hq hpq hrel (hnone (a + t) hm1) (hnone (a + t + 1) hm2)
      rw [← add_assoc, hexact, ih ht_le, pow_succ']
      ring
  have htop := hstep (B * a) le_rfl
  rw [show a + B * a = (B + 1) * a from by ring] at htop
  have hnot_dvd : ¬ ((q : ℤ) ∣ (w ^ (K + 1 - a) * u)) := by
    intro hd
    have hnat : q ∣ w.natAbs ^ (K + 1 - a) * u.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hd
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    have hq_dvd_u : q ∣ u.natAbs := (hw_cop.pow_left (K + 1 - a)).symm.dvd_of_dvd_mul_left hnat
    exact hu (Int.ofNat_dvd_left.mpr hq_dvd_u)
  have hge := circleDist_ge_of_not_dvd hq ha1 hnot_dvd
  have hlt_top : circleDist (β ((B + 1) * a)) < 1 / (2 * ((p : ℝ) + q)) :=
    hnone ((B + 1) * a) (Finset.mem_Icc.mpr ⟨by nlinarith, le_rfl⟩)
  have hB_real : ((2 * (p + q) : ℝ) * (q : ℝ) ^ (B + 1) : ℝ) ≤ (p : ℝ) ^ B := by
    exact_mod_cast hB
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by grind : 0 < q)
  have hp_ge_2q : (2 * ((p : ℝ) + q) : ℝ) ≤ ((p : ℝ) ^ B / (q : ℝ) ^ (B + 1)) := by
    rw [le_div_iff₀ (pow_pos hqpos _)]
    exact hB_real
  have hgrow_one : (1 : ℝ) ≤ ((p : ℝ) ^ B / (q : ℝ) ^ (B + 1)) := by
    have : (4 : ℝ) ≤ 2 * ((p : ℝ) + q) := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have : (q : ℝ) < p := by exact_mod_cast hpq
      linarith
    linarith
  have ha_ne0 : a ≠ 0 := by grind
  have hpow_one : ((2 * ((p : ℝ) + q) : ℝ) ≤ ((p : ℝ) ^ B / (q : ℝ) ^ (B + 1)) ^ a) :=
    le_trans hp_ge_2q (le_self_pow₀ hgrow_one ha_ne0)
  have hcoeff : ((p : ℝ) ^ B / (q : ℝ) ^ (B + 1)) ^ a =
      ((p : ℝ) / q) ^ (B * a) * ((1 : ℝ) / (q : ℝ) ^ a) := by
    have hq_ne : (q : ℝ) ≠ 0 := hqpos.ne'
    calc
      ((p : ℝ) ^ B / (q : ℝ) ^ (B + 1)) ^ a
          = (p : ℝ) ^ (B * a) / (q : ℝ) ^ ((B + 1) * a) := by
            rw [div_pow, ← pow_mul, ← pow_mul]
      _ = ((p : ℝ) / q) ^ (B * a) * ((1 : ℝ) / (q : ℝ) ^ a) := by
            rw [show (B + 1) * a = B * a + a from by ring, pow_add, div_pow]
            field_simp [hq_ne]
  have hlower : (2 * ((p : ℝ) + q) : ℝ) ≤ ((p : ℝ) / q) ^ (B * a) * circleDist (β a) := by
    calc
      (2 * ((p : ℝ) + q) : ℝ) ≤ ((p : ℝ) ^ B / (q : ℝ) ^ (B + 1)) ^ a := hpow_one
      _ = ((p : ℝ) / q) ^ (B * a) * ((1 : ℝ) / (q : ℝ) ^ a) := hcoeff
      _ ≤ ((p : ℝ) / q) ^ (B * a) * circleDist (β a) := by gcongr
  have h_inv_gt : (1 / (2 * ((p : ℝ) + q)) : ℝ) < 2 * ((p : ℝ) + q) := by
    have hgt1 : (1 : ℝ) < 2 * ((p : ℝ) + q) := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have : (q : ℝ) < p := by exact_mod_cast hpq
      linarith
    have hinv_lt : (1 / (2 * ((p : ℝ) + q)) : ℝ) < 1 :=
      div_lt_one (by linarith) |>.mpr hgt1
    linarith
  linarith

private lemma abs_cos_pi_le_one_pq (x : ℝ) : |Real.cos (Real.pi * x)| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- Disjoint-block `(p, q)` cosine product bound. -/
public theorem norm_hatMuPQ_le_cos_pow (M : TunnelModelPQ) {B : ℕ} (hB1 : 1 ≤ B)
    (hB : 2 * (M.p + M.q) * M.q ^ (B + 1) ≤ M.p ^ B) {K R : ℕ} (hR : (B + 2) ^ R ≤ K)
    {u : ℤ} (hu : ¬ ((M.q : ℤ) ∣ u)) :
    ‖M.hatMu K u‖ ≤ (Real.cos (Real.pi / (2 * (M.p + M.q)))) ^ R := by
  cases R with
  | zero =>
    simp only [pow_zero]
    rw [norm_hatMuPQ_cosine_product]
    refine prod_le_one_nat _ _ (fun _ _ => abs_nonneg _) fun _ _ => ?_
    rw [mul_div_assoc]
    exact abs_cos_pi_le_one_pq _
  | succ R' =>
    have hKpos : 1 ≤ K := by
      have : 1 ≤ (B + 2) ^ (R' + 1) := Nat.one_le_pow _ _ (by grind)
      grind
    let w : ℤ := (ZMod.val ((M.p : ZMod (M.q ^ K))⁻¹) : ℤ)
    have hdvd : (M.q : ℤ) ^ K ∣ ((M.p : ℤ) * w - 1) := zmod_p_inv_dvd M K
    have hw_cop : Nat.Coprime w.natAbs M.q := by
      obtain ⟨rZ, hrZ⟩ := hdvd
      have hq_pos : 0 < M.q := by have := M.hq; grind
      have hdiv_one : (M.p : ℤ) * w - (M.q : ℤ) * ((M.q : ℤ) ^ (K - 1) * rZ) = 1 := by
        have hk : (M.q : ℤ) ^ K = M.q * (M.q : ℤ) ^ (K - 1) := by
          obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by grind⟩
          rw [pow_succ']
          simp
        calc
          (M.p : ℤ) * w - (M.q : ℤ) * ((M.q : ℤ) ^ (K - 1) * rZ)
              = ((M.p : ℤ) * w - 1) - (M.q : ℤ) ^ K * rZ + 1 := by rw [hk]; ring
          _ = 1 := by rw [hrZ]; ring
      refine Nat.coprime_of_dvd' fun k hk hkw hkq => ?_
      have hkwZ : (k : ℤ) ∣ w := Int.ofNat_dvd_left.mpr hkw
      have hkqZ : (k : ℤ) ∣ M.q := Int.ofNat_dvd.mpr hkq
      have hk1 : (k : ℤ) ∣ 1 := by
        rw [← hdiv_one]
        exact dvd_sub (dvd_mul_of_dvd_right hkwZ _) (dvd_mul_of_dvd_left hkqZ _)
      exact Int.ofNat_dvd.mp hk1
    have hhit : ∀ j : ℕ, ∃ m : ℕ, j < R' + 1 →
        m ∈ Finset.Icc ((B + 2) ^ j) ((B + 1) * (B + 2) ^ j) ∧
          (1 / (2 * ((M.p : ℝ) + M.q)) : ℝ) ≤
            circleDist (((w ^ (K + 1 - m) * u : ℤ) : ℝ) / (M.q : ℝ) ^ m) := by
      intro j
      by_cases hj : j < R' + 1
      · have ha1 : 1 ≤ (B + 2) ^ j := Nat.one_le_pow _ _ (by grind)
        have ha_top : (B + 1) * (B + 2) ^ j ≤ K := by
          have hpow : (B + 2) ^ (j + 1) ≤ (B + 2) ^ (R' + 1) :=
            Nat.pow_le_pow_right (by grind) (by grind)
          rw [pow_succ'] at hpow
          nlinarith
        obtain ⟨m, hm1, hm2⟩ :=
          tunnel_block_hit_pq M.hq M.hpq hB1 hB w u hw_cop hu hdvd ha1 ha_top
        exact ⟨m, fun _ => ⟨hm1, hm2⟩⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose m_of hm_spec using hhit
    have hm_mem : ∀ j < R' + 1, m_of j ∈ Finset.Icc ((B + 2) ^ j) ((B + 1) * (B + 2) ^ j) :=
      fun j hj => (hm_spec j hj).1
    have hm_dist : ∀ j < R' + 1,
        (1 / (2 * ((M.p : ℝ) + M.q)) : ℝ) ≤
          circleDist (((w ^ (K + 1 - m_of j) * u : ℤ) : ℝ) / (M.q : ℝ) ^ m_of j) :=
      fun j hj => (hm_spec j hj).2
    let picks : Finset ℕ := (Finset.range (R' + 1)).image (fun j => m_of j - 1)
    have hinj : ∀ j₁ ∈ Finset.range (R' + 1), ∀ j₂ ∈ Finset.range (R' + 1),
        m_of j₁ - 1 = m_of j₂ - 1 → j₁ = j₂ := by
      intro j₁ hj1 j₂ hj2 heq
      have h1 := Finset.mem_Icc.mp (hm_mem j₁ (Finset.mem_range.mp hj1))
      have h2 := Finset.mem_Icc.mp (hm_mem j₂ (Finset.mem_range.mp hj2))
      have ha1 : 1 ≤ (B + 2) ^ j₁ := Nat.one_le_pow _ _ (by grind)
      have ha2 : 1 ≤ (B + 2) ^ j₂ := Nat.one_le_pow _ _ (by grind)
      have hm_eq : m_of j₁ = m_of j₂ := by grind
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : (B + 2) ^ (j₁ + 1) ≤ (B + 2) ^ j₂ :=
          Nat.pow_le_pow_right (by grind) (by grind)
        rw [pow_succ'] at hpow
        nlinarith
      · have hpow : (B + 2) ^ (j₂ + 1) ≤ (B + 2) ^ j₁ :=
          Nat.pow_le_pow_right (by grind) (by grind)
        rw [pow_succ'] at hpow
        nlinarith
    have hcard : picks.card = R' + 1 := by
      rw [Finset.card_image_of_injOn (fun j₁ hj1 j₂ hj2 h => hinj j₁ hj1 j₂ hj2 h),
        Finset.card_range]
    have hsub : picks ⊆ Finset.range K := by
      intro idx hidx
      rw [Finset.mem_image] at hidx
      obtain ⟨j, hj, rfl⟩ := hidx
      have hmem := Finset.mem_Icc.mp (hm_mem j (Finset.mem_range.mp hj))
      have hj' : j < R' + 1 := Finset.mem_range.mp hj
      have hpow : (B + 2) ^ (j + 1) ≤ (B + 2) ^ (R' + 1) :=
        Nat.pow_le_pow_right (by grind) (by grind)
      have hha1 : 1 ≤ (B + 2) ^ j := Nat.one_le_pow _ _ (by grind)
      have hm_le : m_of j ≤ (B + 1) * (B + 2) ^ j := hmem.2
      have hm_ge : (B + 2) ^ j ≤ m_of j := hmem.1
      have hmul_lt : (B + 1) * (B + 2) ^ j < (B + 2) ^ (j + 1) := by
        rw [pow_succ']
        nlinarith [hha1]
      have hlt1 : m_of j - 1 < (B + 2) ^ (j + 1) := by grind
      exact Finset.mem_range.mpr (lt_of_lt_of_le hlt1 (le_trans hpow hR))
    let f : ℕ → ℝ := fun idx =>
      |Real.cos (Real.pi * ((w ^ (K - idx) * u : ℤ) : ℝ) / (M.q : ℝ) ^ (idx + 1))|
    have hprod_eq : ‖M.hatMu K u‖ = ∏ idx ∈ Finset.range K, f idx :=
      norm_hatMuPQ_cosine_product M K u
    have hsplit : ∏ idx ∈ Finset.range K, f idx =
        (∏ idx ∈ picks, f idx) * (∏ idx ∈ Finset.range K \ picks, f idx) :=
      (Finset.prod_sdiff hsub).symm.trans (mul_comm _ _)
    have hrest : ∏ idx ∈ Finset.range K \ picks, f idx ≤ 1 := by
      refine prod_le_one_nat _ _ (fun _ _ => abs_nonneg _) fun _ _ => ?_
      dsimp [f]
      rw [mul_div_assoc]
      exact abs_cos_pi_le_one_pq _
    have hpicks_nn : 0 ≤ ∏ idx ∈ picks, f idx :=
      Finset.prod_nonneg (fun _ _ => abs_nonneg _)
    have hδ0 : (0 : ℝ) ≤ 1 / (2 * ((M.p : ℝ) + M.q)) := by positivity
    have hδ1 : (1 / (2 * ((M.p : ℝ) + M.q)) : ℝ) ≤ 1 / 2 := by
      have hpq_ge2 : (2 : ℝ) ≤ 2 * ((M.p : ℝ) + M.q) := by
        have : (2 : ℝ) ≤ M.q := by exact_mod_cast M.hq
        have : (M.q : ℝ) < M.p := by exact_mod_cast M.hpq
        linarith
      rw [one_div_le_one_div (by linarith) (by norm_num)]
      exact hpq_ge2
    have hδ_eq : Real.pi * (1 / (2 * ((M.p : ℝ) + M.q))) =
        Real.pi / (2 * (M.p + M.q)) := by ring
    have hpicks_le : ∏ idx ∈ picks, f idx ≤
        (Real.cos (Real.pi / (2 * (M.p + M.q)))) ^ picks.card := by
      calc
        ∏ idx ∈ picks, f idx ≤
            ∏ _idx ∈ picks, Real.cos (Real.pi / (2 * (M.p + M.q))) := by
          refine prod_le_prod_nat _ _ _ (fun _ _ => abs_nonneg _) fun idx hidx => ?_
          rw [Finset.mem_image] at hidx
          obtain ⟨j, hj, rfl⟩ := hidx
          have hj_lt : j < R' + 1 := Finset.mem_range.mp hj
          have hmem := Finset.mem_Icc.mp (hm_mem j hj_lt)
          have ha1 : 1 ≤ (B + 2) ^ j := Nat.one_le_pow _ _ (by grind)
          have hm1 : 1 ≤ m_of j := by grind
          have hidx_eq1 : K - (m_of j - 1) = K + 1 - m_of j := by grind
          have hidx_eq2 : (m_of j - 1) + 1 = m_of j := by grind
          dsimp [f]
          rw [hidx_eq1, hidx_eq2]
          have harg :
              Real.pi * ((w ^ (K + 1 - m_of j) * u : ℤ) : ℝ) / (M.q : ℝ) ^ m_of j =
                Real.pi * (((w ^ (K + 1 - m_of j) * u : ℤ) : ℝ) / (M.q : ℝ) ^ m_of j) := by
            ring
          rw [harg, ← hδ_eq]
          exact abs_cos_pi_le_cos_pi_div hδ0 hδ1 (hm_dist j hj_lt)
        _ = (Real.cos (Real.pi / (2 * (M.p + M.q)))) ^ picks.card := Finset.prod_const _
    rw [hprod_eq, hsplit, hcard] at *
    calc
      (∏ idx ∈ picks, f idx) * (∏ idx ∈ Finset.range K \ picks, f idx)
          ≤ (∏ idx ∈ picks, f idx) * 1 := mul_le_mul_of_nonneg_left hrest hpicks_nn
      _ = ∏ idx ∈ picks, f idx := mul_one _
      _ ≤ (Real.cos (Real.pi / (2 * (M.p + M.q)))) ^ (R' + 1) := by
          simpa [hcard] using hpicks_le

/-- **General `(p, q)` quantitative Weyl Fourier decay**: for any `TunnelModelPQ` `M`, there exist
`C > 0` and `c > 0` such that `‖M.hatMu K u‖ ≤ C · K^{-c}` for all `K ≥ 1` and `q ∤ u`. -/
public theorem global_coprime_freq_decay_pq (M : TunnelModelPQ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), ¬ ((M.q : ℤ) ∣ u) →
        ‖M.hatMu K u‖ ≤ C * (K : ℝ) ^ (-c) := by
  obtain ⟨B, hB1, hB⟩ := exists_tunnel_block_exp M.p M.q M.hq M.hpq
  let γ : ℝ := Real.cos (Real.pi / (2 * (M.p + M.q)))
  have hden_ge4 : (4 : ℝ) ≤ 2 * ((M.p : ℝ) + M.q) := by
    have hq2 : (2 : ℝ) ≤ M.q := by exact_mod_cast M.hq
    have hpq : (M.q : ℝ) < M.p := by exact_mod_cast M.hpq
    linarith
  have hpi_gt0 : 0 < Real.pi / (2 * (M.p + M.q)) := by positivity
  have hpi_lt_pi2 : Real.pi / (2 * (M.p + M.q)) < Real.pi / 2 := by
    have hden_gt2 : (2 : ℝ) < 2 * ((M.p : ℝ) + M.q) := by linarith
    exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) hden_gt2
  have hγ_pos : 0 < γ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hpi_lt_pi2⟩
  have hγ_lt1 : γ < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩
      ⟨hpi_gt0.le, le_trans hpi_lt_pi2.le (by linarith [Real.pi_pos])⟩ hpi_gt0
  have hlogγ_neg : Real.log γ < 0 := Real.log_neg hγ_pos hγ_lt1
  have hb_gt1 : (1 : ℝ) < (B + 2 : ℕ) := by exact_mod_cast (by grind : 1 < B + 2)
  have hlogb_pos : 0 < Real.log ((B + 2 : ℕ) : ℝ) := Real.log_pos hb_gt1
  let c : ℝ := -Real.log γ / Real.log ((B + 2 : ℕ) : ℝ)
  have hc_pos : 0 < c := div_pos (neg_pos.mpr hlogγ_neg) hlogb_pos
  let C : ℝ := γ⁻¹
  have hC_pos : 0 < C := inv_pos.mpr hγ_pos
  refine ⟨C, c, hC_pos, hc_pos, fun K hK u hu => ?_⟩
  let R := Nat.log (B + 2) K
  have hR : (B + 2) ^ R ≤ K := Nat.pow_log_le_self (B + 2) (by grind)
  have hbound : ‖M.hatMu K u‖ ≤ γ ^ R := norm_hatMuPQ_le_cos_pow M hB1 hB hR hu
  have hKlt : K < (B + 2) ^ (R + 1) := Nat.lt_pow_succ_log_self (by grind) K
  have hKltR : (K : ℝ) < ((B + 2 : ℕ) : ℝ) ^ ((R + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hKlt
  have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hrpow_lt : (((B + 2 : ℕ) : ℝ) ^ ((R + 1 : ℕ) : ℝ)) ^ (-c) < (K : ℝ) ^ (-c) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hKposR.le]
    refine inv_strictAnti₀ (Real.rpow_pos_of_pos hKposR c) ?_
    exact Real.rpow_lt_rpow hKposR.le hKltR hc_pos
  have hb_neg_c : ((B + 2 : ℕ) : ℝ) ^ (-c) = γ := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have hmul : Real.log ((B + 2 : ℕ) : ℝ) * (-c) = Real.log γ := by
      dsimp [c]
      field_simp [hlogb_pos.ne']
    rw [hmul, Real.exp_log hγ_pos]
  have hpow_eq : (((B + 2 : ℕ) : ℝ) ^ ((R + 1 : ℕ) : ℝ)) ^ (-c) = γ ^ (R + 1) := by
    rw [← Real.rpow_mul (by positivity), mul_comm ((R + 1 : ℕ) : ℝ) (-c),
      Real.rpow_mul (by positivity), hb_neg_c, Real.rpow_natCast]
  rw [hpow_eq] at hrpow_lt
  have hC_mul : γ ^ R = C * γ ^ (R + 1) := by
    dsimp [C]
    rw [pow_succ']
    field_simp [hγ_pos.ne']
  calc
    ‖M.hatMu K u‖ ≤ γ ^ R := hbound
    _ = C * γ ^ (R + 1) := hC_mul
    _ ≤ C * (K : ℝ) ^ (-c) := by gcongr

/-- Combined `q`-contraction and `q ∤ u` Weyl decay: for `v < K` and `q ∤ u`,
`‖M.hatMu K (q^v u)‖ ≤ C · (K - v)^{-c}`. -/
public theorem global_freq_decay_of_q_pow_pq (M : TunnelModelPQ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (K v : ℕ), v < K → ∀ (u : ℤ), ¬ ((M.q : ℤ) ∣ u) →
        ‖M.hatMu K ((M.q : ℤ) ^ v * u)‖ ≤ C * ((K - v : ℕ) : ℝ) ^ (-c) := by
  obtain ⟨C, c, hC, hc, hmain⟩ := global_coprime_freq_decay_pq M
  refine ⟨C, c, hC, hc, fun K v hv u hu => ?_⟩
  rw [norm_hatMuPQ_q_pow_mul M hv.le u]
  exact hmain (K - v) (by grind) u hu

/-- Quantitative Weyl Fourier decay instantiated for base `3/2`. -/
public theorem weyl_decay_3_2 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), ¬ ((2 : ℤ) ∣ u) →
      ‖(TunnelModelPQ.mkConsecutive 3 2 1 (by decide) (by decide) (by decide)).hatMu K u‖ ≤
        C * (K : ℝ) ^ (-c) :=
  global_coprime_freq_decay_pq
    (TunnelModelPQ.mkConsecutive 3 2 1 (by decide) (by decide) (by decide))

/-- Quantitative Weyl Fourier decay instantiated for base `4/3`. -/
public theorem weyl_decay_4_3 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), ¬ ((3 : ℤ) ∣ u) →
      ‖(TunnelModelPQ.mkConsecutive 4 3 1 (by decide) (by decide) (by decide)).hatMu K u‖ ≤
        C * (K : ℝ) ^ (-c) :=
  global_coprime_freq_decay_pq
    (TunnelModelPQ.mkConsecutive 4 3 1 (by decide) (by decide) (by decide))

/-- Quantitative Weyl Fourier decay instantiated for base `5/4`. -/
public theorem weyl_decay_5_4 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), ¬ ((4 : ℤ) ∣ u) →
      ‖(TunnelModelPQ.mkConsecutive 5 4 1 (by decide) (by decide) (by decide)).hatMu K u‖ ≤
        C * (K : ℝ) ^ (-c) :=
  global_coprime_freq_decay_pq
    (TunnelModelPQ.mkConsecutive 5 4 1 (by decide) (by decide) (by decide))

/-- Quantitative Weyl Fourier decay instantiated for base `5/3`. -/
public theorem weyl_decay_5_3 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), ¬ ((3 : ℤ) ∣ u) →
      ‖(TunnelModelPQ.mkConsecutive 5 3 1 (by decide) (by decide) (by decide)).hatMu K u‖ ≤
        C * (K : ℝ) ^ (-c) :=
  global_coprime_freq_decay_pq
    (TunnelModelPQ.mkConsecutive 5 3 1 (by decide) (by decide) (by decide))

/-- Quantitative Weyl Fourier decay instantiated for base `7/4`. -/
public theorem weyl_decay_7_4 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), ¬ ((4 : ℤ) ∣ u) →
      ‖(TunnelModelPQ.mkConsecutive 7 4 1 (by decide) (by decide) (by decide)).hatMu K u‖ ≤
        C * (K : ℝ) ^ (-c) :=
  global_coprime_freq_decay_pq
    (TunnelModelPQ.mkConsecutive 7 4 1 (by decide) (by decide) (by decide))

/-- Quantitative Weyl Fourier decay instantiated for base `8/3`. -/
public theorem weyl_decay_8_3 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), ¬ ((3 : ℤ) ∣ u) →
      ‖(TunnelModelPQ.mkConsecutive 8 3 1 (by decide) (by decide) (by decide)).hatMu K u‖ ≤
        C * (K : ℝ) ^ (-c) :=
  global_coprime_freq_decay_pq
    (TunnelModelPQ.mkConsecutive 8 3 1 (by decide) (by decide) (by decide))


/-! ### 3. Karp dual-potential cycle-mean bound and `44`-vertex container -/

/-- **Karp dual-potential cycle bound**: along any valid cycle `p` (`pathEnd u p = u`),
the cycle weight product is bounded unconditionally by `λ^{|p|}` (cancelling potential `φ u`). -/
public theorem karp_cycle_bound {n : ℕ} (cert : DualPotentialCert n) (u : Fin n)
    (p : List (Fin n)) (hval : cert.pathValid u p)
    (hcyc : DualPotentialCert.pathEnd u p = u) :
    cert.pathWeight u p ≤ cert.lam ^ p.length := by
  have hphi : 0 < cert.phi u := cert.phi_pos u
  have hb := cert.path_bound u p hval
  rw [hcyc] at hb
  exact le_of_mul_le_mul_right hb hphi

/-- Concrete `44`-vertex uniform-step baseline container (`λ = 249/250 < 1`, mirroring
`Model94GlobalDecay.cert42`); any `44`-vertex geometric dual-potential table satisfies the same
`DualPotentialCert 44` interface and `karp_cycle_bound`. -/
@[expose] public def cert44 : DualPotentialCert 44 where
  edge := fun _ _ => true
  weight := fun _ _ => 249 / 250
  phi := fun _ => 1
  lam := 249 / 250
  phi_pos := fun _ => by norm_num
  weight_nonneg := fun _ _ => by norm_num
  lam_pos := by norm_num
  lam_lt_one := by norm_num
  dual_ineq := fun _ _ _ => by norm_num

/-- Exponential path decay instantiated at `cert44`. -/
public theorem cert44_path_decay (u : Fin 44) (p : List (Fin 44)) :
    cert44.pathWeight u p ≤ (249 / 250 : ℚ) ^ p.length := by
  have hvalid : cert44.pathValid u p := by
    induction p generalizing u with
    | nil => trivial
    | cons v rest ih => exact ⟨rfl, ih v⟩
  simpa [cert44] using cert44.path_contraction u p hvalid

/-- Cycle contraction instantiated at `cert44`. -/
public theorem cert44_cycle_bound (u : Fin 44) (p : List (Fin 44))
    (hcyc : DualPotentialCert.pathEnd u p = u) :
    cert44.pathWeight u p ≤ (249 / 250 : ℚ) ^ p.length := by
  have hvalid : cert44.pathValid u p := by
    clear hcyc
    induction p generalizing u with
    | nil => trivial
    | cons v rest ih => exact ⟨rfl, ih v⟩
  exact karp_cycle_bound cert44 u p hvalid hcyc

end Mahler32.GeneralPQDecay

end
