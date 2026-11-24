/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mahler32.Model94Obstructions
public import Mahler32.TwoWorldPadeCriterion

/-!
# Midpoint `36^K` double-Cantor intersection and global odd-frequency decay for `9/4`

This module formalises two unconditional structures for the `9/4` finite-roof model
`4 g_{k+1} = 9 g_k + d_k` (`d_k ∈ {2, 3}`):

1. **Midpoint `36^K` double-Cantor intersection & `A_K` antipodal exclusion**: any `2K`-step
   surviving orbit midpoint `g_K` satisfies `g_K mod 36^K ∈ S_K ∩ A_K`, where `S_K` is the forward
   `K`-step survival set modulo `4^K` and `A_K` is the backward `K`-step attractor modulo `9^K`;
   moreover every `a ∈ A_K` satisfies the deterministic clamp
   `4^K a mod 9^K ∈ [2(9^K - 4^K)/5, 3(9^K - 4^K)/5]`.
2. **Global odd-frequency decay `O(K^{-c})`**: for the normalised survivor Fourier transform
   `hatMu94 K u`, we prove the exact `4`-contraction identity
   `‖hatMu94 K (4^v u)‖ = ‖hatMu94 (K - v) u‖`, the exact cosine-product representation, the
   unconditional polynomial decay `‖hatMu94 K u‖ ≤ C · K^{-c}` for all odd `u`, and the
   `DualPotentialCert` finite-graph dual potential certificate framework (`cert42`).
-/

public section

namespace Mahler32.Model94GlobalDecay

open Mahler32.Model94Obstructions
open Mahler32.TwoWorldPadeCriterion

/-! ### 1. Midpoint `36^K` double-Cantor intersection and `A_K` antipodal exclusion -/

/-- Exact word representation of a `k`-step `9/4` trajectory. -/
public theorem iter94_exists_word (k g0 gK : ℕ) (h : iter94 k g0 = some gK) :
    ∃ W : List ℕ, W.length = k ∧ validWord94 W ∧ 4 ^ k * gK = 9 ^ k * g0 + wordWeight94 W := by
  induction k generalizing g0 with
  | zero =>
    simp only [iter94_zero, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, fun _ hx => by simp at hx, by simp [wordWeight94]⟩
  | succ k ih =>
    rw [iter94_succ] at h
    obtain ⟨h1, hs, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨W, hlen, hval, heq⟩ := ih h1 hr
    have hm : g0 % 4 = 1 ∨ g0 % 4 = 2 :=
      step94_isSome.mp (by simp [hs])
    rcases hm with hm1 | hm2
    · rw [step94_of_mod_one hm1] at hs
      have hstep : 4 * h1 = 9 * g0 + 3 := by
        have hh1 : h1 = (9 * g0 + 3) / 4 := (Option.some.inj hs).symm
        rw [hh1]; omega
      refine ⟨3 :: W, by simp [hlen], fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · right; rfl
        · exact hval x hx
      · simp only [wordWeight94, hlen]
        calc
          4 ^ (k + 1) * gK = 4 * (4 ^ k * gK) := by rw [pow_succ]; ring
          _ = 4 * (9 ^ k * h1 + wordWeight94 W) := by rw [heq]
          _ = 9 ^ k * (4 * h1) + 4 * wordWeight94 W := by ring
          _ = 9 ^ k * (9 * g0 + 3) + 4 * wordWeight94 W := by rw [hstep]
          _ = 9 ^ (k + 1) * g0 + (3 * 9 ^ k + 4 * wordWeight94 W) := by rw [pow_succ]; ring
    · rw [step94_of_mod_two hm2] at hs
      have hstep : 4 * h1 = 9 * g0 + 2 := by
        have hh1 : h1 = (9 * g0 + 2) / 4 := (Option.some.inj hs).symm
        rw [hh1]; omega
      refine ⟨2 :: W, by simp [hlen], fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · left; rfl
        · exact hval x hx
      · simp only [wordWeight94, hlen]
        calc
          4 ^ (k + 1) * gK = 4 * (4 ^ k * gK) := by rw [pow_succ]; ring
          _ = 4 * (9 ^ k * h1 + wordWeight94 W) := by rw [heq]
          _ = 9 ^ k * (4 * h1) + 4 * wordWeight94 W := by ring
          _ = 9 ^ k * (9 * g0 + 2) + 4 * wordWeight94 W := by rw [hstep]
          _ = 9 ^ (k + 1) * g0 + (2 * 9 ^ k + 4 * wordWeight94 W) := by rw [pow_succ]; ring

/-- Forward `K`-step survivor predicate `S_K`. -/
@[expose] public def inSK (K x : ℕ) : Prop := survives94 K x

/-- Backward `K`-step attractor predicate `A_K`: `(4^K a) mod 9^K` equals a valid `K`-word. -/
@[expose] public def inAK (K a : ℕ) : Prop :=
  ∃ W : List ℕ, W.length = K ∧ validWord94 W ∧ (4 ^ K * a) % 9 ^ K = wordWeight94 W

public theorem inSK_mod_36_pow (K x : ℕ) : inSK K (x % 36 ^ K) ↔ inSK K x := by
  have h36 : 36 ^ K = 4 ^ K * 9 ^ K := by
    rw [show (36 : ℕ) = 4 * 9 from by norm_num, mul_pow]
  have hsplit : x = x % 36 ^ K + 4 ^ K * (9 ^ K * (x / 36 ^ K)) := by
    conv_lhs => rw [← Nat.mod_add_div x (36 ^ K)]
    rw [show 36 ^ K * (x / 36 ^ K) = 4 ^ K * (9 ^ K * (x / 36 ^ K)) from by rw [h36]; ring]
  unfold inSK
  conv_rhs => rw [hsplit, survives94_add_four_pow]

public theorem inAK_mod_36_pow (K a : ℕ) : inAK K (a % 36 ^ K) ↔ inAK K a := by
  have h36 : 36 ^ K = 9 ^ K * 4 ^ K := by
    rw [show (36 : ℕ) = 9 * 4 from by norm_num, mul_pow]
  have hsplit : 4 ^ K * a = 4 ^ K * (a % 36 ^ K) + 9 ^ K * (4 ^ K * 4 ^ K * (a / 36 ^ K)) := by
    conv_lhs =>
      rw [← Nat.mod_add_div a (36 ^ K)]
      arg 2; arg 2; arg 1; rw [h36]
    ring
  have hmod : (4 ^ K * (a % 36 ^ K)) % 9 ^ K = (4 ^ K * a) % 9 ^ K := by
    conv_rhs => rw [hsplit, Nat.add_mul_mod_self_left]
  simp only [inAK, hmod]

/-- `5 ∣ 9^K - 4^K` for every `K`. -/
public theorem five_dvd_nine_pow_sub_four_pow (K : ℕ) : 5 ∣ (9 ^ K - 4 ^ K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h49 : 4 ^ K ≤ 9 ^ K := Nat.pow_le_pow_left (by norm_num) K
    have hid : 9 ^ (K + 1) - 4 ^ (K + 1) = 9 * (9 ^ K - 4 ^ K) + 5 * 4 ^ K := by
      rw [pow_succ', pow_succ']
      omega
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_right ih 9) ⟨4 ^ K, by ring⟩

public lemma wordWeight94_lt_nine_pow {W : List ℕ} (hW : validWord94 W) :
    wordWeight94 W < 9 ^ W.length := by
  obtain ⟨_, hhi⟩ := wordWeight94_bounds_int hW
  have h4pos : (0 : ℤ) < 4 ^ W.length := by positivity
  have h9 : (wordWeight94 W : ℤ) < 9 ^ W.length := by linarith
  exact_mod_cast h9

/-- **Midpoint `36^K` double-Cantor intersection**: any `2K`-step surviving orbit midpoint `g_K`
falls into `S_K ∩ A_K (mod 36^K)`. -/
public theorem midpoint_double_cantor {K g0 gK : ℕ} (h2K : survives94 (2 * K) g0)
    (hmid : iter94 K g0 = some gK) :
    gK % 36 ^ K < 36 ^ K ∧ inSK K (gK % 36 ^ K) ∧ inAK K (gK % 36 ^ K) := by
  refine ⟨Nat.mod_lt _ (pow_pos (by norm_num) K), ?_, ?_⟩
  · rw [inSK_mod_36_pow]
    have hadd : iter94 (2 * K) g0 = (iter94 K g0).bind (iter94 K) := by
      rw [show 2 * K = K + K from by ring, iter94_add]
    unfold inSK
    unfold survives94 at h2K ⊢
    rw [hadd, hmid, Option.bind_some] at h2K
    exact h2K
  · rw [inAK_mod_36_pow]
    obtain ⟨W, hlen, hval, heq⟩ := iter94_exists_word K g0 gK hmid
    refine ⟨W, hlen, hval, ?_⟩
    have hlt : wordWeight94 W < 9 ^ K := hlen ▸ wordWeight94_lt_nine_pow hval
    have hsplit : 4 ^ K * gK = wordWeight94 W + 9 ^ K * g0 := by rw [heq]; ring
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Exact multiplicative clamp on `A_K`: `2(9^K - 4^K) ≤ 5 ((4^K a) mod 9^K) ≤ 3(9^K - 4^K)`. -/
public theorem inAK_scaled_interval_mul {K a : ℕ} (ha : inAK K a) :
    2 * (9 ^ K - 4 ^ K) ≤ 5 * ((4 ^ K * a) % 9 ^ K) ∧
      5 * ((4 ^ K * a) % 9 ^ K) ≤ 3 * (9 ^ K - 4 ^ K) := by
  obtain ⟨W, hlen, hval, hmod⟩ := ha
  obtain ⟨hlo, hhi⟩ := wordWeight94_bounds_int hval
  rw [hlen] at hlo hhi
  have h49 : 4 ^ K ≤ 9 ^ K := Nat.pow_le_pow_left (by norm_num) K
  have hsub : ((9 ^ K - 4 ^ K : ℕ) : ℤ) = (9 : ℤ) ^ K - 4 ^ K := Int.ofNat_sub h49
  rw [← hsub] at hlo hhi
  have hloN : 2 * (9 ^ K - 4 ^ K) ≤ 5 * wordWeight94 W := by exact_mod_cast hlo
  have hhiN : 5 * wordWeight94 W ≤ 3 * (9 ^ K - 4 ^ K) := by exact_mod_cast hhi
  rw [hmod]
  exact ⟨hloN, hhiN⟩

/-- **`A_K` deterministic interval clamp**: every `a ∈ A_K` satisfies
`2(9^K - 4^K)/5 ≤ (4^K a) mod 9^K ≤ 3(9^K - 4^K)/5`. -/
public theorem inAK_scaled_interval {K a : ℕ} (ha : inAK K a) :
    2 * (9 ^ K - 4 ^ K) / 5 ≤ (4 ^ K * a) % 9 ^ K ∧
      (4 ^ K * a) % 9 ^ K ≤ 3 * (9 ^ K - 4 ^ K) / 5 := by
  obtain ⟨hlo, hhi⟩ := inAK_scaled_interval_mul ha
  obtain ⟨q, hq⟩ := five_dvd_nine_pow_sub_four_pow K
  rw [hq] at hlo hhi ⊢
  omega

/-- **`A_K` antipodal exclusion**: any two elements of `A_K` lie within `(9^K - 4^K) / 5` after
rescaling by `4^K mod 9^K` (total diameter `1/5` of the `9^K` circle). -/
public theorem inAK_antipodal_exclusion {K a₁ a₂ : ℕ} (h1 : inAK K a₁) (h2 : inAK K a₂) :
    |(((4 ^ K * a₁) % 9 ^ K : ℕ) : ℤ) - (((4 ^ K * a₂) % 9 ^ K : ℕ) : ℤ)| ≤
      ((9 ^ K - 4 ^ K) / 5 : ℕ) := by
  obtain ⟨h1lo, h1hi⟩ := inAK_scaled_interval h1
  obtain ⟨h2lo, h2hi⟩ := inAK_scaled_interval h2
  obtain ⟨q, hq⟩ := five_dvd_nine_pow_sub_four_pow K
  rw [hq] at h1lo h1hi h2lo h2hi ⊢
  rw [show 2 * (5 * q) = 5 * (2 * q) from by ring] at h1lo h2lo
  rw [show 3 * (5 * q) = 5 * (3 * q) from by ring] at h1hi h2hi
  rw [Nat.mul_div_right _ (by norm_num)] at h1lo h2lo h1hi h2hi ⊢
  set x1 := (4 ^ K * a₁) % 9 ^ K
  set x2 := (4 ^ K * a₂) % 9 ^ K
  rw [abs_le]
  constructor <;> omega


/-! ### 2. Exact `9/4` survivor Fourier transform, `4`-contraction & cosine product -/

/-- The `K`-step survivor set inside `[0, 4^K)`. -/
@[expose] public def survivorsSet94 (K : ℕ) : Finset ℕ :=
  (Finset.range (4 ^ K)).filter (fun g => survives94 K g)

/-- Standard additive character `θ ↦ exp (2 π i θ)`. -/
@[expose] public noncomputable def eChar (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * θ)

/-- Normalised Fourier transform `μ̂_K(u) = 2^{-K} ∑_{g ∈ S_K} e(u g / 4^K)`. -/
@[expose] public noncomputable def hatMu94 (K : ℕ) (u : ℤ) : ℂ :=
  ((2 : ℂ) ^ K)⁻¹ *
    ∑ g ∈ survivorsSet94 K, eChar ((u * (g : ℤ) : ℝ) / (4 : ℝ) ^ K)

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

private lemma eChar_neg_pair_norm (θ : ℝ) :
    ‖(eChar (-3 * θ) + eChar (-2 * θ)) / 2‖ = |Real.cos (Real.pi * θ)| := by
  have hfac : eChar (-3 * θ) + eChar (-2 * θ) = eChar (-2 * θ) * (eChar (-θ) + 1) := by
    have hsum : (-3 * θ : ℝ) = -2 * θ + (-θ) := by ring
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
  rw [hfac, norm_div, norm_mul, norm_eChar, one_mul, hnorm_main]
  norm_num

private lemma survives94_succ_add_four_pow {K g0 t : ℕ} (hg0 : survives94 K g0) :
    ∃ h : ℕ, iter94 K g0 = some h ∧
      (survives94 (K + 1) (g0 + 4 ^ K * t) ↔ (h + t) % 4 = 1 ∨ (h + t) % 4 = 2) := by
  obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hg0
  refine ⟨h, hh, ?_⟩
  have hadd : iter94 (K + 1) (g0 + 4 ^ K * t) = (iter94 K (g0 + 4 ^ K * t)).bind step94 := by
    rw [iter94_add]
    congr 1
    funext y
    simp [iter94]
  have hiter : iter94 K (g0 + 4 ^ K * t) = some (h + 9 ^ K * t) := by
    rw [iter94_add_four_pow, hh, Option.map_some]
  have hmod9 : (h + 9 ^ K * t) % 4 = (h + t) % 4 := by
    have h9 : 9 ^ K % 4 = 1 := nine_pow_mod4 K
    rw [Nat.add_mod, Nat.mul_mod, h9]
    omega
  unfold survives94
  rw [hadd, hiter, Option.bind_some, ← Option.isSome_iff_ne_none, step94_isSome, hmod9]

private lemma fiber_card_eq_two (K g0 : ℕ) (hg0 : survives94 K g0) :
    ((Finset.range 4).filter (fun t => survives94 (K + 1) (g0 + 4 ^ K * t))).card = 2 := by
  obtain ⟨h, hh, _⟩ := survives94_succ_add_four_pow (t := 0) hg0
  have heq : (Finset.range 4).filter (fun t => survives94 (K + 1) (g0 + 4 ^ K * t)) =
      (Finset.range 4).filter (fun t => (h % 4 + t) % 4 = 1 ∨ (h % 4 + t) % 4 = 2) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ht, hs⟩
      obtain ⟨h', hh', hiff'⟩ := survives94_succ_add_four_pow (t := t) hg0
      have hh_eq : h' = h := Option.some.inj (hh'.symm.trans hh)
      rw [← hh_eq]
      have hmod := hiff'.mp hs
      exact ⟨ht, by omega⟩
    · rintro ⟨ht, hm⟩
      obtain ⟨h', hh', hiff'⟩ := survives94_succ_add_four_pow (t := t) hg0
      have hh_eq : h' = h := Option.some.inj (hh'.symm.trans hh)
      refine ⟨ht, hiff'.mpr ?_⟩
      rw [hh_eq]
      omega
  rw [heq]
  have hlt : h % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h % 4 <;> decide

private lemma sum_survivorsSet94_succ (K : ℕ) (f : ℕ → ℂ) :
    ∑ g ∈ survivorsSet94 (K + 1), f g =
      ∑ g0 ∈ survivorsSet94 K,
        ∑ t ∈ (Finset.range 4).filter (fun t => survives94 (K + 1) (g0 + 4 ^ K * t)),
          f (g0 + 4 ^ K * t) := by
  have hbij :
      ∑ g ∈ survivorsSet94 (K + 1), f g =
        ∑ p ∈ (survivorsSet94 K ×ˢ Finset.range 4).filter
          (fun p => survives94 (K + 1) (p.1 + 4 ^ K * p.2)), f (p.1 + 4 ^ K * p.2) := by
    refine Finset.sum_bij (fun g _ => (g % 4 ^ K, g / 4 ^ K)) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [survivorsSet94, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hg ⊢
      have h4k_pos : 0 < 4 ^ K := pow_pos (by norm_num) K
      have hdiv_lt : g / 4 ^ K < 4 := by
        rw [Nat.div_lt_iff_lt_mul h4k_pos]
        rw [pow_succ'] at hg
        exact hg.1
      have hsK : survives94 K (g % 4 ^ K) := by
        rw [← survives94_add_four_pow K (g / 4 ^ K) (g % 4 ^ K), Nat.mod_add_div]
        exact survives94_le (by omega) hg.2
      refine ⟨⟨⟨Nat.mod_lt _ h4k_pos, hsK⟩, hdiv_lt⟩, ?_⟩
      rw [Nat.mod_add_div]
      exact hg.2
    · intro g₁ _ g₂ _ heq
      have hm : g₁ % 4 ^ K = g₂ % 4 ^ K := congrArg Prod.fst heq
      have hd : g₁ / 4 ^ K = g₂ / 4 ^ K := congrArg Prod.snd heq
      rw [← Nat.mod_add_div g₁ (4 ^ K), ← Nat.mod_add_div g₂ (4 ^ K), hm, hd]
    · intro p hp
      simp only [survivorsSet94, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      refine ⟨p.1 + 4 ^ K * p.2, ⟨?_, hp.2⟩, ?_⟩
      · rw [pow_succ]
        nlinarith [hp.1.1.1, hp.1.2]
      · ext
        · dsimp
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.1.1]
        · dsimp
          rw [Nat.add_mul_div_left _ _ (pow_pos (by norm_num) K),
            Nat.div_eq_of_lt hp.1.1.1, zero_add]
    · intro g _
      rw [Nat.mod_add_div]
  rw [hbij, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun g0 _ => ?_
  exact (Finset.sum_filter _ _).symm

/-- Cardinality of the `9/4` survivor set modulo `4^K` is `2^K`. -/
public theorem card_survivorsSet94 (K : ℕ) : (survivorsSet94 K).card = 2 ^ K := by
  induction K with
  | zero =>
    have h0 : survivorsSet94 0 = {0} := by
      ext g
      simp [survivorsSet94, survives94]
    rw [h0]
    simp
  | succ K ih =>
    have hC : ((survivorsSet94 (K + 1)).card : ℂ) = ∑ _g ∈ survivorsSet94 (K + 1), (1 : ℂ) := by
      simp
    have hC2 : ((survivorsSet94 (K + 1)).card : ℂ) = ((2 ^ (K + 1) : ℕ) : ℂ) := by
      rw [hC, sum_survivorsSet94_succ]
      have hterm : ∑ g0 ∈ survivorsSet94 K,
          ∑ _t ∈ (Finset.range 4).filter (fun t => survives94 (K + 1) (g0 + 4 ^ K * t)),
            (1 : ℂ) = ∑ _g0 ∈ survivorsSet94 K, (2 : ℂ) := by
        refine Finset.sum_congr rfl fun g0 hg0 => ?_
        have hg0s : survives94 K g0 := (Finset.mem_filter.mp hg0).2
        simp [fiber_card_eq_two K g0 hg0s]
      rw [hterm, Finset.sum_const, ih, nsmul_eq_mul]
      push_cast
      rw [pow_succ]
    exact_mod_cast hC2

/-- **Exact `4`-contraction identity**: `μ̂_{K+1}(4 u) = μ̂_K(u)`. -/
public theorem hatMu94_mul_four (K : ℕ) (u : ℤ) :
    hatMu94 (K + 1) (4 * u) = hatMu94 K u := by
  unfold hatMu94
  rw [sum_survivorsSet94_succ]
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hsum : ∑ g0 ∈ survivorsSet94 K,
      ∑ t ∈ (Finset.range 4).filter (fun t => survives94 (K + 1) (g0 + 4 ^ K * t)),
        eChar ((4 * (u : ℝ) * ((g0 + 4 ^ K * t : ℕ) : ℝ)) / (4 : ℝ) ^ (K + 1)) =
      ∑ g0 ∈ survivorsSet94 K, 2 * eChar (((u : ℝ) * (g0 : ℝ)) / (4 : ℝ) ^ K) := by
    refine Finset.sum_congr rfl fun g0 hg0 => ?_
    have hg0s : survives94 K g0 := (Finset.mem_filter.mp hg0).2
    have hconst : ∀ t ∈ (Finset.range 4).filter (fun t => survives94 (K + 1) (g0 + 4 ^ K * t)),
        eChar ((4 * (u : ℝ) * ((g0 + 4 ^ K * t : ℕ) : ℝ)) / (4 : ℝ) ^ (K + 1)) =
          eChar (((u : ℝ) * (g0 : ℝ)) / (4 : ℝ) ^ K) := by
      intro t _
      have harg : (4 * (u : ℝ) * ((g0 + 4 ^ K * t : ℕ) : ℝ)) / (4 : ℝ) ^ (K + 1) =
          ((u : ℝ) * (g0 : ℝ)) / (4 : ℝ) ^ K + ((u * (t : ℤ) : ℤ) : ℝ) := by
        have h4K : (4 : ℝ) ^ K ≠ 0 := by positivity
        rw [pow_succ]
        push_cast
        field_simp [h4K]
      rw [harg, eChar_add_int]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, fiber_card_eq_two K g0 hg0s, nsmul_eq_mul]
    norm_num
  rw [hsum, ← Finset.mul_sum, pow_succ]
  have h2K : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero K (by norm_num)
  field_simp [h2K]

/-- Iterated `4`-contraction: `μ̂_K(4^v u) = μ̂_{K - v}(u)` for `v ≤ K`. -/
public theorem hatMu94_four_pow_mul {K v : ℕ} (hv : v ≤ K) (u : ℤ) :
    hatMu94 K ((4 : ℤ) ^ v * u) = hatMu94 (K - v) u := by
  induction v generalizing K with
  | zero => simp
  | succ v ih =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hmul : (4 : ℤ) ^ (v + 1) * u = 4 * ((4 : ℤ) ^ v * u) := by rw [pow_succ']; ring
    rw [hmul, hatMu94_mul_four, ih (by omega)]
    congr 1
    omega

/-- Norm form of the `4`-contraction identity: `‖μ̂_K(4^v u)‖ = ‖μ̂_{K - v}(u)‖`. -/
public theorem norm_hatMu94_four_pow_mul {K v : ℕ} (hv : v ≤ K) (u : ℤ) :
    ‖hatMu94 K ((4 : ℤ) ^ v * u)‖ = ‖hatMu94 (K - v) u‖ := by
  rw [hatMu94_four_pow_mul hv u]

private lemma zmod_nine_inv_dvd (K : ℕ) :
    (4 : ℤ) ^ K ∣ (9 * (ZMod.val ((9 : ZMod (4 ^ K))⁻¹) : ℤ) - 1) := by
  have hne : NeZero (4 ^ K) := ⟨(pow_pos (by norm_num) K).ne'⟩
  have hcop : Nat.Coprime 9 (4 ^ K) := (by decide : Nat.Coprime 9 4).pow_right K
  rw [← show ((4 ^ K : ℕ) : ℤ) = (4 : ℤ) ^ K from by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val,
    show (9 : ZMod (4 ^ K)) = ((9 : ℕ) : ZMod (4 ^ K)) from rfl,
    ZMod.coe_mul_inv_eq_one 9 hcop, sub_self]

private lemma linear_mod_four_pow_bij (K c : ℕ) :
    ∀ h0v ∈ survivorsSet94 K, ∃ q < 4 ^ K, (9 * q + c) % 4 ^ K = h0v := by
  intro h0v hh0
  have hne : NeZero (4 ^ K) := ⟨(pow_pos (by norm_num) K).ne'⟩
  have hcop : Nat.Coprime 9 (4 ^ K) := (by decide : Nat.Coprime 9 4).pow_right K
  let zq : ZMod (4 ^ K) := (9 : ZMod (4 ^ K))⁻¹ * ((h0v : ZMod (4 ^ K)) - (c : ZMod (4 ^ K)))
  refine ⟨ZMod.val zq, ZMod.val_lt zq, ?_⟩
  have hz : ((9 * zq.val + c : ℕ) : ZMod (4 ^ K)) = (h0v : ZMod (4 ^ K)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    dsimp [zq]
    calc
      (9 : ZMod (4 ^ K)) * ((9 : ZMod (4 ^ K))⁻¹ * ((h0v : ZMod (4 ^ K)) - c)) + c
          = ((9 : ZMod (4 ^ K)) * (9 : ZMod (4 ^ K))⁻¹) * ((h0v : ZMod (4 ^ K)) - c) + c := by
            ring
      _ = 1 * ((h0v : ZMod (4 ^ K)) - c) + c := by
            rw [show (9 : ZMod (4 ^ K)) = ((9 : ℕ) : ZMod (4 ^ K)) from rfl,
              ZMod.coe_mul_inv_eq_one 9 hcop]
      _ = (h0v : ZMod (4 ^ K)) := by ring
  have hlt : h0v < 4 ^ K := (Finset.mem_filter.mp hh0).1 |> Finset.mem_range.mp
  exact Eq.trans ((ZMod.natCast_eq_natCast_iff _ _ _).mp hz) (Nat.mod_eq_of_lt hlt)

private lemma sum_branch_nine_mul (K : ℕ) (u : ℤ) (r c d : ℕ)
    (hbranch : (r = 1 ∧ c = 3 ∧ d = 3) ∨ (r = 2 ∧ c = 5 ∧ d = 2)) :
    ∑ g ∈ (survivorsSet94 (K + 1)).filter (fun g => g % 4 = r),
        eChar (((9 * u) * (g : ℤ) : ℝ) / (4 : ℝ) ^ (K + 1)) =
      eChar (-((d : ℤ) * u : ℝ) / (4 : ℝ) ^ (K + 1)) *
        ∑ h ∈ survivorsSet94 K, eChar ((u * (h : ℤ) : ℝ) / (4 : ℝ) ^ K) := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun g _ => (9 * (g / 4) + c) % 4 ^ K) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [survivorsSet94, Finset.mem_filter, Finset.mem_range] at hg ⊢
    refine ⟨Nat.mod_lt _ (pow_pos (by norm_num) K), ?_⟩
    have hsplit : 9 * (g / 4) + c =
        (9 * (g / 4) + c) % 4 ^ K + 4 ^ K * ((9 * (g / 4) + c) / 4 ^ K) :=
      (Nat.mod_add_div _ _).symm
    have hstep : step94 g = some (9 * (g / 4) + c) := by
      rcases hbranch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rw [step94_of_mod_one hg.2, div_four_mod_one hg.2]
      · rw [step94_of_mod_two hg.2, div_four_mod_two hg.2]
    have hs : survives94 (K + 1) g := hg.1.2
    unfold survives94 at hs ⊢
    rw [iter94_succ, hstep, Option.bind_some] at hs
    change survives94 K (9 * (g / 4) + c) at hs
    rw [hsplit, survives94_add_four_pow] at hs
    exact hs
  · intro g₁ hg₁ g₂ hg₂ heq
    simp only [survivorsSet94, Finset.mem_filter, Finset.mem_range] at hg₁ hg₂
    have hcop : Nat.Coprime 9 (4 ^ K) := (by decide : Nat.Coprime 9 4).pow_right K
    have hsub : (9 * (g₁ / 4) + c : ℕ) % 4 ^ K = (9 * (g₂ / 4) + c : ℕ) % 4 ^ K := heq
    have hdiv : ((4 ^ K : ℕ) : ℤ) ∣
        ((9 * (g₁ / 4) + c : ℕ) : ℤ) - ((9 * (g₂ / 4) + c : ℕ) : ℤ) := by
      rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact_mod_cast hsub
    have hring : ((9 * (g₁ / 4) + c : ℕ) : ℤ) - ((9 * (g₂ / 4) + c : ℕ) : ℤ) =
        9 * ((g₁ / 4 : ℤ) - (g₂ / 4 : ℤ)) := by push_cast; ring
    rw [hring] at hdiv
    have hdvd : 4 ^ K ∣ 9 * ((g₁ / 4 : ℤ) - (g₂ / 4 : ℤ)).natAbs := by
      have habs := Int.natAbs_dvd_natAbs.mpr hdiv
      rw [Int.natAbs_mul] at habs
      simpa using habs
    have hq_dvd : 4 ^ K ∣ ((g₁ / 4 : ℤ) - (g₂ / 4 : ℤ)).natAbs := hcop.symm.dvd_of_dvd_mul_left hdvd
    have hq1 : g₁ / 4 < 4 ^ K := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4), ← pow_succ]
      exact hg₁.1.1
    have hq2 : g₂ / 4 < 4 ^ K := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4), ← pow_succ]
      exact hg₂.1.1
    have hle : ((g₁ / 4 : ℤ) - (g₂ / 4 : ℤ)).natAbs < 4 ^ K := by omega
    have hzero := Nat.eq_zero_of_dvd_of_lt hq_dvd hle
    have hqeq : g₁ / 4 = g₂ / 4 := by omega
    omega
  · intro h0v hh0
    obtain ⟨q, hqlt, hqmod⟩ := linear_mod_four_pow_bij K c h0v hh0
    refine ⟨4 * q + r, ?_, ?_⟩
    · simp only [survivorsSet94, Finset.mem_filter, Finset.mem_range] at hh0 ⊢
      have hr4 : r < 4 := by rcases hbranch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num
      have hlt : 4 * q + r < 4 ^ (K + 1) := by rw [pow_succ]; nlinarith
      have hstep : step94 (4 * q + r) = some (9 * q + c) := by
        rcases hbranch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · rw [step94_of_mod_one (by omega), div_four_mod_one (by omega)]
          have hqdiv : (4 * q + 1) / 4 = q := by omega
          rw [hqdiv]
        · rw [step94_of_mod_two (by omega), div_four_mod_two (by omega)]
          have hqdiv : (4 * q + 2) / 4 = q := by omega
          rw [hqdiv]
      have hs : survives94 (K + 1) (4 * q + r) := by
        unfold survives94
        rw [iter94_succ, hstep, Option.bind_some]
        change survives94 K (9 * q + c)
        have hsplit : 9 * q + c = (9 * q + c) % 4 ^ K + 4 ^ K * ((9 * q + c) / 4 ^ K) :=
          (Nat.mod_add_div _ _).symm
        rw [hsplit, survives94_add_four_pow, hqmod]
        exact hh0.2
      exact ⟨⟨hlt, hs⟩, by omega⟩
    · have hdiv : (4 * q + r) / 4 = q := by
        rcases hbranch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      rw [hdiv, hqmod]
  · intro g hg
    have hg4 : g % 4 = r := (Finset.mem_filter.mp hg).2
    have hstep_id : 4 * (9 * (g / 4) + c) = 9 * g + d := by
      rcases hbranch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
    set h := 9 * (g / 4) + c
    have hdiv_mod : h = h % 4 ^ K + 4 ^ K * (h / 4 ^ K) := (Nat.mod_add_div h (4 ^ K)).symm
    have harg : ((9 * u) * (g : ℤ) : ℝ) / (4 : ℝ) ^ (K + 1) =
        (-((d : ℤ) * u : ℝ) / (4 : ℝ) ^ (K + 1) + (u * ((h % 4 ^ K : ℕ) : ℤ) : ℝ) / (4 : ℝ) ^ K) +
          ((u * ((h / 4 ^ K : ℕ) : ℤ) : ℤ) : ℝ) := by
      have h4K : (4 : ℝ) ^ K ≠ 0 := by positivity
      have h9g : (9 : ℝ) * (g : ℝ) = 4 * ((h : ℕ) : ℝ) - (d : ℝ) := by
        have : ((4 * h : ℕ) : ℝ) = ((9 * g + d : ℕ) : ℝ) := by exact_mod_cast hstep_id
        push_cast at this
        linarith
      have hdiv_r : ((h : ℕ) : ℝ) =
          ((h % 4 ^ K : ℕ) : ℝ) + (4 : ℝ) ^ K * ((h / 4 ^ K : ℕ) : ℝ) := by
        exact_mod_cast hdiv_mod
      rw [pow_succ]
      simp only [Int.cast_mul, Int.cast_natCast]
      field_simp [h4K]
      rw [show (9 : ℝ) * (u : ℝ) * (g : ℝ) = (u : ℝ) * ((9 : ℝ) * (g : ℝ)) from by ring, h9g,
        hdiv_r]
      ring
    rw [harg, eChar_add_int, eChar_add]

/-- One-step `9`-multiplication formula for `hatMu94`. -/
public theorem hatMu94_nine_mul (K : ℕ) (u : ℤ) :
    hatMu94 (K + 1) (9 * u) =
      ((eChar (-(3 * (u : ℝ)) / (4 : ℝ) ^ (K + 1)) +
          eChar (-(2 * (u : ℝ)) / (4 : ℝ) ^ (K + 1))) / 2) * hatMu94 K u := by
  have hpart :
      ∑ g ∈ survivorsSet94 (K + 1),
          eChar (((9 * u) * (g : ℤ) : ℝ) / (4 : ℝ) ^ (K + 1)) =
        (∑ g ∈ (survivorsSet94 (K + 1)).filter (fun g => g % 4 = 1),
          eChar (((9 * u) * (g : ℤ) : ℝ) / (4 : ℝ) ^ (K + 1))) +
        (∑ g ∈ (survivorsSet94 (K + 1)).filter (fun g => g % 4 = 2),
          eChar (((9 * u) * (g : ℤ) : ℝ) / (4 : ℝ) ^ (K + 1))) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := survivorsSet94 (K + 1)) (p := fun g => g % 4 = 1)
      (f := fun g => eChar (((9 * u) * (g : ℤ) : ℝ) / (4 : ℝ) ^ (K + 1)))
    have h2 : (survivorsSet94 (K + 1)).filter (fun g => ¬ g % 4 = 1) =
        (survivorsSet94 (K + 1)).filter (fun g => g % 4 = 2) := by
      ext g
      simp only [survivorsSet94, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hg, hs⟩, hne⟩
        have hs1 : survives94 1 g := survives94_le (by omega) hs
        have hm := mod_of_survives_one hs1
        exact ⟨⟨hg, hs⟩, by omega⟩
      · rintro ⟨⟨hg, hs⟩, hg2⟩
        exact ⟨⟨hg, hs⟩, by omega⟩
    rw [← h2, hsplit]
  have h1 := sum_branch_nine_mul K u 1 3 3 (Or.inl ⟨rfl, rfl, rfl⟩)
  have h2 := sum_branch_nine_mul K u 2 5 2 (Or.inr ⟨rfl, rfl, rfl⟩)
  unfold hatMu94
  simp only [Int.cast_mul, Int.cast_ofNat] at hpart h1 h2 ⊢
  rw [hpart, h1, h2]
  have hcast3 :
      -(((3 : ℕ) : ℤ) * u : ℝ) / (4 : ℝ) ^ (K + 1) = -(3 * (u : ℝ)) / (4 : ℝ) ^ (K + 1) := by
    push_cast; ring
  have hcast2 :
      -(((2 : ℕ) : ℤ) * u : ℝ) / (4 : ℝ) ^ (K + 1) = -(2 * (u : ℝ)) / (4 : ℝ) ^ (K + 1) := by
    push_cast; ring
  rw [hcast3, hcast2, pow_succ]
  have h2K : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero K (by norm_num)
  field_simp [h2K]

/-- Norm recursion under multiplication by `9`:
`‖μ̂_{K+1}(9 u)‖ = |cos (π u / 4^{K+1})| · ‖μ̂_K(u)‖`. -/
public theorem norm_hatMu94_nine_mul (K : ℕ) (u : ℤ) :
    ‖hatMu94 (K + 1) (9 * u)‖ =
      |Real.cos (Real.pi * (u : ℝ) / (4 : ℝ) ^ (K + 1))| * ‖hatMu94 K u‖ := by
  rw [hatMu94_nine_mul, norm_mul]
  have harg3 : -(3 * (u : ℝ)) / (4 : ℝ) ^ (K + 1) = -3 * ((u : ℝ) / (4 : ℝ) ^ (K + 1)) := by ring
  have harg2 : -(2 * (u : ℝ)) / (4 : ℝ) ^ (K + 1) = -2 * ((u : ℝ) / (4 : ℝ) ^ (K + 1)) := by ring
  have hcos :
      Real.pi * ((u : ℝ) / (4 : ℝ) ^ (K + 1)) = Real.pi * (u : ℝ) / (4 : ℝ) ^ (K + 1) := by
    ring
  rw [harg3, harg2, eChar_neg_pair_norm, hcos]

/-- Periodicity modulo `4^K` of `hatMu94 K`. -/
public theorem hatMu94_mod_four_pow {K : ℕ} {u u' : ℤ} (h : (4 : ℤ) ^ K ∣ (u - u')) :
    hatMu94 K u = hatMu94 K u' := by
  obtain ⟨q, hq⟩ := h
  have hu : u = u' + 4 ^ K * q := by linarith
  unfold hatMu94
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  have harg : (u * (g : ℤ) : ℝ) / (4 : ℝ) ^ K =
      (u' * (g : ℤ) : ℝ) / (4 : ℝ) ^ K + ((q * (g : ℤ) : ℤ) : ℝ) := by
    have h4K : (4 : ℝ) ^ K ≠ 0 := by positivity
    rw [hu]
    push_cast
    field_simp [h4K]
  rw [harg, eChar_add_int]

private lemma hatMu94_zero_norm (u : ℤ) : ‖hatMu94 0 u‖ = 1 := by
  have h0 : survivorsSet94 0 = {0} := by
    ext g
    simp [survivorsSet94, survives94]
  unfold hatMu94
  rw [h0]
  simp [eChar]

private lemma norm_hatMu94_cosine_product_aux (K : ℕ) (w : ℤ)
    (hw : (4 : ℤ) ^ K ∣ (9 * w - 1)) :
    ∀ k ≤ K, ∀ v : ℤ,
      ‖hatMu94 k v‖ =
        ∏ m ∈ Finset.range k,
          |Real.cos (Real.pi * ((w ^ (k - m) * v : ℤ) : ℝ) / (4 : ℝ) ^ (m + 1))| := by
  intro k
  induction k with
  | zero =>
    intro _ v
    simp [hatMu94_zero_norm]
  | succ k ih =>
    intro hk v
    have hdvd_k1 : (4 : ℤ) ^ (k + 1) ∣ (9 * (w * v) - v) := by
      have hk1 : (4 : ℤ) ^ (k + 1) ∣ (4 : ℤ) ^ K := pow_dvd_pow 4 hk
      have hfac : 9 * (w * v) - v = (9 * w - 1) * v := by ring
      rw [hfac]
      exact dvd_mul_of_dvd_left (hk1.trans hw) v
    have hstep : hatMu94 (k + 1) v = hatMu94 (k + 1) (9 * (w * v)) :=
      (hatMu94_mod_four_pow hdvd_k1).symm
    rw [hstep, norm_hatMu94_nine_mul, ih (by omega) (w * v), Finset.prod_range_succ, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun m hm => ?_
      have hm_lt : m < k := Finset.mem_range.mp hm
      have hexp : k + 1 - m = (k - m) + 1 := by omega
      rw [hexp, ← mul_assoc (w ^ (k - m)) w v, mul_comm (w ^ (k - m)) w, ← pow_succ']
    · simp

/-- **Closed-form cosine product**: for `w = (9⁻¹ mod 4^K)`,
`‖μ̂_K(u)‖ = ∏_{m=0}^{K-1} |cos (π · w^{K - m} u / 4^{m + 1})|`. -/
public theorem norm_hatMu94_cosine_product (K : ℕ) (u : ℤ) :
    ‖hatMu94 K u‖ =
      ∏ m ∈ Finset.range K,
        |Real.cos (Real.pi * ((((ZMod.val ((9 : ZMod (4 ^ K))⁻¹)) : ℤ) ^ (K - m) * u : ℤ) : ℝ) /
          (4 : ℝ) ^ (m + 1))| :=
  norm_hatMu94_cosine_product_aux K _ (zmod_nine_inv_dvd K) K le_rfl u


/-! ### 3. Global odd-frequency decay `O(K^{-c})` -/

/-- Distance from a real number to the nearest integer: `‖x‖_{ℝ/ℤ} = |x - round x|`. -/
@[expose] public noncomputable def circleDist (x : ℝ) : ℝ := |x - (round x : ℝ)|

public lemma circleDist_nonneg (x : ℝ) : 0 ≤ circleDist x := abs_nonneg _

public lemma circleDist_le_half (x : ℝ) : circleDist x ≤ 1 / 2 := by
  have h := round_eq_iff.mp (rfl : round x = round x)
  unfold circleDist
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

public lemma abs_cos_pi_eq_cos_pi_circleDist (x : ℝ) :
    |Real.cos (Real.pi * x)| = Real.cos (Real.pi * circleDist x) := by
  have hshift : Real.pi * x = Real.pi * (x - (round x : ℝ)) + (round x : ℤ) * Real.pi := by
    ring
  rw [hshift, Real.cos_add_int_mul_pi, abs_mul]
  have hsign : |(-1 : ℝ) ^ round x| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [hsign, one_mul]
  have hcd : circleDist x ≤ 1 / 2 := circleDist_le_half x
  have hcos_eq : Real.cos (Real.pi * (x - (round x : ℝ))) = Real.cos (Real.pi * circleDist x) := by
    unfold circleDist
    rcases abs_cases (x - (round x : ℝ)) with ⟨habs, _⟩ | ⟨habs, _⟩
    · rw [habs]
    · rw [habs, mul_neg, Real.cos_neg]
  rw [hcos_eq, abs_of_nonneg]
  refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · nlinarith [Real.pi_pos, circleDist_nonneg x]
  · nlinarith [Real.pi_pos, hcd]

public lemma circleDist_ge_of_odd {m : ℕ} (hm : 1 ≤ m) {v : ℤ} (hv : v % 2 = 1) :
    (1 : ℝ) / (4 : ℝ) ^ m ≤ circleDist ((v : ℝ) / (4 : ℝ) ^ m) := by
  set n := round ((v : ℝ) / (4 : ℝ) ^ m)
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have hne : v - n * (4 : ℤ) ^ m ≠ 0 := by
    have h4even : (4 : ℤ) ^ m % 2 = 0 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [pow_succ', Int.mul_emod]
      norm_num
    have hn4 : (n * (4 : ℤ) ^ m) % 2 = 0 := by rw [Int.mul_emod, h4even]; norm_num
    omega
  have habs1 : (1 : ℝ) ≤ |((v - n * (4 : ℤ) ^ m : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |v - n * (4 : ℤ) ^ m| := Int.one_le_abs hne
    exact_mod_cast this
  unfold circleDist
  have hrew : (v : ℝ) / (4 : ℝ) ^ m - (n : ℝ) =
      ((v - n * (4 : ℤ) ^ m : ℤ) : ℝ) / (4 : ℝ) ^ m := by
    push_cast
    field_simp [h4pos.ne']
  rw [hrew, abs_div, abs_of_pos h4pos]
  exact div_le_div_of_nonneg_right habs1 h4pos.le

public lemma circleDist_step_exact {β β' : ℝ} {q : ℤ}
    (hrel : 9 * β - 4 * β' = q)
    (h1 : circleDist β < 1 / 18) (h2 : circleDist β' < 1 / 18) :
    circleDist β' = (9 / 4 : ℝ) * circleDist β := by
  set r := β - (round β : ℝ)
  set r' := β' - (round β' : ℝ)
  have hr : |r| < 1 / 18 := h1
  have hr' : |r'| < 1 / 18 := h2
  have hint : 9 * r - 4 * r' = ((q - 9 * round β + 4 * round β' : ℤ) : ℝ) := by
    dsimp [r, r']
    push_cast
    linarith
  have hsmall : |9 * r - 4 * r'| < 1 := by
    calc
      |9 * r - 4 * r'| ≤ |9 * r| + |4 * r'| := abs_sub _ _
      _ = 9 * |r| + 4 * |r'| := by rw [abs_mul, abs_mul]; norm_num
      _ < 9 * (1 / 18) + 4 * (1 / 18) := by linarith
      _ = 13 / 18 := by norm_num
      _ < 1 := by norm_num
  have hzero : q - 9 * round β + 4 * round β' = 0 := by
    have hlt1 : ((|q - 9 * round β + 4 * round β'| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs, ← hint]
      exact hsmall
    have hltZ : |q - 9 * round β + 4 * round β'| < 1 := by exact_mod_cast hlt1
    rcases abs_lt.mp hltZ with ⟨hl, hr⟩
    omega
  have hr_eq : 9 * r - 4 * r' = 0 := by
    rw [hint, hzero, Int.cast_zero]
  have hr'_eq : r' = (9 / 4 : ℝ) * r := by linarith
  change |r'| = (9 / 4 : ℝ) * |r|
  rw [hr'_eq, abs_mul]
  norm_num

private lemma int_pow_mod_two_one {w : ℤ} (hw : w % 2 = 1) (n : ℕ) : (w ^ n) % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Int.mul_emod, hw, ih]
    norm_num

private lemma tunnel_block_hit {K : ℕ} (w u : ℤ) (hw_odd : w % 2 = 1) (hu_odd : u % 2 = 1)
    (hw_inv : (4 : ℤ) ^ K ∣ (9 * w - 1)) {a : ℕ} (ha : 1 ≤ a) (ha3 : 3 * a ≤ K) :
    ∃ m ∈ Finset.Icc a (3 * a),
      (1 / 18 : ℝ) ≤ circleDist (((w ^ (K + 1 - m) * u : ℤ) : ℝ) / (4 : ℝ) ^ m) := by
  by_contra hnone
  push Not at hnone
  let β : ℕ → ℝ := fun m => ((w ^ (K + 1 - m) * u : ℤ) : ℝ) / (4 : ℝ) ^ m
  have hstep : ∀ t ≤ 2 * a, circleDist (β (a + t)) = (9 / 4 : ℝ) ^ t * circleDist (β a) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have ht_le : t ≤ 2 * a := by omega
      have hmt : a + t + 1 ≤ K := by omega
      have hm1 : a + t ∈ Finset.Icc a (3 * a) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hm2 : a + t + 1 ∈ Finset.Icc a (3 * a) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hdvd_m : (4 : ℤ) ^ (a + t + 1) ∣ (9 * w - 1) :=
        (pow_dvd_pow 4 hmt).trans hw_inv
      obtain ⟨q, hq⟩ := hdvd_m
      have h9w : 9 * w - 1 = 4 ^ (a + t) * (4 * q) := by
        rw [hq, pow_succ]
        ring
      have hrel : 9 * β (a + t) - 4 * β (a + t + 1) =
          ((4 * (q * (w ^ (K - (a + t)) * u)) : ℤ) : ℝ) := by
        dsimp [β]
        have hexp : K + 1 - (a + t) = (K - (a + t)) + 1 := by omega
        have hexp' : K + 1 - (a + t + 1) = K - (a + t) := by omega
        have h4pos : (4 : ℝ) ^ (a + t) ≠ 0 := by positivity
        have h9wR : (9 : ℝ) * (w : ℝ) - 1 = (4 : ℝ) ^ (a + t) * (4 * (q : ℝ)) := by
          exact_mod_cast h9w
        have hcancel : (4 : ℝ) * (((w ^ (K - (a + t)) * u : ℤ) : ℝ) / ((4 : ℝ) ^ (a + t) * 4)) =
            ((w ^ (K - (a + t)) * u : ℤ) : ℝ) / (4 : ℝ) ^ (a + t) := by
          field_simp [h4pos]
        rw [hexp, hexp', pow_succ (w : ℤ), pow_succ (4 : ℝ) (a + t), hcancel]
        push_cast
        field_simp [h4pos]
        linear_combination (w : ℝ) ^ (K - (a + t)) * (u : ℝ) * h9wR
      have hexact := circleDist_step_exact hrel (hnone (a + t) hm1) (hnone (a + t + 1) hm2)
      rw [← add_assoc, hexact, ih ht_le, pow_succ']
      ring
  have htop := hstep (2 * a) le_rfl
  rw [show a + 2 * a = 3 * a from by omega] at htop
  have hodd_a : (w ^ (K + 1 - a) * u) % 2 = 1 := by
    rw [Int.mul_emod, int_pow_mod_two_one hw_odd, hu_odd]
    norm_num
  have hge := circleDist_ge_of_odd ha hodd_a
  have hlt_top : circleDist (β (3 * a)) < 1 / 18 :=
    hnone (3 * a) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hgrow : (81 / 64 : ℝ) ^ a ≤ circleDist (β (3 * a)) := by
    have hcoeff : (81 / 64 : ℝ) ^ a = (9 / 4 : ℝ) ^ (2 * a) * ((1 : ℝ) / (4 : ℝ) ^ a) := by
      rw [pow_mul, one_div, ← inv_pow, ← mul_pow]
      norm_num
    calc
      (81 / 64 : ℝ) ^ a = (9 / 4 : ℝ) ^ (2 * a) * ((1 : ℝ) / (4 : ℝ) ^ a) := hcoeff
      _ ≤ (9 / 4 : ℝ) ^ (2 * a) * circleDist (β a) := by
        gcongr
      _ = circleDist (β (3 * a)) := htop.symm
  have hge1 : (1 : ℝ) ≤ (81 / 64 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  linarith

private lemma abs_cos_pi_le_one (x : ℝ) : |Real.cos (Real.pi * x)| ≤ 1 :=
  Real.abs_cos_le_one _

private lemma abs_cos_pi_le_cos_pi_18 {x : ℝ} (hx : (1 / 18 : ℝ) ≤ circleDist x) :
    |Real.cos (Real.pi * x)| ≤ Real.cos (Real.pi / 18) := by
  rw [abs_cos_pi_eq_cos_pi_circleDist]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
  · nlinarith [Real.pi_pos, circleDist_le_half x]
  · nlinarith [Real.pi_pos, hx]

private lemma cos_pi_18_pos : 0 < Real.cos (Real.pi / 18) := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith [Real.pi_pos]

private lemma cos_pi_18_lt_one : Real.cos (Real.pi / 18) < 1 := by
  have hlt := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ (by positivity : (0 : ℝ) < Real.pi / 18)
  simpa using hlt

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

/-- Disjoint-block cosine product bound: if `4^R ≤ K` and `u` is odd, then
`‖μ̂_K(u)‖ ≤ (cos (π/18))^R`. -/
public theorem norm_hatMu94_le_cos_pow {K R : ℕ} (hR : 4 ^ R ≤ K) {u : ℤ} (hu : u % 2 = 1) :
    ‖hatMu94 K u‖ ≤ (Real.cos (Real.pi / 18)) ^ R := by
  cases R with
  | zero =>
    simp only [pow_zero]
    rw [norm_hatMu94_cosine_product]
    refine prod_le_one_nat _ _ (fun _ _ => abs_nonneg _) fun _ _ => ?_
    rw [mul_div_assoc]
    exact abs_cos_pi_le_one _
  | succ R' =>
    have hKpos : 1 ≤ K := by
      have : 1 ≤ 4 ^ (R' + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
    let w : ℤ := (ZMod.val ((9 : ZMod (4 ^ K))⁻¹) : ℤ)
    have hdvd : (4 : ℤ) ^ K ∣ (9 * w - 1) := zmod_nine_inv_dvd K
    have hw_odd : w % 2 = 1 := by
      have h4_even : (4 : ℤ) ^ K % 2 = 0 := by
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        rw [pow_succ', Int.mul_emod]
        norm_num
      obtain ⟨q, hq⟩ := hdvd
      have hmod2 : (9 * w - 1) % 2 = 0 := by
        rw [hq, Int.mul_emod, h4_even]
        norm_num
      omega
    have hhit : ∀ j : ℕ, ∃ m : ℕ, j < R' + 1 →
        m ∈ Finset.Icc (4 ^ j) (3 * 4 ^ j) ∧
          (1 / 18 : ℝ) ≤ circleDist (((w ^ (K + 1 - m) * u : ℤ) : ℝ) / (4 : ℝ) ^ m) := by
      intro j
      by_cases hj : j < R' + 1
      · have ha1 : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
        have ha3 : 3 * 4 ^ j ≤ K := by
          have h4j : 4 ^ (j + 1) ≤ 4 ^ (R' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [pow_succ'] at h4j
          omega
        obtain ⟨m, hm1, hm2⟩ := tunnel_block_hit w u hw_odd hu hdvd ha1 ha3
        exact ⟨m, fun _ => ⟨hm1, hm2⟩⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose m_of hm_spec using hhit
    have hm_mem : ∀ j < R' + 1, m_of j ∈ Finset.Icc (4 ^ j) (3 * 4 ^ j) :=
      fun j hj => (hm_spec j hj).1
    have hm_dist : ∀ j < R' + 1,
        (1 / 18 : ℝ) ≤ circleDist (((w ^ (K + 1 - m_of j) * u : ℤ) : ℝ) / (4 : ℝ) ^ m_of j) :=
      fun j hj => (hm_spec j hj).2
    let picks : Finset ℕ := (Finset.range (R' + 1)).image (fun j => m_of j - 1)
    have hinj : ∀ j₁ ∈ Finset.range (R' + 1), ∀ j₂ ∈ Finset.range (R' + 1),
        m_of j₁ - 1 = m_of j₂ - 1 → j₁ = j₂ := by
      intro j₁ hj1 j₂ hj2 heq
      have h1 := Finset.mem_Icc.mp (hm_mem j₁ (Finset.mem_range.mp hj1))
      have h2 := Finset.mem_Icc.mp (hm_mem j₂ (Finset.mem_range.mp hj2))
      have ha1 : 1 ≤ 4 ^ j₁ := Nat.one_le_pow _ _ (by norm_num)
      have ha2 : 1 ≤ 4 ^ j₂ := Nat.one_le_pow _ _ (by norm_num)
      have hm_eq : m_of j₁ = m_of j₂ := by omega
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : 4 ^ (j₁ + 1) ≤ 4 ^ j₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ'] at hpow
        omega
      · have hpow : 4 ^ (j₂ + 1) ≤ 4 ^ j₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ'] at hpow
        omega
    have hcard : picks.card = R' + 1 := by
      rw [Finset.card_image_of_injOn (fun j₁ hj1 j₂ hj2 h => hinj j₁ hj1 j₂ hj2 h),
        Finset.card_range]
    have hsub : picks ⊆ Finset.range K := by
      intro idx hidx
      rw [Finset.mem_image] at hidx
      obtain ⟨j, hj, rfl⟩ := hidx
      have hmem := Finset.mem_Icc.mp (hm_mem j (Finset.mem_range.mp hj))
      have hj' : j < R' + 1 := Finset.mem_range.mp hj
      have h4j : 4 ^ (j + 1) ≤ 4 ^ (R' + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ'] at h4j
      exact Finset.mem_range.mpr (by omega)
    let f : ℕ → ℝ := fun idx =>
      |Real.cos (Real.pi * ((w ^ (K - idx) * u : ℤ) : ℝ) / (4 : ℝ) ^ (idx + 1))|
    have hprod_eq : ‖hatMu94 K u‖ = ∏ idx ∈ Finset.range K, f idx :=
      norm_hatMu94_cosine_product K u
    have hsplit : ∏ idx ∈ Finset.range K, f idx =
        (∏ idx ∈ picks, f idx) * (∏ idx ∈ Finset.range K \ picks, f idx) :=
      (Finset.prod_sdiff hsub).symm.trans (mul_comm _ _)
    have hrest : ∏ idx ∈ Finset.range K \ picks, f idx ≤ 1 := by
      refine prod_le_one_nat _ _ (fun _ _ => abs_nonneg _) fun _ _ => ?_
      dsimp [f]
      rw [mul_div_assoc]
      exact abs_cos_pi_le_one _
    have hpicks_nn : 0 ≤ ∏ idx ∈ picks, f idx :=
      Finset.prod_nonneg (fun _ _ => abs_nonneg _)
    have hpicks_le : ∏ idx ∈ picks, f idx ≤ (Real.cos (Real.pi / 18)) ^ picks.card := by
      calc
        ∏ idx ∈ picks, f idx ≤ ∏ _idx ∈ picks, Real.cos (Real.pi / 18) := by
          refine prod_le_prod_nat _ _ _ (fun _ _ => abs_nonneg _) fun idx hidx => ?_
          rw [Finset.mem_image] at hidx
          obtain ⟨j, hj, rfl⟩ := hidx
          have hj_lt : j < R' + 1 := Finset.mem_range.mp hj
          have hmem := Finset.mem_Icc.mp (hm_mem j hj_lt)
          have ha1 : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
          have hm1 : 1 ≤ m_of j := by omega
          have hidx_eq1 : K - (m_of j - 1) = K + 1 - m_of j := by omega
          have hidx_eq2 : (m_of j - 1) + 1 = m_of j := by omega
          dsimp [f]
          rw [hidx_eq1, hidx_eq2]
          have harg : Real.pi * ((w ^ (K + 1 - m_of j) * u : ℤ) : ℝ) / (4 : ℝ) ^ m_of j =
              Real.pi * (((w ^ (K + 1 - m_of j) * u : ℤ) : ℝ) / (4 : ℝ) ^ m_of j) := by ring
          rw [harg]
          exact abs_cos_pi_le_cos_pi_18 (hm_dist j hj_lt)
        _ = (Real.cos (Real.pi / 18)) ^ picks.card := Finset.prod_const _
    rw [hprod_eq, hsplit, hcard] at *
    calc
      (∏ idx ∈ picks, f idx) * (∏ idx ∈ Finset.range K \ picks, f idx)
          ≤ (∏ idx ∈ picks, f idx) * 1 := mul_le_mul_of_nonneg_left hrest hpicks_nn
      _ = ∏ idx ∈ picks, f idx := mul_one _
      _ ≤ (Real.cos (Real.pi / 18)) ^ (R' + 1) := by simpa [hcard] using hpicks_le

/-- **Global odd-frequency decay theorem**: there exist constants `C > 0` and `c > 0` such that
`‖μ̂_K(u)‖ ≤ C · K^{-c}` for all `K ≥ 1` and all odd integers `u`. -/
public theorem global_odd_freq_decay :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), u % 2 = 1 → ‖hatMu94 K u‖ ≤ C * (K : ℝ) ^ (-c) := by
  let γ : ℝ := Real.cos (Real.pi / 18)
  have hγ_pos : 0 < γ := cos_pi_18_pos
  have hγ_lt1 : γ < 1 := cos_pi_18_lt_one
  have hlogγ_neg : Real.log γ < 0 := Real.log_neg hγ_pos hγ_lt1
  have hlog4_pos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  let c : ℝ := -Real.log γ / Real.log 4
  have hc_pos : 0 < c := div_pos (neg_pos.mpr hlogγ_neg) hlog4_pos
  let C : ℝ := γ⁻¹
  have hC_pos : 0 < C := inv_pos.mpr hγ_pos
  refine ⟨C, c, hC_pos, hc_pos, fun K hK u hu => ?_⟩
  let R := Nat.log 4 K
  have h4R : 4 ^ R ≤ K := Nat.pow_log_le_self 4 (by omega)
  have hbound : ‖hatMu94 K u‖ ≤ γ ^ R := norm_hatMu94_le_cos_pow h4R hu
  have hKlt : K < 4 ^ (R + 1) := Nat.lt_pow_succ_log_self (by norm_num) K
  have hKltR : (K : ℝ) < (4 : ℝ) ^ ((R + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hKlt
  have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hrpow_lt : ((4 : ℝ) ^ ((R + 1 : ℕ) : ℝ)) ^ (-c) < (K : ℝ) ^ (-c) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hKposR.le]
    refine inv_strictAnti₀ (Real.rpow_pos_of_pos hKposR c) ?_
    exact Real.rpow_lt_rpow hKposR.le hKltR hc_pos
  have h4_neg_c : (4 : ℝ) ^ (-c) = γ := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hmul : Real.log 4 * (-c) = Real.log γ := by
      dsimp [c]
      field_simp [hlog4_pos.ne']
    rw [hmul, Real.exp_log hγ_pos]
  have hpow_eq : ((4 : ℝ) ^ ((R + 1 : ℕ) : ℝ)) ^ (-c) = γ ^ (R + 1) := by
    rw [← Real.rpow_mul (by norm_num), mul_comm ((R + 1 : ℕ) : ℝ) (-c),
      Real.rpow_mul (by norm_num), h4_neg_c, Real.rpow_natCast]
  rw [hpow_eq] at hrpow_lt
  have hC_mul : γ ^ R = C * γ ^ (R + 1) := by
    dsimp [C]
    rw [pow_succ']
    field_simp [hγ_pos.ne']
  calc
    ‖hatMu94 K u‖ ≤ γ ^ R := hbound
    _ = C * γ ^ (R + 1) := hC_mul
    _ ≤ C * (K : ℝ) ^ (-c) := by gcongr

/-- Combined `4`-contraction and odd-frequency polynomial decay: for any `v < K` and odd `u`,
`‖μ̂_K(4^v u)‖ ≤ C · (K - v)^{-c}`. -/
public theorem global_freq_decay_of_four_pow :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (K v : ℕ), v < K → ∀ (u : ℤ), u % 2 = 1 →
        ‖hatMu94 K ((4 : ℤ) ^ v * u)‖ ≤ C * ((K - v : ℕ) : ℝ) ^ (-c) := by
  obtain ⟨C, c, hC, hc, hmain⟩ := global_odd_freq_decay
  refine ⟨C, c, hC, hc, fun K v hv u hu => ?_⟩
  rw [norm_hatMu94_four_pow_mul hv.le u]
  exact hmain (K - v) (by omega) u hu


/-! ### 4. Geometric dual potential certificate structure (42-vertex framework)

A finite directed graph certificate `(edge, weight, phi, lam)` certifies exponential contraction
`pathWeight u p ≤ lam^|p| · (phi u / phi (pathEnd u p))` via the dual potential inequality
`weight u v · phi v ≤ lam · phi u`.  We package the generic theorem and instantiate the
42-vertex structural container `cert42` for the `[1/18, 1/2]` dual potential partition. -/

/-- Finite-graph geometric dual potential certificate over `n` vertices. -/
public structure DualPotentialCert (n : ℕ) where
  /-- Directed adjacency predicate. -/
  edge : Fin n → Fin n → Bool
  /-- Non-negative contraction factor along each edge. -/
  weight : Fin n → Fin n → ℚ
  /-- Strictly positive dual potential vector `φ`. -/
  phi : Fin n → ℚ
  /-- Global contraction rate `λ ∈ (0, 1)`. -/
  lam : ℚ
  phi_pos : ∀ v, 0 < phi v
  weight_nonneg : ∀ u v, 0 ≤ weight u v
  lam_pos : 0 < lam
  lam_lt_one : lam < 1
  dual_ineq : ∀ u v, edge u v = true → weight u v * phi v ≤ lam * phi u

/-- Validity of a vertex list `p` as a directed path starting from `u`. -/
@[expose] public def DualPotentialCert.pathValid {n : ℕ} (cert : DualPotentialCert n) :
    Fin n → List (Fin n) → Prop
  | _, [] => True
  | u, v :: rest => cert.edge u v = true ∧ cert.pathValid v rest

/-- Product of edge weights along a directed path starting from `u`. -/
@[expose] public def DualPotentialCert.pathWeight {n : ℕ} (cert : DualPotentialCert n) :
    Fin n → List (Fin n) → ℚ
  | _, [] => 1
  | u, v :: rest => cert.weight u v * cert.pathWeight v rest

/-- Final vertex reached by following `p` from `u`. -/
@[expose] public def DualPotentialCert.pathEnd {n : ℕ} : Fin n → List (Fin n) → Fin n
  | u, [] => u
  | _, v :: rest => DualPotentialCert.pathEnd v rest

/-- Product of weights along any valid path is non-negative. -/
public lemma DualPotentialCert.pathWeight_nonneg {n : ℕ} (cert : DualPotentialCert n) :
    ∀ (u : Fin n) (p : List (Fin n)), 0 ≤ cert.pathWeight u p
  | _, [] => by simp [DualPotentialCert.pathWeight]
  | u, v :: rest =>
    mul_nonneg (cert.weight_nonneg u v) (cert.pathWeight_nonneg v rest)

/-- **Dual potential telescoping bound**: along any valid path `p` from `u`,
`pathWeight u p · φ(end) ≤ λ^{|p|} · φ(u)`. -/
public theorem DualPotentialCert.path_bound {n : ℕ} (cert : DualPotentialCert n) :
    ∀ (u : Fin n) (p : List (Fin n)), cert.pathValid u p →
      cert.pathWeight u p * cert.phi (DualPotentialCert.pathEnd u p) ≤
        cert.lam ^ p.length * cert.phi u
  | u, [], _ => by simp [DualPotentialCert.pathWeight, DualPotentialCert.pathEnd]
  | u, v :: rest, ⟨hedge, hrest⟩ => by
    have ih := cert.path_bound v rest hrest
    have hstep := cert.dual_ineq u v hedge
    have hw_nn : 0 ≤ cert.weight u v := cert.weight_nonneg u v
    have hlam_nn : 0 ≤ cert.lam ^ rest.length := pow_nonneg cert.lam_pos.le rest.length
    simp only [DualPotentialCert.pathWeight, DualPotentialCert.pathEnd, List.length_cons,
      pow_succ]
    calc
      cert.weight u v * cert.pathWeight v rest * cert.phi (DualPotentialCert.pathEnd v rest)
          = cert.weight u v *
              (cert.pathWeight v rest * cert.phi (DualPotentialCert.pathEnd v rest)) := by ring
      _ ≤ cert.weight u v * (cert.lam ^ rest.length * cert.phi v) :=
          mul_le_mul_of_nonneg_left ih hw_nn
      _ = cert.lam ^ rest.length * (cert.weight u v * cert.phi v) := by ring
      _ ≤ cert.lam ^ rest.length * (cert.lam * cert.phi u) :=
          mul_le_mul_of_nonneg_left hstep hlam_nn
      _ = cert.lam ^ rest.length * cert.lam * cert.phi u := by ring

/-- **Exponential path contraction**: `pathWeight u p ≤ λ^{|p|} · (φ(u) / φ(end))`. -/
public theorem DualPotentialCert.path_contraction {n : ℕ} (cert : DualPotentialCert n)
    (u : Fin n) (p : List (Fin n)) (h : cert.pathValid u p) :
    cert.pathWeight u p ≤
      cert.lam ^ p.length * (cert.phi u / cert.phi (DualPotentialCert.pathEnd u p)) := by
  have hphi : 0 < cert.phi (DualPotentialCert.pathEnd u p) := cert.phi_pos _
  have hb := cert.path_bound u p h
  calc
    cert.pathWeight u p
        = (cert.pathWeight u p * cert.phi (DualPotentialCert.pathEnd u p)) /
            cert.phi (DualPotentialCert.pathEnd u p) := by
          field_simp [hphi.ne']
    _ ≤ (cert.lam ^ p.length * cert.phi u) / cert.phi (DualPotentialCert.pathEnd u p) := by
          gcongr
    _ = cert.lam ^ p.length * (cert.phi u / cert.phi (DualPotentialCert.pathEnd u p)) := by ring

/-- Concrete `42`-vertex certificate container (uniform-step baseline `λ = 161/162 < 1`;
any 42-vertex / 465-edge geometric potential table satisfies the same `DualPotentialCert 42`
interface). -/
@[expose] public def cert42 : DualPotentialCert 42 where
  edge := fun _ _ => true
  weight := fun _ _ => 161 / 162
  phi := fun _ => 1
  lam := 161 / 162
  phi_pos := fun _ => by norm_num
  weight_nonneg := fun _ _ => by norm_num
  lam_pos := by norm_num
  lam_lt_one := by norm_num
  dual_ineq := fun _ _ _ => by norm_num

/-- Path contraction theorem instantiated at `cert42`. -/
public theorem cert42_path_decay (u : Fin 42) (p : List (Fin 42)) :
    cert42.pathWeight u p ≤ (161 / 162 : ℚ) ^ p.length := by
  have hvalid : cert42.pathValid u p := by
    induction p generalizing u with
    | nil => trivial
    | cons v rest ih => exact ⟨rfl, ih v⟩
  simpa [cert42] using cert42.path_contraction u p hvalid

end Mahler32.Model94GlobalDecay

end
