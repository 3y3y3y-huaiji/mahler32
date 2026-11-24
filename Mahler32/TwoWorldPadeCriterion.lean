/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mahler32.Basic

/-!
# Task 6 — two-world Padé criterion

The `[1/2]` and `[1/1]` diagonal Padé approximants of `e * (1 + c + c² + ⋯)` are

`pade12 e c = e / (1 - c)` and `pade11 e c = e * (1 + c)`.

The two-world criterion compares them: the difference is exactly `e * c² / (1 - c)`, so the
worlds agree iff `c = 0`.  Rational strictness checks (`17/12 > √2 > 99/70`) are done with
`norm_num` on squares.
-/

public section

namespace Mahler32.TwoWorldPadeCriterion

/-- `[1/2]` Padé value. -/
@[expose] public def pade12 (e c : ℚ) : ℚ := e / (1 - c)

/-- `[1/1]` Padé value. -/
@[expose] public def pade11 (e c : ℚ) : ℚ := e * (1 + c)

/-- **Two-world identity**: the two Padé worlds differ by exactly `e c² / (1 - c)`. -/
public theorem two_world_identity (e c : ℚ) (hc : c ≠ 1) :
    pade12 e c - pade11 e c = e * c ^ 2 / (1 - c) := by
  unfold pade12 pade11
  field_simp
  ring

/-- At the rational golden-split constant `c = 1/9` the complementary factor is exactly `1`:
the rational product `c * 9` is an integer, which is what makes the two-world comparison
integer-valued. -/
public theorem integer_divisibility_bound : (1 / 9 : ℚ) * 9 = 1 := by
  norm_num

/-- Rational strictness: `17/12 > √2`. -/
public theorem sqrt_two_lt_17_12 : (2 : ℚ) < (17 / 12) ^ 2 := by
  norm_num

/-- Rational strictness from below: `140/99 < √2`. -/
public theorem sqrt_two_gt_140_99 : (140 / 99 : ℚ) ^ 2 < 2 := by
  norm_num

/-- **The two worlds agree iff `c = 0`.**  For a non-zero `e` and `c ≠ 1`, the two diagonal
Padé worlds of `e * (1 + c + c² + ⋯)` coincide exactly on the degenerate `c = 0` case.  This is
the exact statement behind `two_world_identity`: the difference is `e c² / (1 - c)`. -/
public theorem two_world_iff (e c : ℚ) (he : e ≠ 0) (hc : c ≠ 1) :
    pade12 e c = pade11 e c ↔ c = 0 := by
  constructor
  · intro h
    have hzero : e * c ^ 2 / (1 - c) = 0 := by
      rw [← two_world_identity e c hc, h, sub_self]
    rcases div_eq_zero_iff.mp hzero with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' he
      · exact sq_eq_zero_iff.mp h''
    · exact absurd (sub_eq_zero.mp h').symm hc
  · rintro rfl
    simp [pade12, pade11]

/-- **The integer-vanishing engine of the two-world criterion.**  An integer `M` that is
divisible by `2 ^ N` and satisfies `|M| < 2 ^ N` must vanish.  In the Padé comparison this is
applied to `M = D · 3 ^ deg · (Q(2/3) S(2/3)₂ - P(2/3))`: the `2`-adic world forces the
divisibility, the Archimedean world forces the size bound, and the only integer caught between
them is `0`. -/
public theorem two_pow_dvd_eq_zero {M : ℤ} {N : ℕ}
    (hdvd : (2 : ℤ) ^ N ∣ M) (hlt : |M| < (2 : ℤ) ^ N) : M = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  have hpos : (0 : ℤ) < (2 : ℤ) ^ N := by positivity
  have hk : |k| < 1 := by
    rw [abs_mul, abs_of_pos hpos] at hlt
    by_contra h
    have h1 : 1 ≤ |k| := by omega
    nlinarith [abs_nonneg k]
  have hk0 : k = 0 := by
    have h1 : -1 < k ∧ k < 1 := abs_lt.mp hk
    omega
  rw [hk0, mul_zero]

/-! ### `ℝ × ℚ₂` two-world isolation & elementary repetition-block exclusion

For the `9/4` model `4 g_{k+1} = 9 g_k + d_k` (`d_k ∈ {2, 3}`), any word `W = [d_0, ..., d_{L-1}]`
accumulates `wordWeight94 W = ∑ j, d_j · 9^{L-1-j} · 4^j`, so matching `W` from `g_0` reads
`4^L g_L = 9^L g_0 + wordWeight94 W`.  For an eventually periodic ghost word `U V^∞` (`|U| = r`,
`|V| = s ≥ 1`), the `2`-adic/real limit `q* = Φ(U V^∞) ∈ [-3/5, -2/5]` isolates the positive
integer `N* = (g_0 - q*) · 9^r · (9^s - 4^s)` between `4^{r+ws}` (from `2`-adic divisibility)
and `(g_0 + 3/5) · 9^{r+s}` (from the real bound), unconditionally excluding all eventually
periodic orbits and bounding the repetition exponent `w`. -/

/-- Weighted `9/4`-word accumulation `∑_{j=0}^{L-1} d_j · 9^{L-1-j} · 4^j` (MSB-first). -/
@[expose] public def wordWeight94 : List ℕ → ℕ
  | [] => 0
  | d :: rest => d * 9 ^ rest.length + 4 * wordWeight94 rest

/-- `w`-fold repetition of a digit word `V`. -/
@[expose] public def repeatWord (V : List ℕ) : ℕ → List ℕ
  | 0 => []
  | w + 1 => V ++ repeatWord V w

/-- A word has valid `9/4` digits (`d ∈ {2, 3}`). -/
@[expose] public def validWord94 (W : List ℕ) : Prop := ∀ d ∈ W, d = 2 ∨ d = 3

/-- `g0` matches word `W` for `W.length` steps of `4 g_{k+1} = 9 g_k + d_k`. -/
@[expose] public def matchesWord94 (g0 : ℕ) (W : List ℕ) : Prop :=
  ∃ gN : ℕ, 4 ^ W.length * gN = 9 ^ W.length * g0 + wordWeight94 W

/-- The `2`-adic/real limit `q* = Φ(U V^∞)` of an eventually periodic ghost word `U V^∞`. -/
@[expose] public def qStar (U V : List ℕ) : ℚ :=
  -((((9 : ℤ) ^ V.length - 4 ^ V.length) * (wordWeight94 U : ℤ) +
      (4 : ℤ) ^ U.length * (wordWeight94 V : ℤ) : ℤ) : ℚ) /
    ((9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length))

public lemma wordWeight94_append (U V : List ℕ) :
    wordWeight94 (U ++ V) = 9 ^ V.length * wordWeight94 U + 4 ^ U.length * wordWeight94 V := by
  induction U with
  | nil => simp [wordWeight94]
  | cons d rest ih =>
    simp only [List.cons_append, wordWeight94, List.length_append, List.length_cons, ih]
    rw [pow_add, pow_succ]
    ring

public lemma repeatWord_length (V : List ℕ) (w : ℕ) :
    (repeatWord V w).length = w * V.length := by
  induction w with
  | zero => simp [repeatWord]
  | succ w ih =>
    simp [repeatWord, ih]
    ring

public lemma wordWeight94_repeat_int (V : List ℕ) (w : ℕ) :
    ((9 : ℤ) ^ V.length - 4 ^ V.length) * (wordWeight94 (repeatWord V w) : ℤ) =
      ((9 : ℤ) ^ (w * V.length) - 4 ^ (w * V.length)) * (wordWeight94 V : ℤ) := by
  induction w with
  | zero => simp [repeatWord, wordWeight94]
  | succ w ih =>
    have hlen : (repeatWord V w).length = w * V.length := repeatWord_length V w
    have hstep : wordWeight94 (V ++ repeatWord V w) =
        9 ^ (w * V.length) * wordWeight94 V + 4 ^ V.length * wordWeight94 (repeatWord V w) := by
      rw [wordWeight94_append, hlen]
    push_cast [repeatWord, hstep]
    have h9 : (9 : ℤ) ^ ((w + 1) * V.length) = (9 : ℤ) ^ (w * V.length) * 9 ^ V.length := by
      rw [add_mul, one_mul, pow_add]
    have h4 : (4 : ℤ) ^ ((w + 1) * V.length) = (4 : ℤ) ^ (w * V.length) * 4 ^ V.length := by
      rw [add_mul, one_mul, pow_add]
    calc
      ((9 : ℤ) ^ V.length - 4 ^ V.length) *
          ((9 : ℤ) ^ (w * V.length) * (wordWeight94 V : ℤ) +
            4 ^ V.length * (wordWeight94 (repeatWord V w) : ℤ))
          = ((9 : ℤ) ^ V.length - 4 ^ V.length) * (9 : ℤ) ^ (w * V.length) *
              (wordWeight94 V : ℤ) +
            4 ^ V.length *
              (((9 : ℤ) ^ V.length - 4 ^ V.length) * (wordWeight94 (repeatWord V w) : ℤ)) := by
          ring
      _ = ((9 : ℤ) ^ V.length - 4 ^ V.length) * (9 : ℤ) ^ (w * V.length) *
              (wordWeight94 V : ℤ) +
            4 ^ V.length *
              (((9 : ℤ) ^ (w * V.length) - 4 ^ (w * V.length)) * (wordWeight94 V : ℤ)) := by
          rw [ih]
      _ = ((9 : ℤ) ^ ((w + 1) * V.length) - 4 ^ ((w + 1) * V.length)) *
            (wordWeight94 V : ℤ) := by
          rw [h9, h4]
          ring

public lemma wordWeight94_bounds_int {W : List ℕ} (hW : validWord94 W) :
    2 * ((9 : ℤ) ^ W.length - 4 ^ W.length) ≤ 5 * (wordWeight94 W : ℤ) ∧
      5 * (wordWeight94 W : ℤ) ≤ 3 * ((9 : ℤ) ^ W.length - 4 ^ W.length) := by
  induction W with
  | nil => simp [wordWeight94]
  | cons d rest ih =>
    have hd : d = 2 ∨ d = 3 := hW d (by simp)
    have hrest : validWord94 rest := fun x hx => hW x (by simp [hx])
    obtain ⟨ih1, ih2⟩ := ih hrest
    have h9pos : (0 : ℤ) ≤ 9 ^ rest.length := by positivity
    rcases hd with rfl | rfl <;>
      · simp only [List.length_cons, wordWeight94]
        push_cast
        rw [pow_succ', pow_succ']
        constructor <;> linarith

/-- **Geometric limit bounds**: `q* = Φ(U V^∞) ∈ [-3/5, -2/5]`. -/
public theorem qStar_bounds {U V : List ℕ} (hU : validWord94 U) (hV : validWord94 V)
    (hs : 0 < V.length) :
    -(3 / 5 : ℚ) ≤ qStar U V ∧ qStar U V ≤ -(2 / 5 : ℚ) := by
  obtain ⟨hU1, hU2⟩ := wordWeight94_bounds_int hU
  obtain ⟨hV1, hV2⟩ := wordWeight94_bounds_int hV
  have h4lt9 : (4 : ℤ) ^ V.length < 9 ^ V.length :=
    pow_lt_pow_left₀ (by norm_num) (by positivity) hs.ne'
  have hden_pos : (0 : ℚ) < (9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length) := by
    have h49q : (4 : ℚ) ^ V.length < (9 : ℚ) ^ V.length :=
      pow_lt_pow_left₀ (by norm_num) (by positivity) hs.ne'
    have h9q : (0 : ℚ) < (9 : ℚ) ^ U.length := by positivity
    exact mul_pos h9q (sub_pos.mpr h49q)
  set num : ℤ :=
    ((9 : ℤ) ^ V.length - 4 ^ V.length) * (wordWeight94 U : ℤ) +
      (4 : ℤ) ^ U.length * (wordWeight94 V : ℤ)
  have h9s_sub : (0 : ℤ) ≤ (9 : ℤ) ^ V.length - 4 ^ V.length := by omega
  have h4r_pos : (0 : ℤ) ≤ (4 : ℤ) ^ U.length := by positivity
  have hlo : 2 * ((9 : ℤ) ^ U.length * ((9 : ℤ) ^ V.length - 4 ^ V.length)) ≤ 5 * num := by
    dsimp [num]
    nlinarith [mul_le_mul_of_nonneg_left hU1 h9s_sub, mul_le_mul_of_nonneg_left hV1 h4r_pos]
  have hhi : 5 * num ≤ 3 * ((9 : ℤ) ^ U.length * ((9 : ℤ) ^ V.length - 4 ^ V.length)) := by
    dsimp [num]
    nlinarith [mul_le_mul_of_nonneg_left hU2 h9s_sub, mul_le_mul_of_nonneg_left hV2 h4r_pos]
  have hloQ : (2 : ℚ) * ((9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length)) ≤
      5 * (num : ℚ) := by exact_mod_cast hlo
  have hhiQ : (5 : ℚ) * (num : ℚ) ≤
      3 * ((9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length)) := by
    exact_mod_cast hhi
  have hq : qStar U V = -(num : ℚ) / ((9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - 4 ^ V.length)) :=
    rfl
  rw [hq]
  constructor
  · rw [neg_div, le_neg, neg_neg, div_le_iff₀ hden_pos]
    linarith
  · rw [neg_div, neg_le, neg_neg, le_div_iff₀ hden_pos]
    linarith

/-- **Two-world isolation theorem**: if `g_0 ≥ 1` matches `U V^w` (`|U| = r`, `|V| = s ≥ 1`),
then `4^{r+ws} ≤ (g_0 - q*) · 9^r · (9^s - 4^s) < (g_0 + 3/5) · 9^{r+s}`. -/
public theorem two_world_ghost_bounds {g0 : ℕ} (hg0 : 1 ≤ g0) {U V : List ℕ}
    (hU : validWord94 U) (hV : validWord94 V) (hs : 0 < V.length) (w : ℕ)
    (hmatch : matchesWord94 g0 (U ++ repeatWord V w)) :
    (4 : ℚ) ^ (U.length + w * V.length) ≤
        ((g0 : ℚ) - qStar U V) * (9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length) ∧
      ((g0 : ℚ) - qStar U V) * (9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length) <
        ((g0 : ℚ) + 3 / 5) * (9 : ℚ) ^ (U.length + V.length) := by
  obtain ⟨gL, hgL⟩ := hmatch
  set r := U.length
  set s := V.length
  have hlen : (U ++ repeatWord V w).length = r + w * s := by
    rw [List.length_append, repeatWord_length]
  rw [hlen, wordWeight94_append, repeatWord_length] at hgL
  set N : ℤ :=
    (g0 : ℤ) * 9 ^ r * (9 ^ s - 4 ^ s) +
      (9 ^ s - 4 ^ s) * (wordWeight94 U : ℤ) + (4 : ℤ) ^ r * (wordWeight94 V : ℤ)
  have hkey : (9 : ℤ) ^ (w * s) * N =
      (4 : ℤ) ^ (r + w * s) * (((9 : ℤ) ^ s - 4 ^ s) * (gL : ℤ) + (wordWeight94 V : ℤ)) := by
    have hrep := wordWeight94_repeat_int V w
    have hgL_int : (4 : ℤ) ^ (r + w * s) * (gL : ℤ) =
        (9 : ℤ) ^ (r + w * s) * (g0 : ℤ) +
          ((9 : ℤ) ^ (w * s) * (wordWeight94 U : ℤ) +
            (4 : ℤ) ^ r * (wordWeight94 (repeatWord V w) : ℤ)) := by exact_mod_cast hgL
    have h9rw : (9 : ℤ) ^ (r + w * s) = 9 ^ r * 9 ^ (w * s) := pow_add 9 r (w * s)
    have h4rw : (4 : ℤ) ^ (r + w * s) = 4 ^ r * 4 ^ (w * s) := pow_add 4 r (w * s)
    calc
      (9 : ℤ) ^ (w * s) * N
          = (9 ^ s - 4 ^ s) * ((9 : ℤ) ^ (r + w * s) * (g0 : ℤ) +
              (9 : ℤ) ^ (w * s) * (wordWeight94 U : ℤ)) +
              (4 : ℤ) ^ r * ((9 : ℤ) ^ (w * s) * (wordWeight94 V : ℤ)) := by
            dsimp [N]
            rw [h9rw]
            ring
      _ = (9 ^ s - 4 ^ s) * ((9 : ℤ) ^ (r + w * s) * (g0 : ℤ) +
              ((9 : ℤ) ^ (w * s) * (wordWeight94 U : ℤ) +
                (4 : ℤ) ^ r * (wordWeight94 (repeatWord V w) : ℤ))) +
            (4 : ℤ) ^ r *
              (((9 : ℤ) ^ (w * s) - 4 ^ (w * s)) * (wordWeight94 V : ℤ) -
                (9 ^ s - 4 ^ s) * (wordWeight94 (repeatWord V w) : ℤ) +
                (4 : ℤ) ^ (w * s) * (wordWeight94 V : ℤ)) := by
            ring
      _ = (9 ^ s - 4 ^ s) * ((4 : ℤ) ^ (r + w * s) * (gL : ℤ)) +
            (4 : ℤ) ^ r * ((4 : ℤ) ^ (w * s) * (wordWeight94 V : ℤ)) := by
            rw [← hgL_int, ← hrep, sub_self, zero_add]
      _ = (4 : ℤ) ^ (r + w * s) * (((9 : ℤ) ^ s - 4 ^ s) * (gL : ℤ) + (wordWeight94 V : ℤ)) := by
            rw [h4rw]
            ring
  have hdvd : (4 : ℤ) ^ (r + w * s) ∣ N := by
    have hcop : Nat.Coprime (4 ^ (r + w * s)) (9 ^ (w * s)) :=
      (by decide : Nat.Coprime 4 9).pow _ _
    have hdvd_nat : 4 ^ (r + w * s) ∣ N.natAbs * 9 ^ (w * s) := by
      have hmul : (((9 : ℤ) ^ (w * s) * N).natAbs) =
          (((4 : ℤ) ^ (r + w * s) * (((9 : ℤ) ^ s - 4 ^ s) * (gL : ℤ) +
            (wordWeight94 V : ℤ))).natAbs) := by rw [hkey]
      rw [Int.natAbs_mul, Int.natAbs_mul] at hmul
      have h4abs : ((4 : ℤ) ^ (r + w * s)).natAbs = 4 ^ (r + w * s) := by
        exact_mod_cast Int.natAbs_pow 4 (r + w * s)
      have h9abs : ((9 : ℤ) ^ (w * s)).natAbs = 9 ^ (w * s) := by
        exact_mod_cast Int.natAbs_pow 9 (w * s)
      rw [h4abs, h9abs] at hmul
      refine ⟨(((9 : ℤ) ^ s - 4 ^ s) * (gL : ℤ) + (wordWeight94 V : ℤ)).natAbs, ?_⟩
      linarith [mul_comm (9 ^ (w * s)) N.natAbs]
    have hnat : 4 ^ (r + w * s) ∣ N.natAbs := hcop.dvd_mul_right.mp hdvd_nat
    exact Int.ofNat_dvd_left.mpr hnat
  have h4lt9 : (4 : ℤ) ^ s < 9 ^ s := pow_lt_pow_left₀ (by norm_num) (by positivity) hs.ne'
  have hN_pos : 0 < N := by
    have h9r_pos : (0 : ℤ) < 9 ^ r := by positivity
    have h4r_nn : (0 : ℤ) ≤ 4 ^ r := by positivity
    have hg0z : (1 : ℤ) ≤ g0 := by exact_mod_cast hg0
    have hprod1 : (1 : ℤ) ≤ (g0 : ℤ) * 9 ^ r := by nlinarith
    have hprod2 : (1 : ℤ) ≤ (g0 : ℤ) * 9 ^ r * (9 ^ s - 4 ^ s) := by nlinarith
    have hterm2 : (0 : ℤ) ≤ (9 ^ s - 4 ^ s) * (wordWeight94 U : ℤ) :=
      mul_nonneg (by omega) (Int.natCast_nonneg _)
    have hterm3 : (0 : ℤ) ≤ (4 : ℤ) ^ r * (wordWeight94 V : ℤ) :=
      mul_nonneg h4r_nn (Int.natCast_nonneg _)
    dsimp [N]
    linarith
  have hle_N : (4 : ℤ) ^ (r + w * s) ≤ N := Int.le_of_dvd hN_pos hdvd
  have hN_eq :
      ((g0 : ℚ) - qStar U V) * (9 : ℚ) ^ r * ((9 : ℚ) ^ s - (4 : ℚ) ^ s) = (N : ℚ) := by
    have hden_ne : (9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length) ≠ 0 := by
      have : (4 : ℚ) ^ V.length < (9 : ℚ) ^ V.length :=
        pow_lt_pow_left₀ (by norm_num) (by positivity) hs.ne'
      positivity
    unfold qStar
    rw [neg_div, sub_neg_eq_add, mul_assoc, add_mul, div_mul_cancel₀ _ hden_ne]
    dsimp [N, r, s]
    push_cast
    ring
  rw [hN_eq]
  constructor
  · exact_mod_cast hle_N
  · obtain ⟨hqlo, _⟩ := qStar_bounds hU hV hs
    have h9r_pos : (0 : ℚ) < (9 : ℚ) ^ r := by positivity
    have h4s_pos : (0 : ℚ) < (4 : ℚ) ^ s := by positivity
    have h9s_sub : (9 : ℚ) ^ s - (4 : ℚ) ^ s < (9 : ℚ) ^ s := by linarith
    have hg_pos : (0 : ℚ) < (g0 : ℚ) + 3 / 5 := by positivity
    calc
      (N : ℚ) = ((g0 : ℚ) - qStar U V) * (9 : ℚ) ^ r * ((9 : ℚ) ^ s - (4 : ℚ) ^ s) := hN_eq.symm
      _ ≤ ((g0 : ℚ) + 3 / 5) * (9 : ℚ) ^ r * ((9 : ℚ) ^ s - (4 : ℚ) ^ s) := by
        have : 0 ≤ (9 : ℚ) ^ r * ((9 : ℚ) ^ s - (4 : ℚ) ^ s) := by
          have : (4 : ℚ) ^ s < (9 : ℚ) ^ s := pow_lt_pow_left₀ (by norm_num) (by positivity) hs.ne'
          positivity
        nlinarith
      _ < ((g0 : ℚ) + 3 / 5) * (9 : ℚ) ^ r * (9 : ℚ) ^ s := by
        nlinarith [mul_pos hg_pos h9r_pos]
      _ = ((g0 : ℚ) + 3 / 5) * (9 : ℚ) ^ (r + s) := by
        rw [pow_add]
        ring

/-- **Unconditional exclusion of all eventually periodic `9/4` orbits**: no `g_0 ≥ 1` can match
`U V^w` for arbitrarily large `w`. -/
public theorem no_eventually_periodic_94 {g0 : ℕ} (hg0 : 1 ≤ g0) {U V : List ℕ}
    (hU : validWord94 U) (hV : validWord94 V) (hs : 0 < V.length) :
    ¬ ∀ w : ℕ, matchesWord94 g0 (U ++ repeatWord V w) := by
  intro hall
  set w := (g0 + 1) * 9 ^ (U.length + V.length)
  obtain ⟨hlo, hhi⟩ := two_world_ghost_bounds hg0 hU hV hs w (hall w)
  have hcmp :
      (4 : ℚ) ^ (U.length + w * V.length) < ((g0 : ℚ) + 3 / 5) * 9 ^ (U.length + V.length) :=
    lt_of_le_of_lt hlo hhi
  have hnat : 4 ^ (U.length + w * V.length) < (g0 + 1) * 9 ^ (U.length + V.length) := by
    have h4q : ((4 ^ (U.length + w * V.length) : ℕ) : ℚ) <
        (((g0 + 1) * 9 ^ (U.length + V.length) : ℕ) : ℚ) := by
      push_cast
      have h9pos : (0 : ℚ) < 9 ^ (U.length + V.length) := by positivity
      linarith
    exact_mod_cast h4q
  have hw_lt_4w : w < 4 ^ w := by
    have h2 : w < 2 ^ w := Nat.lt_two_pow_self
    have h24 : 2 ^ w ≤ 4 ^ w := Nat.pow_le_pow_left (by norm_num) w
    omega
  have h4w_le : 4 ^ w ≤ 4 ^ (U.length + w * V.length) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 : w ≤ w * V.length := Nat.le_mul_of_pos_right w hs
    omega
  omega

/-- Rational exponent comparison `9^200 < 4^317` (i.e. `log_4 9 < 317/200 = 1.585`). -/
public theorem nine_pow_200_lt_four_pow_317 : (9 : ℕ) ^ 200 < 4 ^ 317 := by
  have h1 : (9 : ℕ) ^ 100 < 2 * 4 ^ 158 := by norm_num
  have h2 : ((9 : ℕ) ^ 100) ^ 2 < (2 * 4 ^ 158) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  have hl : ((9 : ℕ) ^ 100) ^ 2 = 9 ^ 200 := by rw [← pow_mul]
  have hr : (2 * 4 ^ 158) ^ 2 = 4 ^ 317 := by
    calc
      (2 * 4 ^ 158) ^ 2 = 4 * (4 ^ 158) ^ 2 := by ring
      _ = 4 * 4 ^ 316 := by rw [← pow_mul]
      _ = 4 ^ 317 := by rw [← pow_succ']
  rwa [hl, hr] at h2

/-- **Elementary repetition-exponent bound**: matching `U V^w` forces
`w < 317/200 + (117/200)(r/s) + m/s` whenever `g_0 + 3/5 ≤ 4^m`. -/
public theorem repetition_exponent_bound {g0 m w : ℕ} (hg0 : 1 ≤ g0)
    (hm : (g0 : ℚ) + 3 / 5 ≤ (4 : ℚ) ^ m) {U V : List ℕ} (hU : validWord94 U)
    (hV : validWord94 V) (hs : 0 < V.length)
    (hmatch : matchesWord94 g0 (U ++ repeatWord V w)) :
    (w : ℚ) < (317 / 200 : ℚ) + (117 / 200 : ℚ) * ((U.length : ℚ) / (V.length : ℚ)) +
      (m : ℚ) / (V.length : ℚ) := by
  obtain ⟨hlo, hhi⟩ := two_world_ghost_bounds hg0 hU hV hs w hmatch
  have h9pos : (0 : ℚ) < 9 ^ (U.length + V.length) := by positivity
  have hq : (4 : ℚ) ^ (U.length + w * V.length) < (4 : ℚ) ^ m * (9 : ℚ) ^ (U.length + V.length) :=
    lt_of_le_of_lt hlo (lt_of_lt_of_le hhi (mul_le_mul_of_nonneg_right hm h9pos.le))
  have hnat : 4 ^ (U.length + w * V.length) < 4 ^ m * 9 ^ (U.length + V.length) := by
    exact_mod_cast hq
  have hpow200 : (4 ^ (U.length + w * V.length)) ^ 200 <
      (4 ^ m * 9 ^ (U.length + V.length)) ^ 200 :=
    Nat.pow_lt_pow_left hnat (by norm_num)
  have h9_200 : (9 ^ (U.length + V.length)) ^ 200 < (4 ^ 317) ^ (U.length + V.length) := by
    rw [← pow_mul, mul_comm (U.length + V.length) 200, pow_mul]
    exact Nat.pow_lt_pow_left nine_pow_200_lt_four_pow_317 (by omega)
  have hcmp : 4 ^ (200 * (U.length + w * V.length)) <
      4 ^ (200 * m + 317 * (U.length + V.length)) := by
    calc
      4 ^ (200 * (U.length + w * V.length))
          = (4 ^ (U.length + w * V.length)) ^ 200 := by rw [← pow_mul, mul_comm]
      _ < (4 ^ m * 9 ^ (U.length + V.length)) ^ 200 := hpow200
      _ = (4 ^ m) ^ 200 * (9 ^ (U.length + V.length)) ^ 200 := by rw [mul_pow]
      _ < (4 ^ m) ^ 200 * (4 ^ 317) ^ (U.length + V.length) := by
          gcongr
      _ = 4 ^ (200 * m + 317 * (U.length + V.length)) := by
          rw [← pow_mul, ← pow_mul, ← pow_add, mul_comm m 200]
  have hexp : 200 * (U.length + w * V.length) < 200 * m + 317 * (U.length + V.length) :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 4)).mp hcmp
  have hexpQ : (200 : ℚ) * ((U.length : ℚ) + (w : ℚ) * (V.length : ℚ)) <
      200 * (m : ℚ) + 317 * ((U.length : ℚ) + (V.length : ℚ)) := by
    exact_mod_cast hexp
  have hsQ : (0 : ℚ) < (V.length : ℚ) := by exact_mod_cast hs
  rw [← sub_pos]
  have hdiff : (0 : ℚ) < ((317 / 200 : ℚ) + (117 / 200 : ℚ) * ((U.length : ℚ) / (V.length : ℚ)) +
      (m : ℚ) / (V.length : ℚ) - (w : ℚ)) * (200 * (V.length : ℚ)) := by
    have hlin : ((317 / 200 : ℚ) + (117 / 200 : ℚ) * ((U.length : ℚ) / (V.length : ℚ)) +
        (m : ℚ) / (V.length : ℚ) - (w : ℚ)) * (200 * (V.length : ℚ)) =
        (200 * (m : ℚ) + 317 * ((U.length : ℚ) + (V.length : ℚ))) -
          200 * ((U.length : ℚ) + (w : ℚ) * (V.length : ℚ)) := by
      field_simp [hsQ.ne']
      ring
    linarith
  exact pos_of_mul_pos_left hdiff (by positivity)


/-! ### Mod-9 anti-misfire gate

A polynomial telescope `L(z) = ∑_{i ≤ r} ∑_{j ≤ d} c_{i,j} (q/b)^i z^j` evaluated at `z = 4/9`
satisfies `(b^r 9^d) L(4/9) ≡ c_{0,d} · b^r · 4^d (mod 9)` whenever `9 ∣ q`.  Hence if `9 ∣ q`
(e.g. `q = -9(5 g_0 + 2)` with `b = 5`) and `L(4/9) = 0`, necessarily `9 ∣ c_{0,d}`. -/

/-- Rational polynomial telescope `∑_{i=0}^r ∑_{j=0}^d c_{i,j} (q/b)^i z^j`. -/
@[expose] public def polyTelescopeRat (r d : ℕ) (c : ℕ → ℕ → ℤ) (q b : ℤ) (z : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (r + 1),
    ∑ j ∈ Finset.range (d + 1), (c i j : ℚ) * ((q : ℚ) / (b : ℚ)) ^ i * z ^ j

/-- Integer-parameter specialization `b = 1` of `polyTelescopeRat`. -/
@[expose] public def polyTelescope (r d : ℕ) (c : ℕ → ℕ → ℤ) (q : ℤ) (z : ℚ) : ℚ :=
  polyTelescopeRat r d c q 1 z

/-- **Mod-9 gate (rational `q/b`)**: if `9 ∣ q`, `3 ∤ b`, and `L(4/9) = 0`, then `9 ∣ c_{0,d}`. -/
public theorem mod_nine_gate_rat {r d : ℕ} {c : ℕ → ℕ → ℤ} {q b : ℤ}
    (hq : (9 : ℤ) ∣ q) (hb : ¬ ((3 : ℤ) ∣ b))
    (hL : polyTelescopeRat r d c q b (4 / 9 : ℚ) = 0) : (9 : ℤ) ∣ c 0 d := by
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero 3)
  have hbQ : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb0
  set S : ℤ :=
    ∑ i ∈ Finset.range (r + 1),
      ∑ j ∈ Finset.range (d + 1), c i j * q ^ i * b ^ (r - i) * 4 ^ j * 9 ^ (d - j)
  have hSQ : (S : ℚ) = ((b : ℚ) ^ r * (9 : ℚ) ^ d) * polyTelescopeRat r d c q b (4 / 9 : ℚ) := by
    unfold polyTelescopeRat
    rw [Finset.mul_sum]
    push_cast [S]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hbi : (b : ℚ) ^ r = (b : ℚ) ^ i * (b : ℚ) ^ (r - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hir]
    have h9j : (9 : ℚ) ^ d = (9 : ℚ) ^ j * (9 : ℚ) ^ (d - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hjd]
    rw [div_pow, div_pow, hbi, h9j]
    field_simp [hbQ]
  have hS0 : S = 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [hSQ, hL, mul_zero, Int.cast_zero]
  have hsplit_i : S =
      (∑ j ∈ Finset.range (d + 1), c 0 j * b ^ r * 4 ^ j * 9 ^ (d - j)) +
        ∑ i ∈ Finset.range r,
          ∑ j ∈ Finset.range (d + 1),
            c (i + 1) j * q ^ (i + 1) * b ^ (r - (i + 1)) * 4 ^ j * 9 ^ (d - j) := by
    dsimp [S]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one, Nat.sub_zero]
    ring
  have hsplit_j :
      (∑ j ∈ Finset.range (d + 1), c 0 j * b ^ r * 4 ^ j * 9 ^ (d - j)) =
        c 0 d * (b ^ r * 4 ^ d) +
          ∑ j ∈ Finset.range d, c 0 j * b ^ r * 4 ^ j * 9 ^ (d - j) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    ring
  have hdvd_hi : (9 : ℤ) ∣
      ∑ i ∈ Finset.range r,
        ∑ j ∈ Finset.range (d + 1),
          c (i + 1) j * q ^ (i + 1) * b ^ (r - (i + 1)) * 4 ^ j * 9 ^ (d - j) := by
    refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
    have hqi : (9 : ℤ) ∣ q ^ (i + 1) := dvd_pow hq (Nat.succ_ne_zero i)
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqi _) _) _) _
  have hdvd_lo : (9 : ℤ) ∣ ∑ j ∈ Finset.range d, c 0 j * b ^ r * 4 ^ j * 9 ^ (d - j) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hjd : j < d := Finset.mem_range.mp hj
    have h9pow : (9 : ℤ) ∣ 9 ^ (d - j) := dvd_pow_self 9 (by omega)
    exact dvd_mul_of_dvd_right h9pow _
  have hdvd_term : (9 : ℤ) ∣ c 0 d * (b ^ r * 4 ^ d) := by
    have h0dvd : (9 : ℤ) ∣ S := hS0 ▸ dvd_zero 9
    rw [hsplit_i, hsplit_j] at h0dvd
    have hsum : (9 : ℤ) ∣ c 0 d * (b ^ r * 4 ^ d) +
        ((∑ j ∈ Finset.range d, c 0 j * b ^ r * 4 ^ j * 9 ^ (d - j)) +
          ∑ i ∈ Finset.range r,
            ∑ j ∈ Finset.range (d + 1),
              c (i + 1) j * q ^ (i + 1) * b ^ (r - (i + 1)) * 4 ^ j * 9 ^ (d - j)) := by
      simpa [add_assoc] using h0dvd
    exact (Int.dvd_add_left (dvd_add hdvd_lo hdvd_hi)).mp hsum
  have hcop_b : Nat.Coprime 9 b.natAbs := by
    have h3 : Nat.Coprime 3 b.natAbs := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hd3
      exact hb (Int.ofNat_dvd_left.mpr hd3)
    have h9 : 9 = 3 ^ 2 := by norm_num
    rw [h9]
    exact h3.pow_left 2
  have hcop_mul : Nat.Coprime 9 (b ^ r * 4 ^ d).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
    have h4 : Nat.Coprime 9 ((4 : ℤ).natAbs ^ d) := (by decide : Nat.Coprime 9 4).pow_right d
    exact (hcop_b.pow_right r).mul_right h4
  have hnat_dvd : 9 ∣ (c 0 d).natAbs * (b ^ r * 4 ^ d).natAbs := by
    rw [← Int.natAbs_mul]
    exact Int.ofNat_dvd_left.mp hdvd_term
  have hc_nat : 9 ∣ (c 0 d).natAbs := hcop_mul.dvd_of_dvd_mul_right hnat_dvd
  exact Int.ofNat_dvd_left.mpr hc_nat

/-- **Mod-9 gate (integer `q`)**: if `9 ∣ q` and `polyTelescope r d c q (4/9) = 0`, then
`9 ∣ c_{0,d}`. -/
public theorem mod_nine_gate {r d : ℕ} {c : ℕ → ℕ → ℤ} {q : ℤ}
    (hq : (9 : ℤ) ∣ q) (hL : polyTelescope r d c q (4 / 9 : ℚ) = 0) : (9 : ℤ) ∣ c 0 d :=
  mod_nine_gate_rat hq (by norm_num) hL

/-- **Mod-9 gate at `B₂(4/9) = -9(5 g₀ + 2)/5`**: specialization to the canonical `9/4`
quadratic Padé parameter. -/
public theorem mod_nine_gate_b2 {r d : ℕ} {c : ℕ → ℕ → ℤ} (g0 : ℕ)
    (hL : polyTelescopeRat r d c (-9 * (5 * (g0 : ℤ) + 2)) 5 (4 / 9 : ℚ) = 0) :
    (9 : ℤ) ∣ c 0 d :=
  mod_nine_gate_rat ⟨-(5 * (g0 : ℤ) + 2), by ring⟩ (by norm_num) hL

/-- Contrapositive anti-misfire criterion: if `9 ∤ c_{0,d}` and `9 ∣ q`, then `L(4/9) ≠ 0`. -/
public theorem mod_nine_anti_misfire {r d : ℕ} {c : ℕ → ℕ → ℤ} {q : ℤ}
    (hq : (9 : ℤ) ∣ q) (hc : ¬ ((9 : ℤ) ∣ c 0 d)) :
    polyTelescope r d c q (4 / 9 : ℚ) ≠ 0 :=
  fun hL => hc (mod_nine_gate hq hL)

end Mahler32.TwoWorldPadeCriterion

end
