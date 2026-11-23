/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# Task 11 — the algebraic-irrational pair branch (Stephan §4.4)

This module closes the gap left open in Ralf Stephan, *arXiv:2609.19007*, §4.4, Theorem 4.15:
for an algebraic irrational multiplier `δ` there are only finitely many "violating" pairs
`(a, c)`, `2 ≤ a < c`, with distinct gaps `c - a`, for which `δ * ((3/2)^c - (3/2)^a)` is an
integer up to an exponentially small error `ϑ^c`.

The only external input is the textbook Schlickewei `p`-adic subspace theorem on `ℚ³`
(Bombieri–Gubler Ch. 7, Evertse's lecture notes), stated as the single named axiom
`schlickewei_subspace_Q3`.

The proof splits into the two complementary cases of the resulting rational linear relation:

* `C = 0` — the relation only involves `(3/2)^a` and `(3/2)^c`; dividing gives a *constant*
  value of `(3/2)^(c-a)`, contradicting strict monotonicity of `s ↦ (3/2)^s` together with
  injectivity of the gap map.
* `C ≠ 0` — solving for `n_{a,c}` produces a rational linear form `α (3/2)^c + β (3/2)^a`
  approximating `δ ((3/2)^c - (3/2)^a)`; dividing by `(3/2)^c` and letting the gap and `c`
  tend to infinity forces `δ = α ∈ ℚ`, contradicting irrationality of `δ`.
-/

public section

namespace Mahler32Conditional

open Filter

/-- The Schlickewei `p`-adic subspace theorem on `ℚ³`, in the special form needed here.

For an algebraic real `δ`, a rational `ϑ ∈ (0, 1)`, and an infinite set `T` of pairs
`2 ≤ a < c` on which `δ * ((3/2)^c - (3/2)^a)` is within `ϑ^c` of an integer `n p`,
there is an infinite subset `T' ⊆ T` and a nonzero rational triple `(A, B, C)` with

`A * (3/2)^c + B * (3/2)^a + C * n p = 0`   for all `p = (a, c) ∈ T'`.

The three Archimedean / `2`-adic / `3`-adic product estimates described in the task card
exactly cancel, producing the `ϑ^c` height bound required by the subspace theorem. -/
axiom schlickewei_subspace_Q3
    (δ : ℝ) (hδ : IsAlgebraic ℚ δ)
    (ϑ : ℚ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (T : Set (ℕ × ℕ)) (hT : T.Infinite)
    (hac : ∀ p ∈ T, 2 ≤ p.1 ∧ p.1 < p.2)
    (n : ℕ × ℕ → ℤ)
    (happrox : ∀ p ∈ T,
      |δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1) - (n p : ℝ)| ≤ (ϑ : ℝ) ^ p.2) :
    ∃ T' ⊆ T, T'.Infinite ∧
      ∃ A B C : ℚ, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
        ∀ p ∈ T', (A : ℝ) * (3 / 2 : ℝ) ^ p.2 + (B : ℝ) * (3 / 2 : ℝ) ^ p.1 +
          (C : ℝ) * (n p : ℝ) = 0

/-! ### Elementary helpers -/

/-- `s ↦ (3/2)^s` is strictly increasing on `ℕ`. -/
private lemma pow_three_halves_strictMono :
    StrictMono (fun s : ℕ => (3 / 2 : ℝ) ^ s) :=
  fun _ _ h => pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 3 / 2) h

/-- An infinite set has two distinct elements. -/
private lemma exists_two_ne {α : Type*} {s : Set α} (h : s.Infinite) :
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q := by
  obtain ⟨p, hp⟩ := h.nonempty
  by_contra hc
  push Not at hc
  have hsub : s.Subsingleton := fun x hx y hy => by rw [hc x hx p hp, hc y hy p hp]
  exact h hsub.finite

/-- The gap map is unbounded on an infinite set on which it is injective. -/
private lemma gap_unbounded {T' : Set (ℕ × ℕ)} (hT' : T'.Infinite)
    (hgap : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T') :
    ∀ N, ∃ p ∈ T', N ≤ p.2 - p.1 := by
  intro N
  by_contra h
  push Not at h
  have hsub : T' ⊆ ⋃ s ∈ Set.Iio N, (T' ∩ {p : ℕ × ℕ | p.2 - p.1 = s}) := by
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨p.2 - p.1, h p hp, hp, rfl⟩
  have hfin : (⋃ s ∈ Set.Iio N, (T' ∩ {p : ℕ × ℕ | p.2 - p.1 = s})).Finite := by
    refine Set.Finite.biUnion (Set.finite_Iio N) ?_
    intro s _
    apply Set.Subsingleton.finite
    intro p hp q hq
    exact hgap hp.1 hq.1 (by simpa using hp.2.trans hq.2.symm)
  exact hT' (hfin.subset hsub)

/-! ### Lemma 1: the `C = 0` branch is impossible -/

/-- If an infinite family of pairs with injective gaps satisfies a *homogeneous* relation
`A (3/2)^c + B (3/2)^a = 0` with `(A, B) ≠ (0, 0)`, then `(3/2)^(c-a)` is constant on the
family, which is impossible. -/
public theorem lemma1_no_C_zero
    (T' : Set (ℕ × ℕ)) (hT' : T'.Infinite)
    (hgap : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T')
    (hac' : ∀ p ∈ T', p.1 < p.2)
    (A B : ℚ) (hAB : A ≠ 0 ∨ B ≠ 0)
    (hrel : ∀ p ∈ T', (A : ℝ) * (3 / 2 : ℝ) ^ p.2 + (B : ℝ) * (3 / 2 : ℝ) ^ p.1 = 0) :
    False := by
  obtain ⟨p0, hp0⟩ := hT'.nonempty
  -- `A` cannot vanish: otherwise `(3/2)^a = 0` at any point of `T'`.
  have hA : A ≠ 0 := by
    intro hA0
    have hB : B ≠ 0 := by
      rcases hAB with h | h
      · exact absurd hA0 h
      · exact h
    have h := hrel p0 hp0
    rw [hA0, Rat.cast_zero] at h
    have hXpos : (0 : ℝ) < (3 / 2) ^ p0.1 := pow_pos (by norm_num) _
    have hzero : (B : ℝ) * (3 / 2) ^ p0.1 = 0 := by simpa using h
    have hB0 : (B : ℝ) = 0 := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hXpos)
    exact hB (by exact_mod_cast hB0)
  have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA
  -- On `T'` the quantity `(3/2)^(c-a)` is pinned to the constant `-B/A`.
  have hkey : ∀ p ∈ T', (3 / 2 : ℝ) ^ (p.2 - p.1) = -((B : ℝ) / (A : ℝ)) := by
    intro p hp
    have hlt := hac' p hp
    have h := hrel p hp
    have hXa : (0 : ℝ) < (3 / 2) ^ p.1 := pow_pos (by norm_num) _
    have hsplit : (3 / 2 : ℝ) ^ p.2 = (3 / 2) ^ (p.2 - p.1) * (3 / 2) ^ p.1 := by
      rw [← pow_add]
      congr 1
      omega
    have hmul : (A : ℝ) * (3 / 2) ^ p.2 = -((B : ℝ) * (3 / 2) ^ p.1) := by linarith
    have h5 : (3 / 2 : ℝ) ^ p.2 = -((B : ℝ) / (A : ℝ)) * (3 / 2) ^ p.1 := by
      field_simp
      linear_combination hmul
    have heq : (3 / 2 : ℝ) ^ (p.2 - p.1) * (3 / 2) ^ p.1 =
        (-((B : ℝ) / (A : ℝ))) * (3 / 2) ^ p.1 := by
      rw [← hsplit]
      exact h5
    exact mul_right_cancel₀ (ne_of_gt hXa) heq
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_two_ne hT'
  have hconst : (3 / 2 : ℝ) ^ (p.2 - p.1) = (3 / 2 : ℝ) ^ (q.2 - q.1) := by
    rw [hkey p hp, hkey q hq]
  have hgaps : p.2 - p.1 = q.2 - q.1 := pow_three_halves_strictMono.injective hconst
  exact hpq (hgap hp hq hgaps)

/-! ### Lemma 2: the `C ≠ 0` branch forces `δ` rational -/

/-- One-step inequality: dividing the approximation by `(3/2)^c` yields
`|δ - α| ≤ |δ + β| (2/3)^(c-a) + (2ϑ/3)^c`. -/
private lemma single_bound {δ : ℝ} {α β : ℚ} {ϑ : ℚ} {a c : ℕ} (hac : a < c)
    (h : |δ * ((3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a) -
        ((α : ℝ) * (3 / 2 : ℝ) ^ c + (β : ℝ) * (3 / 2 : ℝ) ^ a)| ≤ (ϑ : ℝ) ^ c) :
    |δ - (α : ℝ)| ≤ |δ + (β : ℝ)| * ((2 / 3 : ℝ) ^ (c - a)) + (2 * (ϑ : ℝ) / 3) ^ c := by
  have hX : (0 : ℝ) < 3 / 2 := by norm_num
  have hXc : (0 : ℝ) < (3 / 2 : ℝ) ^ c := pow_pos hX _
  have hXa : (0 : ℝ) < (3 / 2 : ℝ) ^ a := pow_pos hX _
  -- Factor the approximation error.
  have hfac : |(3 / 2 : ℝ) ^ c * (δ - (α : ℝ)) - (3 / 2 : ℝ) ^ a * (δ + (β : ℝ))| ≤
      (ϑ : ℝ) ^ c := by
    have e : δ * ((3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a) -
          ((α : ℝ) * (3 / 2 : ℝ) ^ c + (β : ℝ) * (3 / 2 : ℝ) ^ a) =
        (3 / 2 : ℝ) ^ c * (δ - (α : ℝ)) - (3 / 2 : ℝ) ^ a * (δ + (β : ℝ)) := by
      ring
    rw [e] at h
    exact h
  -- Reverse triangle inequality.
  have htri : (3 / 2 : ℝ) ^ c * |δ - (α : ℝ)| ≤
      (3 / 2 : ℝ) ^ a * |δ + (β : ℝ)| + (ϑ : ℝ) ^ c := by
    have h1 : |(3 / 2 : ℝ) ^ c * (δ - (α : ℝ))| =
        (3 / 2 : ℝ) ^ c * |δ - (α : ℝ)| := by
      rw [abs_mul, abs_of_pos hXc]
    have h2 : |(3 / 2 : ℝ) ^ a * (δ + (β : ℝ))| =
        (3 / 2 : ℝ) ^ a * |δ + (β : ℝ)| := by
      rw [abs_mul, abs_of_pos hXa]
    have h3 : |(3 / 2 : ℝ) ^ c * (δ - (α : ℝ))| ≤
        |(3 / 2 : ℝ) ^ c * (δ - (α : ℝ)) - (3 / 2 : ℝ) ^ a * (δ + (β : ℝ))| +
          |(3 / 2 : ℝ) ^ a * (δ + (β : ℝ))| := by
      calc |(3 / 2 : ℝ) ^ c * (δ - (α : ℝ))|
          = |((3 / 2 : ℝ) ^ c * (δ - (α : ℝ)) - (3 / 2 : ℝ) ^ a * (δ + (β : ℝ))) +
              (3 / 2 : ℝ) ^ a * (δ + (β : ℝ))| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [h1, h2] at h3
    linarith
  -- Multiply by `(2/3)^c` and simplify the two products.
  have hcancel : ((2 / 3 : ℝ) ^ c) * ((3 / 2 : ℝ) ^ c) = 1 := by
    rw [← mul_pow]
    norm_num
  have hstep : |δ - (α : ℝ)| =
      ((2 / 3 : ℝ) ^ c) * ((3 / 2 : ℝ) ^ c * |δ - (α : ℝ)|) := by
    rw [← mul_assoc, hcancel, one_mul]
  have hpos : (0 : ℝ) < (2 / 3 : ℝ) ^ c := pow_pos (by norm_num) _
  have hmain : |δ - (α : ℝ)| ≤
      ((2 / 3 : ℝ) ^ c) * ((3 / 2 : ℝ) ^ a * |δ + (β : ℝ)| + (ϑ : ℝ) ^ c) := by
    rw [hstep]
    exact mul_le_mul_of_nonneg_left htri (le_of_lt hpos)
  -- Identify the two products.
  have e1 : (2 / 3 : ℝ) ^ c * (3 / 2 : ℝ) ^ a = (2 / 3 : ℝ) ^ (c - a) := by
    have hR : (2 / 3 : ℝ) ^ (c - a) * (2 / 3 : ℝ) ^ a = (2 / 3 : ℝ) ^ c := by
      rw [← pow_add]
      congr 1
      omega
    refine mul_right_cancel₀ (by positivity : ((2 / 3 : ℝ) ^ a) ≠ 0) ?_
    rw [mul_assoc, show (3 / 2 : ℝ) ^ a * (2 / 3 : ℝ) ^ a = 1 by
      rw [← mul_pow]; norm_num, mul_one, hR]
  have e2 : (2 / 3 : ℝ) ^ c * (ϑ : ℝ) ^ c = (2 * (ϑ : ℝ) / 3) ^ c := by
    rw [← mul_pow]
    congr 1
    ring
  calc |δ - (α : ℝ)|
      ≤ ((2 / 3 : ℝ) ^ c) * ((3 / 2 : ℝ) ^ a * |δ + (β : ℝ)| + (ϑ : ℝ) ^ c) := hmain
    _ = |δ + (β : ℝ)| * ((2 / 3 : ℝ) ^ c * (3 / 2 : ℝ) ^ a) +
          (2 / 3 : ℝ) ^ c * (ϑ : ℝ) ^ c := by ring
    _ = |δ + (β : ℝ)| * ((2 / 3 : ℝ) ^ (c - a)) + (2 * (ϑ : ℝ) / 3) ^ c := by
      rw [e1, e2]

/-- If an irrational `δ` is approximated, up to `ϑ^c`, by rational linear forms
`α (3/2)^c + β (3/2)^a` on an infinite family with distinct gaps, then `δ` would be rational,
impossible. -/
public theorem lemma2_no_C_ne_zero
    (δ : ℝ) (hδ : Irrational δ)
    (ϑ : ℚ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (T' : Set (ℕ × ℕ)) (hT' : T'.Infinite)
    (hgap : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T')
    (hac' : ∀ p ∈ T', p.1 < p.2)
    (α β : ℚ)
    (happrox : ∀ p ∈ T',
      |δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1) -
        ((α : ℝ) * (3 / 2 : ℝ) ^ p.2 + (β : ℝ) * (3 / 2 : ℝ) ^ p.1)| ≤ (ϑ : ℝ) ^ p.2) :
    False := by
  -- Uniform bound in the gap length `N`.
  have hforall : ∀ N : ℕ, |δ - (α : ℝ)| ≤
      |δ + (β : ℝ)| * (2 / 3 : ℝ) ^ N + (2 * (ϑ : ℝ) / 3) ^ N := by
    intro N
    obtain ⟨p, hp, hgapN⟩ := gap_unbounded hT' hgap N
    have hlt := hac' p hp
    have hb := single_bound (δ := δ) (α := α) (β := β) (ϑ := ϑ) hlt (happrox p hp)
    have h1 : (2 / 3 : ℝ) ^ (p.2 - p.1) ≤ (2 / 3 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hgapN
    have h2 : (2 * (ϑ : ℝ) / 3) ^ p.2 ≤ (2 * (ϑ : ℝ) / 3) ^ N := by
      refine pow_le_pow_of_le_one (by positivity) ?_ ?_
      · have : (ϑ : ℝ) < 1 := by exact_mod_cast hϑ1
        nlinarith
      · omega
    have hmul : |δ + (β : ℝ)| * (2 / 3 : ℝ) ^ (p.2 - p.1) ≤
        |δ + (β : ℝ)| * (2 / 3 : ℝ) ^ N :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith
  -- Both geometric terms tend to `0`.
  have hg : Tendsto (fun N : ℕ => |δ + (β : ℝ)| * (2 / 3 : ℝ) ^ N +
      (2 * (ϑ : ℝ) / 3) ^ N) atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => (2 / 3 : ℝ) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun N : ℕ => (2 * (ϑ : ℝ) / 3) ^ N) atTop (nhds 0) := by
      refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
      have : (ϑ : ℝ) < 1 := by exact_mod_cast hϑ1
      nlinarith
    simpa using (h1.const_mul |δ + (β : ℝ)|).add h2
  have hlim : |δ - (α : ℝ)| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hg hforall
  have hzero : |δ - (α : ℝ)| = 0 := le_antisymm hlim (abs_nonneg _)
  have hδα : δ = (α : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp hzero)
  exact hδ ⟨α, hδα.symm⟩

/-! ### Main theorem: finiteness of the pair branch -/

/-- **Task 11, main theorem.** For an algebraic irrational `δ` and a rational `ϑ ∈ (0, 1)`,
any set `T` of pairs `(a, c)` with `2 ≤ a < c` and distinct gaps `c - a` on which
`δ * ((3/2)^c - (3/2)^a)` is within `ϑ^c` of an integer is finite. -/
public theorem algebraic_pair_branch_finite
    (δ : ℝ) (hδalg : IsAlgebraic ℚ δ) (hδirr : Irrational δ)
    (ϑ : ℚ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (T : Set (ℕ × ℕ))
    (hgap : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T)
    (hac : ∀ p ∈ T, 2 ≤ p.1 ∧ p.1 < p.2)
    (n : ℕ × ℕ → ℤ)
    (happrox : ∀ p ∈ T,
      |δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1) - (n p : ℝ)| ≤ (ϑ : ℝ) ^ p.2) :
    T.Finite := by
  by_contra hfin
  have hTinf : T.Infinite := hfin
  obtain ⟨T', hT'sub, hT'inf, A, B, C, hABC, hrel⟩ :=
    schlickewei_subspace_Q3 δ hδalg ϑ hϑ0 hϑ1 T hTinf hac n happrox
  have hac' : ∀ p ∈ T', 2 ≤ p.1 ∧ p.1 < p.2 := fun p hp => hac p (hT'sub hp)
  have hgap' : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T' := hgap.mono hT'sub
  have happrox' : ∀ p ∈ T',
      |δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1) - (n p : ℝ)| ≤ (ϑ : ℝ) ^ p.2 :=
    fun p hp => happrox p (hT'sub hp)
  by_cases hC : C = 0
  · -- Case `C = 0`: the homogeneous relation is impossible.
    have hAB : A ≠ 0 ∨ B ≠ 0 := by
      rcases hABC with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hC h
    refine lemma1_no_C_zero T' hT'inf hgap' (fun p hp => (hac' p hp).2) A B hAB ?_
    intro p hp
    have h := hrel p hp
    rw [hC, Rat.cast_zero, zero_mul, add_zero] at h
    exact h
  · -- Case `C ≠ 0`: solve for the integer and apply Lemma 2.
    have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC
    refine lemma2_no_C_ne_zero δ hδirr ϑ hϑ0 hϑ1 T' hT'inf hgap'
      (fun p hp => (hac' p hp).2) (-A / C) (-B / C) ?_
    intro p hp
    have h := hrel p hp
    have hnn : (n p : ℝ) =
        -((A : ℝ) * (3 / 2 : ℝ) ^ p.2 + (B : ℝ) * (3 / 2 : ℝ) ^ p.1) / (C : ℝ) := by
      rw [eq_div_iff hC', mul_comm (n p : ℝ)]
      linarith
    have hcast : (-A / C : ℚ) = -(A / C) := by ring
    have hcast2 : (-B / C : ℚ) = -(B / C) := by ring
    have hrw : (n p : ℝ) = ((-A / C : ℚ) : ℝ) * (3 / 2 : ℝ) ^ p.2 +
        ((-B / C : ℚ) : ℝ) * (3 / 2 : ℝ) ^ p.1 := by
      rw [hnn]
      push_cast
      ring
    have := happrox' p hp
    rw [hrw] at this
    exact this

end Mahler32Conditional
