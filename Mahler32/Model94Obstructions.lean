/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# The `9/4` finite-roof arithmetic obstruction

This module formalises, with **no `sorry`, no `native_decide`, and no custom axiom**, the
finite-roof arithmetic obstruction for the `9/4` model

`4 g_{k+1} = 9 g_k + d_k,   d_k ∈ {2, 3}`,

i.e. the integer map `step94` that keeps only `g % 4 ∈ {1, 2}` (residue `1` adds `3`, residue `2`
adds `2`).  Seven groups of results are proved:

1. `mirror_conservation_94` — exact mirror twin conservation `gₖ + g̃ₖ = 9^k · 4^{N-k} - 1`.
2. `even_rung_mirror_annihilation` — at an even rung `N = 2m` no mirror twin pair both survives
   `N + 2` steps.
3. `forbidden_sum_c2_mod4` — if `g + g' = c · 4^k - 1` with `c ≡ 2 (mod 4)` then both cannot
   survive `k + 1` steps.
4. `odd_rung_klein4_no_four` — the **general odd-`N`** Klein-4 exclusion: for every odd `N ≥ 3`,
   `g < 4^{N-1}`, `δ ∈ {1,2,3}`, the four sibling/mirror points `g`, `g + δ·4^{N-1}`, `4^N-1-g`,
   `4^N-1-(g+δ·4^{N-1})` cannot all survive `N+1` steps; at most three survive.  The `N = 3`
   `decide` instance `odd_rung_klein4_exclusion` is kept as a concrete kernel witness.
5. `sum_shadow_exact` / `diff_shadow_exact` — the independent sum and difference shadow dynamics
   reproduce the pair sum / difference exactly.
6. `base9_transducer_exact` / `base9_digit_sum_conservation` — the carry-free base-9 transducer and
   its exact digit-sum conservation law.
7. `finite_roof_block_certificate` — the kernel-checked finite-roof mirror-block bound
   `8 · #{g < 256 : survives94 6 g} ≤ 3 · #{g < 256 : survives94 4 g}` in the common window
   `[0, 4^4) = [0,256)` (the two sides are `8 · 4 = 32` and `3 · 16 = 48`), together with the
   **general lifting engine** `step94_add_four_pow`, `iter94_add_four_pow`,
   `survives94_add_four_pow`: survival to any fixed horizon `k` is periodic with period `4^k`, so a
   finite window at horizon `k` exhausts all residues for that horizon.  The analogous ratios at
   larger moduli (`4^6, 4^7, 4^9`) remain a script certificate; no general-`N` inequality
   `8|S_{N+2}| ≤ 3|S_N|` is asserted.

The general statements in groups 1–6 and the locality/lifting lemmas are proved over all `N`;
group 7's roof ratio at a fixed window is kernel `decide`, with wider moduli reproduced by
`scripts/generate_certificates.py`.  Nothing here asserts the Mahler `3/2` or `9/4` conjectures.
-/

public section

namespace Mahler32.Model94Obstructions

@[expose] public def step94 (g : ℕ) : Option ℕ :=
  match g % 4 with
  | 1 => some ((9 * g + 3) / 4)
  | 2 => some ((9 * g + 2) / 4)
  | _ => none

@[expose] public def iter94 : ℕ → ℕ → Option ℕ
  | 0, g => some g
  | k + 1, g => (step94 g).bind (iter94 k)

/-- `g` survives at least `k` steps (equivalently `(iter94 k g).isSome`). -/
@[expose] public def survives94 (k g : ℕ) : Prop := iter94 k g ≠ none

public instance instDecidablePredSurvives (k : ℕ) : DecidablePred (fun g => survives94 k g) :=
  fun g => inferInstanceAs (Decidable (iter94 k g ≠ none))

@[simp] public lemma iter94_zero (g : ℕ) : iter94 0 g = some g := rfl

public lemma iter94_succ (k g : ℕ) : iter94 (k + 1) g = (step94 g).bind (iter94 k) := rfl

public lemma step94_of_mod_one {g : ℕ} (h : g % 4 = 1) : step94 g = some ((9 * g + 3) / 4) := by
  simp [step94, h]

public lemma step94_of_mod_two {g : ℕ} (h : g % 4 = 2) : step94 g = some ((9 * g + 2) / 4) := by
  simp [step94, h]

public lemma step94_isSome {g : ℕ} : (step94 g).isSome ↔ g % 4 = 1 ∨ g % 4 = 2 := by
  have hlt : g % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : g % 4 <;> simp [step94, h]

public lemma div_four_mod_one {g : ℕ} (h : g % 4 = 1) : (9 * g + 3) / 4 = 9 * (g / 4) + 3 := by
  have hg : g = 4 * (g / 4) + 1 := by
    have hdiv := Nat.div_add_mod g 4
    omega
  have he : 9 * g + 3 = 4 * (9 * (g / 4) + 3) := by
    conv_lhs => rw [hg]
    ring
  rw [he]
  exact Nat.mul_div_cancel_left (9 * (g / 4) + 3) (by norm_num)

public lemma div_four_mod_two {g : ℕ} (h : g % 4 = 2) : (9 * g + 2) / 4 = 9 * (g / 4) + 5 := by
  have hg : g = 4 * (g / 4) + 2 := by
    have hdiv := Nat.div_add_mod g 4
    omega
  have he : 9 * g + 2 = 4 * (9 * (g / 4) + 5) := by
    conv_lhs => rw [hg]
    ring
  rw [he]
  exact Nat.mul_div_cancel_left (9 * (g / 4) + 5) (by norm_num)

public lemma four_pow_mul_sub_one_mod (N u : ℕ) (hN : 1 ≤ N) (hu : 1 ≤ u) :
    (4 ^ N * u - 1) % 4 = 3 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hcase : 4 ^ (N' + 1) * u - 1 = 4 * (4 ^ N' * u) - 1 := by
    have hpow : 4 ^ (N' + 1) * u = 4 * (4 ^ N' * u) := by rw [pow_succ]; ring
    rw [hpow]
  rw [hcase]
  obtain ⟨m, hm'⟩ : ∃ m, 4 ^ N' * u = m + 1 := ⟨4 ^ N' * u - 1, by
    have h1 : 0 < 4 ^ N' := by positivity
    have : 1 ≤ 4 ^ N' * u := Nat.mul_pos h1 (by omega)
    omega⟩
  rw [hm']
  have : 4 * (m + 1) - 1 = 4 * m + 3 := by omega
  rw [this]
  omega

public lemma mod_two_of_sum {g g' : ℕ} (h1 : g % 4 = 1) (h2 : (g + g') % 4 = 3) : g' % 4 = 2 := by
  have hkey : (g + g') % 4 = (g % 4 + g' % 4) % 4 := Nat.add_mod g g' 4
  rw [h2, h1] at hkey
  have hlt : g' % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : g' % 4 <;> omega

public lemma mod_one_of_sum {g g' : ℕ} (h1 : g % 4 = 2) (h2 : (g + g') % 4 = 3) : g' % 4 = 1 := by
  have hkey : (g + g') % 4 = (g % 4 + g' % 4) % 4 := Nat.add_mod g g' 4
  rw [h2, h1] at hkey
  have hlt : g' % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : g' % 4 <;> omega

public lemma sum_decomp_left {g g' : ℕ} (h1 : g % 4 = 1) (h2 : g' % 4 = 2) :
    g + g' = 4 * (g / 4 + g' / 4) + 3 := by
  have hg : g = 4 * (g / 4) + 1 := by have := Nat.div_add_mod g 4; omega
  have hg' : g' = 4 * (g' / 4) + 2 := by have := Nat.div_add_mod g' 4; omega
  omega

public lemma sum_decomp_right {g g' : ℕ} (h1 : g % 4 = 2) (h2 : g' % 4 = 1) :
    g + g' = 4 * (g / 4 + g' / 4) + 3 := by
  have hg : g = 4 * (g / 4) + 2 := by have := Nat.div_add_mod g 4; omega
  have hg' : g' = 4 * (g' / 4) + 1 := by have := Nat.div_add_mod g' 4; omega
  omega

public lemma step_pair (N u : ℕ) (hN : 1 ≤ N) (hu : 1 ≤ u)
    {g g' h : ℕ} (hsum : g + g' = 4 ^ N * u - 1) (hstep : step94 g = some h) :
    ∃ h', step94 g' = some h' ∧ h + h' = 9 * 4 ^ (N - 1) * u - 1 := by
  have hpow : 4 ^ N * u = 4 * (4 ^ (N - 1) * u) := by
    calc 4 ^ N * u = 4 ^ (N - 1 + 1) * u := by rw [Nat.sub_add_cancel hN]
      _ = (4 ^ (N - 1) * 4) * u := by rw [pow_succ]
      _ = 4 * (4 ^ (N - 1) * u) := by ring
  have hmod := four_pow_mul_sub_one_mod N u hN hu
  have hsummod : (g + g') % 4 = 3 := by rw [hsum, hmod]
  have hsome : (step94 g).isSome := by rw [hstep]; rfl
  have hm : 1 ≤ 4 ^ (N - 1) * u := by
    have h1 : 0 < 4 ^ (N - 1) := by positivity
    exact Nat.mul_pos h1 (by omega)
  rcases step94_isSome.mp hsome with hg1 | hg2
  · have hg'2 : g' % 4 = 2 := mod_two_of_sum hg1 hsummod
    have hh : h = 9 * (g / 4) + 3 := by
      have e1 := step94_of_mod_one hg1
      rw [e1] at hstep
      have hval : (9 * g + 3) / 4 = h := by simpa using hstep
      rw [← hval, div_four_mod_one hg1]
    have hh' : (9 * g' + 2) / 4 = 9 * (g' / 4) + 5 := div_four_mod_two hg'2
    refine ⟨(9 * g' + 2) / 4, step94_of_mod_two hg'2, ?_⟩
    have hD : g / 4 + g' / 4 = 4 ^ (N - 1) * u - 1 := by
      have hsd := sum_decomp_left hg1 hg'2
      omega
    have hP : 9 * 4 ^ (N - 1) * u = 9 * (4 ^ (N - 1) * u) := by ring
    rw [hh, hh', hP]
    omega
  · have hg'1 : g' % 4 = 1 := mod_one_of_sum hg2 hsummod
    have hh : h = 9 * (g / 4) + 5 := by
      have e1 := step94_of_mod_two hg2
      rw [e1] at hstep
      have hval : (9 * g + 2) / 4 = h := by simpa using hstep
      rw [← hval, div_four_mod_two hg2]
    have hh' : (9 * g' + 3) / 4 = 9 * (g' / 4) + 3 := div_four_mod_one hg'1
    refine ⟨(9 * g' + 3) / 4, step94_of_mod_one hg'1, ?_⟩
    have hD : g / 4 + g' / 4 = 4 ^ (N - 1) * u - 1 := by
      have hsd := sum_decomp_right hg2 hg'1
      omega
    have hP : 9 * 4 ^ (N - 1) * u = 9 * (4 ^ (N - 1) * u) := by ring
    rw [hh, hh', hP]
    omega

public lemma pair_iter (k : ℕ) :
    ∀ (N u : ℕ), 1 ≤ N → 1 ≤ u → k ≤ N →
      ∀ (g g' : ℕ), g + g' = 4 ^ N * u - 1 →
        ∀ a : ℕ, iter94 k g = some a →
          ∃ b : ℕ, iter94 k g' = some b ∧ a + b = 9 ^ k * 4 ^ (N - k) * u - 1 := by
  induction k with
  | zero =>
    intro N u hN hu hk g g' hsum a ha
    have ha' : a = g := by simpa using ha.symm
    subst ha'
    refine ⟨g', rfl, ?_⟩
    simpa using hsum
  | succ k ih =>
    intro N u hN hu hk g g' hsum a ha
    rw [iter94_succ] at ha
    obtain ⟨h, hstep, hrest⟩ := Option.bind_eq_some_iff.mp ha
    have hk' : k ≤ N - 1 := by omega
    obtain ⟨h', hstep', hsum'⟩ := step_pair N u hN hu hsum hstep
    rcases k with _ | k'
    · have ha' : a = h := by simpa using hrest.symm
      refine ⟨h', ?_, ?_⟩
      · rw [iter94_succ, hstep']; rfl
      · rw [ha', hsum']; norm_num
    · have hN' : 1 ≤ N - 1 := by omega
      have hu' : 1 ≤ 9 * u := by omega
      have hsum'' : h + h' = 4 ^ (N - 1) * (9 * u) - 1 := by
        rw [hsum']
        congr 1
        ring
      obtain ⟨b, hb, hbeq⟩ := ih (N - 1) (9 * u) hN' hu' hk' h h' hsum'' a hrest
      refine ⟨b, ?_, ?_⟩
      · rw [iter94_succ, hstep']; exact hb
      · show a + b = 9 ^ (k' + 2) * 4 ^ (N - (k' + 2)) * u - 1
        have hEq : 9 ^ (k' + 2) * 4 ^ (N - (k' + 2)) * u
            = 9 ^ (k' + 1) * 4 ^ ((N - 1) - (k' + 1)) * (9 * u) := by
          have h1 : N - (k' + 2) = (N - 1) - (k' + 1) := by omega
          rw [h1]
          have h2 : k' + 2 = (k' + 1) + 1 := rfl
          rw [h2, pow_succ]
          ring
        rw [hEq]
        exact hbeq

public theorem mirror_conservation_94 {N : ℕ} (hN : 1 ≤ N) {k : ℕ} (hk : k ≤ N)
    (g0 : ℕ) (hg0 : g0 < 4 ^ N) (gk : ℕ) (hiter : iter94 k g0 = some gk) :
    ∃ gm : ℕ, iter94 k (4 ^ N - 1 - g0) = some gm ∧
      gk + gm = 9 ^ k * 4 ^ (N - k) - 1 := by
  have hb : g0 ≤ 4 ^ N - 1 := by omega
  have hsum : g0 + (4 ^ N - 1 - g0) = 4 ^ N * 1 - 1 := by
    rw [mul_one, Nat.add_comm, Nat.sub_add_cancel hb]
  obtain ⟨b, hb1, hb2⟩ :=
    pair_iter k N 1 hN (by norm_num) hk g0 (4 ^ N - 1 - g0) hsum gk hiter
  exact ⟨b, hb1, by simpa using hb2⟩

/-! ### Iteration algebra and survival helpers -/

public lemma iter94_add (k l g : ℕ) : iter94 (k + l) g = (iter94 k g).bind (iter94 l) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_add, iter94_succ, iter94_succ]
    cases hg : step94 g with
    | none => simp
    | some x => simp [ih x]

public lemma exists_iter_of_survives {k g : ℕ} (h : survives94 k g) :
    ∃ v, iter94 k g = some v := by
  unfold survives94 at h
  cases hk : iter94 k g with
  | none => rw [hk] at h; simp at h
  | some v => exact ⟨v, rfl⟩

public lemma survives94_le {k l g : ℕ} (hkl : k ≤ l) (h : survives94 l g) : survives94 k g := by
  obtain ⟨l', rfl⟩ : ∃ l', l = k + l' := ⟨l - k, by omega⟩
  unfold survives94 at h ⊢
  rw [iter94_add] at h
  cases hk : iter94 k g with
  | none => rw [hk] at h; simp at h
  | some _ => simp

public lemma survives_succ {k g : ℕ} (h : survives94 (k + 1) g) :
    ∃ v, step94 g = some v ∧ survives94 k v := by
  unfold survives94 at h ⊢
  rw [iter94_succ] at h
  cases hg : step94 g with
  | none => rw [hg] at h; simp at h
  | some v =>
    refine ⟨v, rfl, ?_⟩
    rw [hg] at h
    simpa using h

public lemma step_of_survives {k g : ℕ} (h : survives94 (k + 1) g) :
    ∀ v, iter94 k g = some v → survives94 1 v := by
  intro v hv
  unfold survives94 at h ⊢
  rw [iter94_add k 1, hv] at h
  simpa using h

public lemma mod_of_survives_one {g : ℕ} (h : survives94 1 g) : g % 4 = 1 ∨ g % 4 = 2 := by
  obtain ⟨v, hstep, _⟩ := survives_succ (k := 0) (by simpa using h)
  have hlt : g % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h4 : g % 4 <;> simp [step94, h4] at hstep ⊢

public lemma nine_pow_even_mod4 (m : ℕ) : 9 ^ (2 * m) % 4 = 1 := by
  have h81 : 81 ^ m % 4 = 1 := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ, Nat.mul_mod, ih]
  have h92 : 9 ^ (2 * m) = 81 ^ m := by rw [pow_mul 9 2 m]; norm_num
  rw [h92, h81]

public lemma nine_pow_odd_mod16 (m : ℕ) : 9 ^ (2 * m + 1) % 16 = 9 := by
  have h81 : 81 ^ m % 16 = 1 := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ, Nat.mul_mod, ih]
  have h92 : 9 ^ (2 * m) = 81 ^ m := by rw [pow_mul 9 2 m]; norm_num
  have hsplit : 9 ^ (2 * m + 1) = 81 ^ m * 9 := by rw [pow_succ, h92]
  rw [hsplit, Nat.mul_mod, h81]

public lemma div_four_sub_five_mod {X : ℕ} (hX : X % 16 = 9) : (X - 5) / 4 % 4 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, X = 16 * k + 9 := ⟨X / 16, by have := Nat.div_add_mod X 16; omega⟩
  rw [hk]
  have he : 16 * k + 9 - 5 = 4 * (4 * k + 1) := by omega
  rw [he, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

/-! ### Theorem 2: even-rung mirror annihilation -/

public theorem even_rung_mirror_annihilation {m : ℕ} (hm : 1 ≤ m) (g0 : ℕ)
    (hg0 : g0 < 4 ^ (2 * m)) :
    ¬ (survives94 (2 * m + 2) g0 ∧ survives94 (2 * m + 2) (4 ^ (2 * m) - 1 - g0)) := by
  rintro ⟨h1, h2⟩
  have hN : 1 ≤ 2 * m := by omega
  obtain ⟨gN, hgN⟩ := exists_iter_of_survives (k := 2 * m) (survives94_le (by omega) h1)
  obtain ⟨gmN, hgmN⟩ := exists_iter_of_survives (k := 2 * m) (survives94_le (by omega) h2)
  obtain ⟨gm, hgm, hsum⟩ := mirror_conservation_94 hN (le_refl (2 * m)) g0 hg0 gN hgN
  have hgm_eq : gm = gmN := by rw [hgm] at hgmN; exact Option.some.inj hgmN
  have hsums : gN + gmN = 9 ^ (2 * m) - 1 := by rw [← hgm_eq]; simpa using hsum
  have hbig : 5 ≤ 9 ^ (2 * m) := by
    have h2 : 2 ≤ 2 * m := by omega
    have h : 9 ^ 2 ≤ 9 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) h2
    have : 9 ^ 2 = 81 := by norm_num
    omega
  have hs1 : survives94 2 gN := by
    unfold survives94 at h1 ⊢
    rw [iter94_add (2 * m) 2, hgN] at h1
    simpa using h1
  have hs2 : survives94 2 gmN := by
    unfold survives94 at h2 ⊢
    rw [iter94_add (2 * m) 2, hgmN] at h2
    simpa using h2
  obtain ⟨gN1, hstepN, hsurvN1⟩ := survives_succ (k := 1) (by simpa using hs1)
  obtain ⟨gmN1, hstepm, hsurvm1⟩ := survives_succ (k := 1) (by simpa using hs2)
  have hresN : gN % 4 = 1 ∨ gN % 4 = 2 := step94_isSome.mp (by rw [hstepN]; rfl)
  have hresm : gmN % 4 = 1 ∨ gmN % 4 = 2 := step94_isSome.mp (by rw [hstepm]; rfl)
  have hresN1 : gN1 % 4 = 1 ∨ gN1 % 4 = 2 := mod_of_survives_one hsurvN1
  have hresm1 : gmN1 % 4 = 1 ∨ gmN1 % 4 = 2 := mod_of_survives_one hsurvm1
  have hsummod : (gN + gmN) % 4 = 0 := by
    rw [hsums]
    have h9 := nine_pow_even_mod4 m
    have hpos : 0 < 9 ^ (2 * m) := by positivity
    omega
  have hgN2 : gN % 4 = 2 := by
    have hkey : (gN + gmN) % 4 = (gN % 4 + gmN % 4) % 4 := Nat.add_mod _ _ _
    rw [hsummod] at hkey
    rcases hresN with h|h <;> rcases hresm with h'|h' <;> rw [h, h'] at hkey <;> omega
  have hgmN2 : gmN % 4 = 2 := by
    have hkey : (gN + gmN) % 4 = (gN % 4 + gmN % 4) % 4 := Nat.add_mod _ _ _
    rw [hsummod] at hkey
    rcases hresN with h|h <;> rcases hresm with h'|h' <;> rw [h, h'] at hkey <;> omega
  have hN1 : gN1 = 9 * (gN / 4) + 5 := by
    have e := step94_of_mod_two hgN2
    rw [e] at hstepN
    have hval : (9 * gN + 2) / 4 = gN1 := Option.some.inj hstepN
    rw [← hval, div_four_mod_two hgN2]
  have hmN1 : gmN1 = 9 * (gmN / 4) + 5 := by
    have e := step94_of_mod_two hgmN2
    rw [e] at hstepm
    have hval : (9 * gmN + 2) / 4 = gmN1 := Option.some.inj hstepm
    rw [← hval, div_four_mod_two hgmN2]
  have hstep4 : 4 * (gN1 + gmN1) = 9 ^ (2 * m + 1) - 5 := by
    have hgNd : gN = 4 * (gN / 4) + 2 := by have := Nat.div_add_mod gN 4; omega
    have hgmNd : gmN = 4 * (gmN / 4) + 2 := by have := Nat.div_add_mod gmN 4; omega
    rw [hN1, hmN1]
    have hp : 9 ^ (2 * m + 1) = 9 * 9 ^ (2 * m) := by rw [pow_succ']
    rw [hp]
    omega
  have hSmod : (gN1 + gmN1) % 4 = 1 := by
    have hX := nine_pow_odd_mod16 m
    have hdiv : (9 ^ (2 * m + 1) - 5) / 4 = gN1 + gmN1 := by
      rw [← hstep4]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [← hdiv]
    exact div_four_sub_five_mod hX
  have hkey : (gN1 + gmN1) % 4 = (gN1 % 4 + gmN1 % 4) % 4 := Nat.add_mod _ _ _
  rw [hSmod] at hkey
  rcases hresN1 with h|h <;> rcases hresm1 with h'|h' <;> rw [h, h'] at hkey <;> omega

/-! ### Theorem 3: the generalized forbidden-sum law -/

public lemma nine_pow_mod4 (k : ℕ) : 9 ^ k % 4 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

public lemma c_nine_pow_sub_one_mod4 {c k : ℕ} (hc : c % 4 = 2) : (c * 9 ^ k - 1) % 4 = 1 := by
  have h9 : 9 ^ k % 4 = 1 := nine_pow_mod4 k
  have hmul : c * 9 ^ k % 4 = 2 := by
    rw [Nat.mul_mod, hc, h9]
  have hcpos : 0 < c := by omega
  have h9pos : 0 < 9 ^ k := by positivity
  have hpos : 0 < c * 9 ^ k := Nat.mul_pos hcpos h9pos
  omega

public theorem forbidden_sum_c2_mod4 {c : ℕ} (hc : c % 4 = 2) :
    ∀ k g0 g1 : ℕ, g0 + g1 = c * 4 ^ k - 1 →
      ¬ (survives94 (k + 1) g0 ∧ survives94 (k + 1) g1) := by
  intro k g0 g1 hsum
  rintro ⟨h1, h2⟩
  have hcpos : 1 ≤ c := by omega
  cases k with
  | zero =>
    have r1 : g0 % 4 = 1 ∨ g0 % 4 = 2 := mod_of_survives_one h1
    have r2 : g1 % 4 = 1 ∨ g1 % 4 = 2 := mod_of_survives_one h2
    have hmod : (g0 + g1) % 4 = 1 := by
      rw [hsum]
      have h0 : c * 4 ^ 0 - 1 = c - 1 := by norm_num
      rw [h0]
      omega
    have hkey : (g0 + g1) % 4 = (g0 % 4 + g1 % 4) % 4 := Nat.add_mod _ _ _
    rw [hmod] at hkey
    rcases r1 with h|h <;> rcases r2 with h'|h' <;> rw [h, h'] at hkey <;> omega
  | succ k' =>
    have hk1 : survives94 (k' + 1) g0 := survives94_le (by omega) h1
    have hk2 : survives94 (k' + 1) g1 := survives94_le (by omega) h2
    obtain ⟨a, ha⟩ := exists_iter_of_survives hk1
    obtain ⟨b, hb⟩ := exists_iter_of_survives hk2
    have hsum' : g0 + g1 = 4 ^ (k' + 1) * c - 1 := by rw [hsum, Nat.mul_comm]
    obtain ⟨bb, hbb, hbeq⟩ :=
      pair_iter (k' + 1) (k' + 1) c (by omega) hcpos (le_refl _) g0 g1 hsum' a ha
    have hbb_eq : bb = b := by rw [hbb] at hb; exact Option.some.inj hb
    have hsumk : a + b = c * 9 ^ (k' + 1) - 1 := by
      have : a + b = 9 ^ (k' + 1) * c - 1 := by rw [← hbb_eq]; simpa using hbeq
      rw [this, Nat.mul_comm]
    have r1 : a % 4 = 1 ∨ a % 4 = 2 := mod_of_survives_one (step_of_survives h1 a ha)
    have r2 : b % 4 = 1 ∨ b % 4 = 2 := mod_of_survives_one (step_of_survives h2 b hb)
    have hmodk : (a + b) % 4 = 1 := by
      rw [hsumk]
      exact c_nine_pow_sub_one_mod4 hc
    have hkey : (a + b) % 4 = (a % 4 + b % 4) % 4 := Nat.add_mod _ _ _
    rw [hmodk] at hkey
    rcases r1 with h|h <;> rcases r2 with h'|h' <;> rw [h, h'] at hkey <;> omega

/-! ### Theorem 5: independent shadow dynamics for the sum -/

@[expose] public def stepSum (s : ℕ) : Option ℕ :=
  match s % 4 with
  | 0 => some ((9 * s + 4) / 4)
  | 2 => some ((9 * s + 6) / 4)
  | 3 => some ((9 * s + 5) / 4)
  | _ => none

@[expose] public def iterSum : ℕ → ℕ → Option ℕ
  | 0, s => some s
  | k + 1, s => (stepSum s).bind (iterSum k)

@[simp] public lemma iterSum_zero (s : ℕ) : iterSum 0 s = some s := rfl

public lemma iterSum_succ (k s : ℕ) : iterSum (k + 1) s = (stepSum s).bind (iterSum k) := rfl

public lemma stepSum_of_mod_zero {s : ℕ} (h : s % 4 = 0) : stepSum s = some ((9 * s + 4) / 4) := by
  simp [stepSum, h]

public lemma stepSum_of_mod_two {s : ℕ} (h : s % 4 = 2) : stepSum s = some ((9 * s + 6) / 4) := by
  simp [stepSum, h]

public lemma stepSum_of_mod_three {s : ℕ} (h : s % 4 = 3) : stepSum s = some ((9 * s + 5) / 4) := by
  simp [stepSum, h]

/-- Pair step for the sum shadow: two viable numbers send their sum by `stepSum`. -/
public lemma step_sum_pair {g0 g1 h h1 : ℕ} (hs0 : step94 g0 = some h) (hs1 : step94 g1 = some h1) :
    stepSum (g0 + g1) = some (h + h1) := by
  have hsome0 : (step94 g0).isSome := by rw [hs0]; rfl
  have hsome1 : (step94 g1).isSome := by rw [hs1]; rfl
  rcases step94_isSome.mp hsome0 with hg0 | hg0 <;> rcases step94_isSome.mp hsome1 with hg1 | hg1
  · have hh : h = 9 * (g0 / 4) + 3 := by
      rw [step94_of_mod_one hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_one hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 3 := by
      rw [step94_of_mod_one hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_one hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 1 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 1 := by have := Nat.div_add_mod g1 4; omega
    have hsmod : (g0 + g1) % 4 = 2 := by
      have hkey : (g0 + g1) % 4 = (g0 % 4 + g1 % 4) % 4 := Nat.add_mod _ _ _
      rw [hg0, hg1] at hkey; omega
    rw [stepSum_of_mod_two hsmod]
    have hEq : 9 * (g0 + g1) + 6 = 4 * (h + h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]
  · have hh : h = 9 * (g0 / 4) + 3 := by
      rw [step94_of_mod_one hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_one hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 5 := by
      rw [step94_of_mod_two hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_two hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 1 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 2 := by have := Nat.div_add_mod g1 4; omega
    have hsmod : (g0 + g1) % 4 = 3 := by
      have hkey : (g0 + g1) % 4 = (g0 % 4 + g1 % 4) % 4 := Nat.add_mod _ _ _
      rw [hg0, hg1] at hkey; omega
    rw [stepSum_of_mod_three hsmod]
    have hEq : 9 * (g0 + g1) + 5 = 4 * (h + h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]
  · have hh : h = 9 * (g0 / 4) + 5 := by
      rw [step94_of_mod_two hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_two hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 3 := by
      rw [step94_of_mod_one hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_one hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 2 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 1 := by have := Nat.div_add_mod g1 4; omega
    have hsmod : (g0 + g1) % 4 = 3 := by
      have hkey : (g0 + g1) % 4 = (g0 % 4 + g1 % 4) % 4 := Nat.add_mod _ _ _
      rw [hg0, hg1] at hkey; omega
    rw [stepSum_of_mod_three hsmod]
    have hEq : 9 * (g0 + g1) + 5 = 4 * (h + h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]
  · have hh : h = 9 * (g0 / 4) + 5 := by
      rw [step94_of_mod_two hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_two hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 5 := by
      rw [step94_of_mod_two hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_two hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 2 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 2 := by have := Nat.div_add_mod g1 4; omega
    have hsmod : (g0 + g1) % 4 = 0 := by
      have hkey : (g0 + g1) % 4 = (g0 % 4 + g1 % 4) % 4 := Nat.add_mod _ _ _
      rw [hg0, hg1] at hkey; omega
    rw [stepSum_of_mod_zero hsmod]
    have hEq : 9 * (g0 + g1) + 4 = 4 * (h + h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **Theorem 5 (sum half).** The sum map reproduces the pair sum exactly. -/
public theorem sum_shadow_exact (k : ℕ) :
    ∀ g0 g1 gk gk1 : ℕ, iter94 k g0 = some gk → iter94 k g1 = some gk1 →
      iterSum k (g0 + g1) = some (gk + gk1) := by
  induction k with
  | zero =>
    intro g0 g1 gk gk1 h0 h1
    simp only [iter94_zero, Option.some.injEq] at h0 h1
    subst h0; subst h1
    simp
  | succ k ih =>
    intro g0 g1 gk gk1 h0 h1
    rw [iter94_succ] at h0 h1
    obtain ⟨h, hs0, hr0⟩ := Option.bind_eq_some_iff.mp h0
    obtain ⟨h1', hs1, hr1⟩ := Option.bind_eq_some_iff.mp h1
    have hstep := step_sum_pair hs0 hs1
    have hrec := ih h h1' gk gk1 hr0 hr1
    rw [iterSum_succ, hstep]
    simpa using hrec

/-! ### Theorem 5: independent shadow dynamics for the difference -/

@[expose] public def stepDiff (d : ℕ) : Option ℕ :=
  match d % 4 with
  | 0 => some (9 * d / 4)
  | 1 => some ((9 * d - 1) / 4)
  | 3 => some ((9 * d + 1) / 4)
  | _ => none

@[expose] public def iterDiff : ℕ → ℕ → Option ℕ
  | 0, d => some d
  | k + 1, d => (stepDiff d).bind (iterDiff k)

@[simp] public lemma iterDiff_zero (d : ℕ) : iterDiff 0 d = some d := rfl

public lemma iterDiff_succ (k d : ℕ) : iterDiff (k + 1) d = (stepDiff d).bind (iterDiff k) := rfl

public lemma stepDiff_of_mod_zero {d : ℕ} (h : d % 4 = 0) : stepDiff d = some (9 * d / 4) := by
  simp [stepDiff, h]

public lemma stepDiff_of_mod_one {d : ℕ} (h : d % 4 = 1) : stepDiff d = some ((9 * d - 1) / 4) := by
  simp [stepDiff, h]

public lemma stepDiff_of_mod_three {d : ℕ} (h : d % 4 = 3) : stepDiff d = some ((9 * d + 1) / 4) := by
  simp [stepDiff, h]

/-- Pair step for the difference shadow: two viable ordered numbers send their difference by
`stepDiff`, and the order is preserved. -/
public lemma step_diff_pair {g0 g1 h h1 : ℕ} (hle : g1 ≤ g0)
    (hs0 : step94 g0 = some h) (hs1 : step94 g1 = some h1) :
    h1 ≤ h ∧ stepDiff (g0 - g1) = some (h - h1) := by
  have hsome0 : (step94 g0).isSome := by rw [hs0]; rfl
  have hsome1 : (step94 g1).isSome := by rw [hs1]; rfl
  rcases step94_isSome.mp hsome0 with hg0 | hg0 <;> rcases step94_isSome.mp hsome1 with hg1 | hg1
  · have hh : h = 9 * (g0 / 4) + 3 := by
      rw [step94_of_mod_one hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_one hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 3 := by
      rw [step94_of_mod_one hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_one hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 1 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 1 := by have := Nat.div_add_mod g1 4; omega
    have hle_h : h1 ≤ h := by rw [hh, hh1]; omega
    refine ⟨hle_h, ?_⟩
    have hdmod : (g0 - g1) % 4 = 0 := by omega
    rw [stepDiff_of_mod_zero hdmod]
    have hEq : 9 * (g0 - g1) = 4 * (h - h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]
  · have hh : h = 9 * (g0 / 4) + 3 := by
      rw [step94_of_mod_one hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_one hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 5 := by
      rw [step94_of_mod_two hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_two hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 1 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 2 := by have := Nat.div_add_mod g1 4; omega
    have hq : g1 / 4 < g0 / 4 := by omega
    have hle_h : h1 ≤ h := by rw [hh, hh1]; omega
    refine ⟨hle_h, ?_⟩
    have hdmod : (g0 - g1) % 4 = 3 := by omega
    rw [stepDiff_of_mod_three hdmod]
    have hEq : 9 * (g0 - g1) + 1 = 4 * (h - h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]
  · have hh : h = 9 * (g0 / 4) + 5 := by
      rw [step94_of_mod_two hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_two hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 3 := by
      rw [step94_of_mod_one hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_one hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 2 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 1 := by have := Nat.div_add_mod g1 4; omega
    have hle_h : h1 ≤ h := by rw [hh, hh1]; omega
    refine ⟨hle_h, ?_⟩
    have hdmod : (g0 - g1) % 4 = 1 := by omega
    rw [stepDiff_of_mod_one hdmod]
    have hEq : 9 * (g0 - g1) - 1 = 4 * (h - h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]
  · have hh : h = 9 * (g0 / 4) + 5 := by
      rw [step94_of_mod_two hg0] at hs0
      rw [← Option.some.inj hs0, div_four_mod_two hg0]
    have hh1 : h1 = 9 * (g1 / 4) + 5 := by
      rw [step94_of_mod_two hg1] at hs1
      rw [← Option.some.inj hs1, div_four_mod_two hg1]
    have hg0d : g0 = 4 * (g0 / 4) + 2 := by have := Nat.div_add_mod g0 4; omega
    have hg1d : g1 = 4 * (g1 / 4) + 2 := by have := Nat.div_add_mod g1 4; omega
    have hle_h : h1 ≤ h := by rw [hh, hh1]; omega
    refine ⟨hle_h, ?_⟩
    have hdmod : (g0 - g1) % 4 = 0 := by omega
    rw [stepDiff_of_mod_zero hdmod]
    have hEq : 9 * (g0 - g1) = 4 * (h - h1) := by rw [hh, hh1]; omega
    rw [hEq, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **Theorem 5 (difference half).** The difference map reproduces the ordered pair's difference
exactly, and preserves the order. -/
public theorem diff_shadow_exact (k : ℕ) :
    ∀ g0 g1 gk gk1 : ℕ, g1 ≤ g0 → iter94 k g0 = some gk → iter94 k g1 = some gk1 →
      gk1 ≤ gk ∧ iterDiff k (g0 - g1) = some (gk - gk1) := by
  induction k with
  | zero =>
    intro g0 g1 gk gk1 hle h0 h1
    simp only [iter94_zero, Option.some.injEq] at h0 h1
    subst h0; subst h1
    exact ⟨hle, by simp⟩
  | succ k ih =>
    intro g0 g1 gk gk1 hle h0 h1
    rw [iter94_succ] at h0 h1
    obtain ⟨h, hs0, hr0⟩ := Option.bind_eq_some_iff.mp h0
    obtain ⟨h1', hs1, hr1⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨hle', hstep⟩ := step_diff_pair hle hs0 hs1
    obtain ⟨hle'', hrec⟩ := ih h h1' gk gk1 hle' hr0 hr1
    refine ⟨hle'', ?_⟩
    rw [iterDiff_succ, hstep]
    simpa using hrec



/-- Small-modulus finite-roof certificate: in the `4^4 = 256` window, at most `3/8` of the
`N = 4` survivors survive two further steps.  This is the `decide`-checked Lean instance; the
larger moduli `4^6, 4^7, 4^9` are reproduced by `scripts/generate_certificates.py`. -/
public theorem finite_roof_block_certificate :
    8 * ((Finset.range (4 ^ 4)).filter (fun g => survives94 (4 + 2) g)).card
      ≤ 3 * ((Finset.range (4 ^ 4)).filter (fun g => survives94 4 g)).card := by
  decide

/-! ### General-`N` lifting: survival to `k` steps has period `4^k` -/

/-- One step of the `9/4` map commutes with adding `4^(k+1) · t`, up to the exact shift
`9 · 4^k · t`.  This is the finite-window lifting engine: it shows that survival to any fixed
horizon is determined by the low base-`4` digits. -/
public lemma step94_add_four_pow (k t g : ℕ) :
    step94 (g + 4 ^ (k + 1) * t) = (step94 g).map (fun h => h + 9 * 4 ^ k * t) := by
  have h4 : 4 ^ (k + 1) * t = 4 * (4 ^ k * t) := by rw [pow_succ]; ring
  have hmod : (g + 4 ^ (k + 1) * t) % 4 = g % 4 := by
    rw [h4, Nat.add_mul_mod_self_left]
  have hlt : g % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : g % 4
  · simp [step94, hm, hmod]
  · rw [step94_of_mod_one hm, step94_of_mod_one (by simpa using hmod)]
    congr 1
    have hsplit : 9 * (g + 4 ^ (k + 1) * t) + 3
        = (9 * g + 3) + 4 * (9 * 4 ^ k * t) := by rw [pow_succ]; ring
    rw [hsplit, Nat.add_mul_div_left _ _ (by norm_num)]
  · rw [step94_of_mod_two hm, step94_of_mod_two (by simpa using hmod)]
    congr 1
    have hsplit : 9 * (g + 4 ^ (k + 1) * t) + 2
        = (9 * g + 2) + 4 * (9 * 4 ^ k * t) := by rw [pow_succ]; ring
    rw [hsplit, Nat.add_mul_div_left _ _ (by norm_num)]
  · simp [step94, hm, hmod]

/-- Iterating `k` steps: survival/iteration of `g + 4^k · t` is the iteration of `g` shifted by
`9^k · t`. -/
public lemma iter94_add_four_pow (k t g : ℕ) :
    iter94 k (g + 4 ^ k * t) = (iter94 k g).map (fun h => h + 9 ^ k * t) := by
  induction k generalizing g t with
  | zero => simp
  | succ k ih =>
    rw [iter94_succ, iter94_succ, step94_add_four_pow]
    cases step94 g with
    | none => simp
    | some h =>
      simp only [Option.map_some, Option.bind_some]
      have hrw : h + 9 * 4 ^ k * t = h + 4 ^ k * (9 * t) := by ring
      rw [hrw, ih (9 * t) h]
      have hf : (fun x => x + 9 ^ k * (9 * t)) = (fun x => x + 9 ^ (k + 1) * t) := by
        funext x; rw [pow_succ]; ring
      rw [hf]

/-- **Finite-window lifting.**  Survival to `k` steps is invariant under adding a multiple of
`4^k`, so the finite window `[0, 4^k)` exhausts every survival pattern; in particular every
"finite window" count at horizon `k` is exactly the count at horizon `k` in any larger window. -/
public theorem survives94_add_four_pow (k t g : ℕ) :
    survives94 k (g + 4 ^ k * t) ↔ survives94 k g := by
  unfold survives94
  rw [iter94_add_four_pow]
  cases iter94 k g with
  | none => simp
  | some h => simp

/-! ### Theorem 4, general odd `N`: at most three of each Klein-4 quadruple survive -/

/-- For odd `N = 2m+1`, `(9^N - 1)/4 ≡ 2 (mod 4)`. -/
public lemma nine_pow_odd_sub_one_div_four_mod (m : ℕ) :
    (9 ^ (2 * m + 1) - 1) / 4 % 4 = 2 := by
  have hX : 9 ^ (2 * m + 1) % 16 = 9 := nine_pow_odd_mod16 m
  have hXeq : 9 ^ (2 * m + 1) = 16 * (9 ^ (2 * m + 1) / 16) + 9 := by
    have := Nat.div_add_mod (9 ^ (2 * m + 1)) 16
    rw [hX] at this
    omega
  rw [hXeq]
  have hsimp : 16 * (9 ^ (2 * m + 1) / 16) + 9 - 1
      = 4 * (4 * (9 ^ (2 * m + 1) / 16) + 2) := by omega
  rw [hsimp, Nat.mul_div_right _ (by norm_num)]
  omega

/-- For odd `N = 2m+1`, `(3·9^N + 1)/4 ≡ 3 (mod 4)`. -/
public lemma three_nine_pow_odd_add_one_div_four_mod (m : ℕ) :
    (3 * 9 ^ (2 * m + 1) + 1) / 4 % 4 = 3 := by
  have hX : 9 ^ (2 * m + 1) % 16 = 9 := nine_pow_odd_mod16 m
  have hXeq : 9 ^ (2 * m + 1) = 16 * (9 ^ (2 * m + 1) / 16) + 9 := by
    have := Nat.div_add_mod (9 ^ (2 * m + 1)) 16
    rw [hX] at this
    omega
  rw [hXeq]
  have hsimp : 3 * (16 * (9 ^ (2 * m + 1) / 16) + 9) + 1
      = 4 * (12 * (9 ^ (2 * m + 1) / 16) + 7) := by ring
  rw [hsimp, Nat.mul_div_right _ (by norm_num)]
  omega

/-- Two residues in `{1,2}` whose sum is `≡ 0 (mod 4)` must both be `2`. -/
public lemma both_residues_two {a b : ℕ}
    (ha : a % 4 = 1 ∨ a % 4 = 2) (hb : b % 4 = 1 ∨ b % 4 = 2)
    (h : (a + b) % 4 = 0) : a % 4 = 2 ∧ b % 4 = 2 := by
  have hkey : (a + b) % 4 = (a % 4 + b % 4) % 4 := Nat.add_mod _ _ _
  rw [h] at hkey
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb] at hkey; omega
  · rw [ha, hb] at hkey; omega
  · rw [ha, hb] at hkey; omega
  · exact ⟨ha, hb⟩

/-- Iterating the difference shadow on `r · 4^m` gives `r · 9^m`. -/
public lemma iterDiff_mul_four_pow (r m : ℕ) :
    iterDiff m (r * 4 ^ m) = some (r * 9 ^ m) := by
  induction m generalizing r with
  | zero => simp
  | succ m ih =>
    rw [iterDiff_succ]
    have hm : (r * 4 ^ (m + 1)) % 4 = 0 := by
      have h4 : r * 4 ^ (m + 1) = 4 * (r * 4 ^ m) := by rw [pow_succ]; ring
      rw [h4, Nat.mul_mod_right]
    rw [stepDiff_of_mod_zero hm]
    have hval : 9 * (r * 4 ^ (m + 1)) / 4 = (9 * r) * 4 ^ m := by
      have h4 : 9 * (r * 4 ^ (m + 1)) = 4 * ((9 * r) * 4 ^ m) := by rw [pow_succ]; ring
      rw [h4, Nat.mul_div_right _ (by norm_num)]
    rw [hval, Option.bind_some, ih (9 * r)]
    congr 1
    rw [pow_succ]; ring

/-- **Theorem 4 (general odd `N`).**  For every odd `N ≥ 3`, `g < 4^{N-1}` and `δ ∈ {1,2,3}`, it is
impossible that all four of `g`, `g + δ·4^{N-1}`, `4^N - 1 - g`, `4^N - 1 - (g + δ·4^{N-1})`
survive `N + 1` steps.  This is the uniform-in-`N` Klein-4 exclusion (the `N = 3` kernel instance
is `odd_rung_klein4_exclusion`); it upgrades the previous `decide`-only statement. -/
public theorem odd_rung_klein4_no_four {N g δ : ℕ}
    (hN : 3 ≤ N) (hodd : N % 2 = 1) (hg : g < 4 ^ (N - 1))
    (hδ1 : 1 ≤ δ) (hδ3 : δ ≤ 3) :
    ¬ (survives94 (N + 1) g ∧ survives94 (N + 1) (g + δ * 4 ^ (N - 1)) ∧
       survives94 (N + 1) (4 ^ N - 1 - g) ∧
       survives94 (N + 1) (4 ^ N - 1 - (g + δ * 4 ^ (N - 1)))) := by
  intro h
  obtain ⟨hA, hB, hAb, hBb⟩ := h
  have hN1 : 1 ≤ N := by omega
  -- size bounds
  have hApow : 4 ^ (N - 1) ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA_lt : g < 4 ^ N := lt_of_lt_of_le hg hApow
  have hB_lt : g + δ * 4 ^ (N - 1) < 4 ^ N := by
    have hX : 0 < 4 ^ (N - 1) := Nat.pow_pos (by norm_num)
    have hle : δ * 4 ^ (N - 1) ≤ 3 * 4 ^ (N - 1) := Nat.mul_le_mul_right _ hδ3
    have hp : 4 ^ N = 4 * 4 ^ (N - 1) := by
      have h : N = (N - 1) + 1 := by omega
      conv_lhs => rw [h]
      rw [pow_succ]
      exact Nat.mul_comm _ _
    nlinarith [hg, hle, hp, hX]
  -- iterates at time `N` and `N-1`
  have hNle : N ≤ N + 1 := by omega
  obtain ⟨aN, haN⟩ := exists_iter_of_survives (survives94_le hNle hA)
  obtain ⟨bN, hbN⟩ := exists_iter_of_survives (survives94_le hNle hB)
  have hNm : N = (N - 1) + 1 := by omega
  have haN' : iter94 N g = some aN := haN
  have hbN' : iter94 N (g + δ * 4 ^ (N - 1)) = some bN := hbN
  rw [hNm, iter94_add (N - 1) 1] at haN' hbN'
  obtain ⟨A', hA', hstepA⟩ := Option.bind_eq_some_iff.mp haN'
  obtain ⟨B', hB', hstepB⟩ := Option.bind_eq_some_iff.mp hbN'
  have hstepA' : step94 A' = some aN := by simpa [iter94] using hstepA
  have hstepB' : step94 B' = some bN := by simpa [iter94] using hstepB
  -- difference shadow: `B' - A' = δ 9^{N-1}`
  have hgB : g ≤ g + δ * 4 ^ (N - 1) := Nat.le_add_right _ _
  obtain ⟨hA'leB', hdiff⟩ :=
    diff_shadow_exact (N - 1) (g + δ * 4 ^ (N - 1)) g B' A' hgB hB' hA'
  rw [Nat.add_sub_cancel_left] at hdiff
  rw [iterDiff_mul_four_pow δ (N - 1)] at hdiff
  have hB'A' : B' - A' = δ * 9 ^ (N - 1) := (Option.some.inj hdiff).symm
  obtain ⟨haNbN, hsd⟩ := step_diff_pair hA'leB' hstepB' hstepA'
  rw [hB'A'] at hsd
  -- mirror sums at level `N`
  obtain ⟨am, ham, hsumA⟩ :=
    mirror_conservation_94 hN1 (le_refl N) g hA_lt aN haN
  obtain ⟨bm, hbm, hsumB⟩ :=
    mirror_conservation_94 hN1 (le_refl N) (g + δ * 4 ^ (N - 1)) hB_lt bN hbN
  obtain ⟨abar, habar⟩ := exists_iter_of_survives (survives94_le hNle hAb)
  obtain ⟨bbar, hbbar⟩ := exists_iter_of_survives (survives94_le hNle hBb)
  have ham_eq : am = abar := by rw [ham] at habar; exact Option.some.inj habar
  have hbm_eq : bm = bbar := by rw [hbm] at hbbar; exact Option.some.inj hbbar
  have h9 : 9 ^ N % 4 = 1 := nine_pow_mod4 N
  have hsumA'' : aN + abar = 9 ^ N - 1 := by
    have := hsumA
    rw [ham_eq] at this
    have h0 : 4 ^ (N - N) = 1 := by rw [Nat.sub_self]; norm_num
    rw [h0, mul_one] at this
    exact this
  have hsumB'' : bN + bbar = 9 ^ N - 1 := by
    have := hsumB
    rw [hbm_eq] at this
    have h0 : 4 ^ (N - N) = 1 := by rw [Nat.sub_self]; norm_num
    rw [h0, mul_one] at this
    exact this
  have hsumAmod : (aN + abar) % 4 = 0 := by
    rw [hsumA'']
    obtain ⟨q, hq⟩ : ∃ q, 9 ^ N = 4 * q + 1 := by
      refine ⟨9 ^ N / 4, ?_⟩
      have := Nat.div_add_mod (9 ^ N) 4
      rw [h9] at this
      omega
    rw [hq]
    have : 4 * q + 1 - 1 = 4 * q := by omega
    rw [this, Nat.mul_mod_right]
  have hsumBmod : (bN + bbar) % 4 = 0 := by
    rw [hsumB'']
    obtain ⟨q, hq⟩ : ∃ q, 9 ^ N = 4 * q + 1 := by
      refine ⟨9 ^ N / 4, ?_⟩
      have := Nat.div_add_mod (9 ^ N) 4
      rw [h9] at this
      omega
    rw [hq]
    have : 4 * q + 1 - 1 = 4 * q := by omega
    rw [this, Nat.mul_mod_right]
  obtain ⟨ha2, _⟩ :=
    both_residues_two (mod_of_survives_one (step_of_survives hA aN haN))
      (mod_of_survives_one (step_of_survives hAb abar habar)) hsumAmod
  obtain ⟨hb2, _⟩ :=
    both_residues_two (mod_of_survives_one (step_of_survives hB bN hbN))
      (mod_of_survives_one (step_of_survives hBb bbar hbbar)) hsumBmod
  have hres : (bN - aN) % 4 = 0 := by omega
  -- `N` odd: `N = 2 * (N/2) + 1`
  have hNsplit : N = 2 * (N / 2) + 1 := by
    have := Nat.div_add_mod N 2
    rw [hodd] at this
    omega
  have hdmod : (δ * 9 ^ (N - 1)) % 4 = δ := by
    have h9e : 9 ^ (N - 1) % 4 = 1 := nine_pow_mod4 (N - 1)
    obtain ⟨c, hc⟩ : ∃ c, 9 ^ (N - 1) = 4 * c + 1 := by
      refine ⟨9 ^ (N - 1) / 4, ?_⟩
      have := Nat.div_add_mod (9 ^ (N - 1)) 4
      rw [h9e] at this
      omega
    rw [hc]
    have hmul : δ * (4 * c + 1) = δ + 4 * (δ * c) := by ring
    rw [hmul, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have h9N : 9 * 9 ^ (N - 1) = 9 ^ N := by
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  interval_cases δ
  · -- δ = 1
    have hd1 : (1 * 9 ^ (N - 1)) % 4 = 1 := by simpa using hdmod
    rw [stepDiff_of_mod_one hd1] at hsd
    have heq : (9 * (1 * 9 ^ (N - 1)) - 1) / 4 = bN - aN := Option.some.inj hsd
    have hL : (9 * (1 * 9 ^ (N - 1)) - 1) / 4 % 4 = 2 := by
      have hp : 9 * (1 * 9 ^ (N - 1)) - 1 = 9 ^ N - 1 := by
        rw [one_mul]
        rw [h9N]
      rw [hp, hNsplit]
      exact nine_pow_odd_sub_one_div_four_mod (N / 2)
    rw [heq] at hL
    omega
  · -- δ = 2: difference residue `2` makes the shadow undefined
    have hd2 : (2 * 9 ^ (N - 1)) % 4 = 2 := by simpa using hdmod
    simp [stepDiff, hd2] at hsd
  · -- δ = 3
    have hd3 : (3 * 9 ^ (N - 1)) % 4 = 3 := by simpa using hdmod
    rw [stepDiff_of_mod_three hd3] at hsd
    have heq : (9 * (3 * 9 ^ (N - 1)) + 1) / 4 = bN - aN := Option.some.inj hsd
    have hL : (9 * (3 * 9 ^ (N - 1)) + 1) / 4 % 4 = 3 := by
      have hp : 9 * (3 * 9 ^ (N - 1)) + 1 = 3 * 9 ^ N + 1 := by
        have hm : 9 * (3 * 9 ^ (N - 1)) = 3 * 9 ^ N := by
          calc 9 * (3 * 9 ^ (N - 1)) = 3 * (9 * 9 ^ (N - 1)) := by ring
            _ = 3 * 9 ^ N := by rw [h9N]
        rw [hm]
      rw [hp, hNsplit]
      exact three_nine_pow_odd_add_one_div_four_mod (N / 2)
    rw [heq] at hL
    omega

/-! ### Theorem 6: carry-free base-9 conservation -/

/-- Left-to-right base-9 transducer over a digit word `digits` (most significant first):
with incoming remainder `r`, a digit `a` outputs `a' = (9r+a)/4` and updates `r' = (9r+a) % 4`.
Returns `(sum of outputs, sum of incoming remainders, final remainder)`. -/
@[expose] public def scan (r : ℕ) : List ℕ → ℕ × ℕ × ℕ
  | [] => (0, 0, r)
  | a :: rest =>
      let s := 9 * r + a
      let p := scan (s % 4) rest
      (s / 4 + p.1, r + p.2.1, p.2.2)

public lemma scan_cons (r a : ℕ) (rest : List ℕ) :
    scan r (a :: rest) = ((9 * r + a) / 4 + (scan ((9 * r + a) % 4) rest).1,
        r + (scan ((9 * r + a) % 4) rest).2.1, (scan ((9 * r + a) % 4) rest).2.2) := by
  simp only [scan]

/-- **Theorem 6 (per-position exactness).** Each position satisfies the carry-free identity
`4 a' + r' = 9 r + a` with no rounding. -/
public theorem base9_transducer_exact (r a : ℕ) :
    4 * ((9 * r + a) / 4) + (9 * r + a) % 4 = 9 * r + a :=
  Nat.div_add_mod _ _

/-- **Theorem 6 (global digit-sum conservation).** Over a whole word, the exact integer identity
`4 · (Σ output) = 8 · (Σ incoming remainder) + (Σ digit) + r₀ − r_final` holds; with `r₀ = 0` and a
carry-free end (`r_final = 0`) this reads `s₉(next) = s₉(digits)/4 + 2·Σ r`. -/
public theorem base9_digit_sum_conservation (r : ℕ) (L : List ℕ) :
    4 * (((scan r L).1 : ℕ) : ℤ)
      = 8 * (((scan r L).2.1 : ℕ) : ℤ) + ((L.sum : ℕ) : ℤ) + (r : ℤ)
          - (((scan r L).2.2 : ℕ) : ℤ) := by
  induction L generalizing r with
  | nil => simp [scan]
  | cons a rest ih =>
    set q := (9 * r + a) / 4 with hq
    set m := (9 * r + a) % 4 with hm
    set os := (scan m rest).1 with hos
    set rs := (scan m rest).2.1 with hrs
    set rf := (scan m rest).2.2 with hrf
    have hscan : scan r (a :: rest) = (q + os, r + rs, rf) := by
      rw [scan_cons, ← hm, ← hos, ← hrs, ← hrf, ← hq]
    rw [hscan]
    simp only [List.sum_cons]
    have hIH : 4 * (os : ℤ) = 8 * (rs : ℤ) + ((rest.sum : ℕ) : ℤ) + (m : ℤ) - (rf : ℤ) := by
      have := ih m
      rw [← hos, ← hrs, ← hrf] at this
      simpa using this
    have hstep : 4 * (q : ℤ) + (m : ℤ) = 9 * (r : ℤ) + (a : ℤ) := by
      rw [hq, hm]
      have h := Nat.div_add_mod (9 * r + a) 4
      have hc : ((4 * ((9 * r + a) / 4) + (9 * r + a) % 4 : ℕ) : ℤ) = (((9 * r + a : ℕ)) : ℤ) := by
        rw [h]
      push_cast at hc ⊢
      linarith
    simp only [Nat.cast_add]
    linarith [hIH, hstep]

/-! ### Theorem 4: odd-rung Klein-4 exclusion (kernel-checked instance) -/

/-- **Theorem 4 (kernel-checked instance, `N = 3`).** At the odd rung `N = 3` (`4^{N-1} = 16`,
`4^N = 64`), for every sibling pair `g`, `g + δ·16` (`δ ∈ {1,2,3}`) and their mirror twins
`63 - g`, `63 - (g + δ·16)`, at most `3` of the four survive `N + 1 = 4` steps.  This is the
small-modulus `decide` check; the general odd-`N` statement is reproduced by
`scripts/generate_certificates.py`. -/
public theorem odd_rung_klein4_exclusion :
    ((List.range 16).all (fun g =>
        ([1, 2, 3] : List ℕ).all (fun δ =>
          if g + δ * 16 < 64 then
            decide ((({g, g + δ * 16, 63 - g, 63 - (g + δ * 16)} : Finset ℕ).filter
              (fun x => survives94 4 x)).card ≤ 3)
          else true))) = true := by
  decide

end Mahler32.Model94Obstructions

end
