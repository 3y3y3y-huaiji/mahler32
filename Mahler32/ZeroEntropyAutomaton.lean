/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mahler32.RationalBaseDefs

/-!
# General Signed Rational Zero-Entropy Automaton & Exact Markov SCC Certificates

This module proves soundness of the pure definitions in `Mahler32.RationalBaseDefs`:
1. `hasBranchOverlap_sound`: every transition `StepPQ p q neg x y` (`x ∈ I, y ∈ J`) activates
   `hasBranchOverlap p q neg I J = true`.
2. `totalPaths_poly_bound` and `zero_entropy_of_no_branching_scc`: topologically ordered SCCs with
   at most one intra-component edge per vertex force polynomial walk growth and topological entropy
   zero (`∀ ε > 0, ∃ C > 0, totalPaths adj L ≤ C · (1 + ε)^L`).
3. Concrete finite-depth rational survivor partition certificates (checked in the Lean kernel by
   `decide`, zero `native_decide`; full survivor-partition provenance cross-checked in
   `scripts/generate_certificates.py --verify`):
   - `cert_neg_5_3`: `-5/3` centered `[89/250, 161/250)` (`0.2880`)
   - `cert_neg_3_2_holed`: `-3/2` holed `[147/1000, 43/100) ∪ [57/100, 853/1000)` (`0.5660 > 1/2`)
   - `cert_neg_3_2_centered`: `-3/2` centered `[1429/5000, 3571/5000)` (`0.4284`)
   - `cert_pos_5_3_centered`: `+5/3` centered `[697/2000, 1303/2000)` (`0.3030`)
-/

public section

open scoped BigOperators

namespace Mahler32.ZeroEntropyAutomaton

open Mahler32

private lemma ratInterval_lo_le_one_div (I : RatInterval) : I.lo < I.hi := by
  unfold RatInterval.lo RatInterval.hi
  have h1 : (0 : ℚ) < I.ld := by exact_mod_cast I.ldPos
  have h2 : (0 : ℚ) < I.hd := by exact_mod_cast I.hdPos
  rw [div_lt_div_iff₀ h1 h2]
  exact_mod_cast I.lt

private lemma hasOverlapBranch_of_rat {p q : ℕ} (hq : 1 ≤ q) (neg : Bool) (I J : RatInterval)
    (k : ℕ) (m : ℤ)
    (h1 : ((if neg then -(p : ℚ) * I.hi else (p : ℚ) * I.lo) + (k : ℚ)) / (q : ℚ) - (m : ℚ) <
      J.hi)
    (h2 : J.lo ≤
      ((if neg then -(p : ℚ) * I.lo else (p : ℚ) * I.hi) + (k : ℚ)) / (q : ℚ) - (m : ℚ)) :
    hasOverlapBranch p q neg I J k m = true := by
  unfold hasOverlapBranch
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq
  have hIld : (0 : ℚ) < I.ld := by exact_mod_cast I.ldPos
  have hIhd : (0 : ℚ) < I.hd := by exact_mod_cast I.hdPos
  have hJld : (0 : ℚ) < J.ld := by exact_mod_cast J.ldPos
  have hJhd : (0 : ℚ) < J.hd := by exact_mod_cast J.hdPos
  cases hneg : neg
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    rw [hneg] at h1 h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    have hlo_eq :
        ((p : ℚ) * I.lo + (k : ℚ)) / (q : ℚ) - (m : ℚ) =
          (((p : ℤ) * I.ln + ((k : ℤ) - m * (q : ℤ)) * (I.ld : ℤ) : ℤ) : ℚ) /
            (((q : ℤ) * (I.ld : ℤ) : ℤ) : ℚ) := by
      unfold RatInterval.lo
      push_cast
      field_simp [hqpos.ne', hIld.ne']
      ring
    have hhi_eq :
        ((p : ℚ) * I.hi + (k : ℚ)) / (q : ℚ) - (m : ℚ) =
          (((p : ℤ) * I.hn + ((k : ℤ) - m * (q : ℤ)) * (I.hd : ℤ) : ℤ) : ℚ) /
            (((q : ℤ) * (I.hd : ℤ) : ℤ) : ℚ) := by
      unfold RatInterval.hi
      push_cast
      field_simp [hqpos.ne', hIhd.ne']
      ring
    rw [hlo_eq] at h1
    rw [hhi_eq] at h2
    unfold RatInterval.hi at h1
    unfold RatInterval.lo at h2
    have hdenLo : (0 : ℚ) < ((q : ℤ) * (I.ld : ℤ) : ℤ) := by
      push_cast; exact mul_pos hqpos hIld
    have hdenHi : (0 : ℚ) < ((q : ℤ) * (I.hd : ℤ) : ℤ) := by
      push_cast; exact mul_pos hqpos hIhd
    rw [div_lt_div_iff₀ hdenLo hJhd] at h1
    rw [div_le_div_iff₀ hJld hdenHi] at h2
    have h1Z : ((p : ℤ) * I.ln + ((k : ℤ) - m * (q : ℤ)) * (I.ld : ℤ)) * (J.hd : ℤ) <
        J.hn * ((q : ℤ) * (I.ld : ℤ)) := by exact_mod_cast h1
    have h2Z : J.ln * ((q : ℤ) * (I.hd : ℤ)) ≤
        ((p : ℤ) * I.hn + ((k : ℤ) - m * (q : ℤ)) * (I.hd : ℤ)) * (J.ld : ℤ) := by
      exact_mod_cast h2
    exact ⟨h1Z, h2Z⟩
  · simp only [↓reduceIte, decide_eq_true_eq]
    rw [hneg] at h1 h2
    simp only [↓reduceIte] at h1 h2
    have hlo_eq :
        (-(p : ℚ) * I.hi + (k : ℚ)) / (q : ℚ) - (m : ℚ) =
          ((-(p : ℤ) * I.hn + ((k : ℤ) - m * (q : ℤ)) * (I.hd : ℤ) : ℤ) : ℚ) /
            (((q : ℤ) * (I.hd : ℤ) : ℤ) : ℚ) := by
      unfold RatInterval.hi
      push_cast
      field_simp [hqpos.ne', hIhd.ne']
      ring
    have hhi_eq :
        (-(p : ℚ) * I.lo + (k : ℚ)) / (q : ℚ) - (m : ℚ) =
          ((-(p : ℤ) * I.ln + ((k : ℤ) - m * (q : ℤ)) * (I.ld : ℤ) : ℤ) : ℚ) /
            (((q : ℤ) * (I.ld : ℤ) : ℤ) : ℚ) := by
      unfold RatInterval.lo
      push_cast
      field_simp [hqpos.ne', hIld.ne']
      ring
    rw [hlo_eq] at h1
    rw [hhi_eq] at h2
    unfold RatInterval.hi at h1
    unfold RatInterval.lo at h2
    have hdenLo : (0 : ℚ) < ((q : ℤ) * (I.hd : ℤ) : ℤ) := by
      push_cast; exact mul_pos hqpos hIhd
    have hdenHi : (0 : ℚ) < ((q : ℤ) * (I.ld : ℤ) : ℤ) := by
      push_cast; exact mul_pos hqpos hIld
    rw [div_lt_div_iff₀ hdenLo hJhd] at h1
    rw [div_le_div_iff₀ hJld hdenHi] at h2
    have h1Z : (-(p : ℤ) * I.hn + ((k : ℤ) - m * (q : ℤ)) * (I.hd : ℤ)) * (J.hd : ℤ) <
        J.hn * ((q : ℤ) * (I.hd : ℤ)) := by exact_mod_cast h1
    have h2Z : J.ln * ((q : ℤ) * (I.ld : ℤ)) ≤
        (-(p : ℤ) * I.ln + ((k : ℤ) - m * (q : ℤ)) * (I.ld : ℤ)) * (J.ld : ℤ) := by
      exact_mod_cast h2
    exact ⟨h1Z, h2Z⟩

/-- Soundness of `hasBranchOverlap` whenever `0 ≤ I.lo`, `I.hi ≤ 1`, and `1 ≤ q`. -/
public theorem hasBranchOverlap_sound {p q : ℕ} (hq : 1 ≤ q) {neg : Bool}
    {I J : RatInterval} (hI0 : 0 ≤ I.lo) (hI1 : I.hi ≤ 1)
    {x y : ℚ} (hx : I.mem x) (hy : J.mem y) (hstep : StepPQ p q neg x y) :
    hasBranchOverlap p q neg I J = true := by
  obtain ⟨hy0, hy1, k, hk, m, hrel⟩ := hstep
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ x := le_trans hI0 hx.1
  have hx1 : x < 1 := lt_of_lt_of_le hx.2 hI1
  have hm_lo : -(p : ℤ) - 1 ≤ m := by
    have hq_lo : -(p : ℚ) ≤ (q : ℚ) * (y + (m : ℚ)) := by
      rw [hrel]
      cases neg <;> simp <;> nlinarith [show (0 : ℚ) ≤ k from by positivity,
        show (0 : ℚ) ≤ p from by positivity]
    have hm_gt : -((p : ℚ) / q) - 1 < (m : ℚ) := by
      have h1 : -((p : ℚ) / q) ≤ y + (m : ℚ) := by
        rw [← neg_div, div_le_iff₀ hqpos]
        linarith [hq_lo]
      linarith
    have hp_le : ((p : ℚ) / q) ≤ p := div_le_self (by positivity) (by exact_mod_cast hq)
    have : -((p : ℚ) + 1) < (m : ℚ) := by linarith
    have hmZ : -((p : ℤ) + 1) < m := by exact_mod_cast this
    grind
  have hm_hi : m ≤ (p : ℤ) + 1 := by
    have hq_hi : (q : ℚ) * (y + (m : ℚ)) < (p : ℚ) + q := by
      rw [hrel]
      have hk_lt : (k : ℚ) < q := by exact_mod_cast hk
      cases neg <;> simp <;> nlinarith [show (0 : ℚ) ≤ p from by positivity]
    have hm_lt : (m : ℚ) < (p : ℚ) / q + 1 := by
      have h1 : y + (m : ℚ) < (p : ℚ) / q + 1 := by
        have h1' : y + (m : ℚ) < ((p : ℚ) + q) / q := (lt_div_iff₀ hqpos).mpr (by linarith)
        have hadd : ((p : ℚ) + q) / q = (p : ℚ) / q + 1 := by field_simp [hqpos.ne']
        linarith
      linarith
    have hp_le : ((p : ℚ) / q) ≤ p := div_le_self (by positivity) (by exact_mod_cast hq)
    have : (m : ℚ) < (p : ℚ) + 1 := by linarith
    have hmZ : m < (p : ℤ) + 1 := by exact_mod_cast this
    grind
  let idx : ℕ := (m + (p : ℤ) + 1).toNat
  have hidx_lt : idx < 2 * p + 3 := by grind
  have hidx_eq : ((idx : ℤ) - (p : ℤ) - 1) = m := by grind
  have hob : hasOverlapBranch p q neg I J k m = true := by
    have hyq : y = ((if neg then -(p : ℚ) else (p : ℚ)) * x + (k : ℚ)) / (q : ℚ) - (m : ℚ) := by
      field_simp [hqpos.ne']
      linarith [hrel]
    have hp0 : (0 : ℚ) ≤ p := by positivity
    refine hasOverlapBranch_of_rat hq neg I J k m ?_ ?_
    · cases hneg : neg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hneg] at hyq
        simp only [Bool.false_eq_true, ↓reduceIte] at hyq
        have hlo : ((p : ℚ) * I.lo + (k : ℚ)) / (q : ℚ) - (m : ℚ) ≤ y := by
          rw [hyq]; gcongr; exact hx.1
        exact lt_of_le_of_lt hlo hy.2
      · simp only [↓reduceIte]
        rw [hneg] at hyq
        simp only [↓reduceIte] at hyq
        have hlo : (-(p : ℚ) * I.hi + (k : ℚ)) / (q : ℚ) - (m : ℚ) ≤ y := by
          rw [hyq]
          have : (p : ℚ) * x ≤ (p : ℚ) * I.hi := mul_le_mul_of_nonneg_left hx.2.le hp0
          have : -(p : ℚ) * I.hi ≤ -(p : ℚ) * x := by linarith
          gcongr
        exact lt_of_le_of_lt hlo hy.2
    · cases hneg : neg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hneg] at hyq
        simp only [Bool.false_eq_true, ↓reduceIte] at hyq
        have hhi : y ≤ ((p : ℚ) * I.hi + (k : ℚ)) / (q : ℚ) - (m : ℚ) := by
          rw [hyq]; gcongr; exact hx.2.le
        exact le_trans hy.1 hhi
      · simp only [↓reduceIte]
        rw [hneg] at hyq
        simp only [↓reduceIte] at hyq
        have hhi : y ≤ (-(p : ℚ) * I.lo + (k : ℚ)) / (q : ℚ) - (m : ℚ) := by
          rw [hyq]
          have : (p : ℚ) * I.lo ≤ (p : ℚ) * x := mul_le_mul_of_nonneg_left hx.1 hp0
          have : -(p : ℚ) * x ≤ -(p : ℚ) * I.lo := by linarith
          gcongr
        exact le_trans hy.1 hhi
  unfold hasBranchOverlap
  simp only [List.any_eq_true, List.mem_range]
  refine ⟨k, hk, idx, hidx_lt, ?_⟩
  rwa [hidx_eq]

private lemma countPathsFrom_poly_aux {N M : ℕ} (adj : Fin N → Fin N → Bool)
    (comp : Fin N → Fin M) (htopo : ∀ i j, adj i j = true → comp i ≤ comp j)
    (hnobranch : ∀ i, (Finset.univ.filter (fun j => adj i j = true ∧ comp j = comp i)).card ≤ 1) :
    ∀ (b L : ℕ) (u : Fin N), M - (comp u).val ≤ b →
      countPathsFrom adj u L ≤ (N * (L + 1)) ^ b := by
  intro b
  induction b with
  | zero =>
    intro L u hu
    have hlt : (comp u).val < M := (comp u).isLt
    grind
  | succ b ihb =>
    intro L
    induction L with
    | zero =>
      intro u _
      have hN : 1 ≤ N := Nat.succ_le_of_lt (Fin.pos u)
      simpa [countPathsFrom] using Nat.one_le_pow (b + 1) N hN
    | succ L ihL =>
      intro u hu
      have hN : 1 ≤ N := Nat.succ_le_of_lt (Fin.pos u)
      let same := Finset.univ.filter (fun v => adj u v = true ∧ comp v = comp u)
      let higher := Finset.univ.filter (fun v => adj u v = true ∧ comp u < comp v)
      have hsplit : countPathsFrom adj u (L + 1) =
          (∑ v ∈ same, countPathsFrom adj v L) + (∑ v ∈ higher, countPathsFrom adj v L) := by
        have hdisj : Disjoint same higher := by
          rw [Finset.disjoint_filter]
          intro v _ h1 h2
          exact ne_of_lt h2.2 h1.2.symm
        have hunion : Finset.univ.filter (fun v => adj u v = true) = same ∪ higher := by
          ext v
          simp only [same, higher, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hadj
            rcases eq_or_lt_of_le (htopo u v hadj) with heq | hlt
            · exact Or.inl ⟨hadj, heq.symm⟩
            · exact Or.inr ⟨hadj, hlt⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        rw [countPathsFrom, ← Finset.sum_filter, hunion, Finset.sum_union hdisj]
      have hsame : ∑ v ∈ same, countPathsFrom adj v L ≤ (N * (L + 1)) ^ (b + 1) := by
        have hle1' : same.card ≤ 1 := hnobranch u
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1' with hc0 | hc1
        · rw [Finset.card_eq_zero.mp hc0, Finset.sum_empty]
          exact Nat.zero_le _
        · obtain ⟨v0, hv0⟩ := Finset.card_eq_one.mp hc1
          rw [hv0, Finset.sum_singleton]
          have hv0_mem : v0 ∈ same := hv0 ▸ Finset.mem_singleton_self v0
          have hceq : comp v0 = comp u := (Finset.mem_filter.mp hv0_mem).2.2
          have hbu : M - (comp v0).val ≤ b + 1 := by rw [hceq]; exact hu
          exact ihL v0 hbu
      have hhigher : ∑ v ∈ higher, countPathsFrom adj v L ≤ N * (N * (L + 1)) ^ b := by
        have hterm : ∀ v ∈ higher, countPathsFrom adj v L ≤ (N * (L + 1)) ^ b := by
          intro v hv
          have hlt : comp u < comp v := (Finset.mem_filter.mp hv).2.2
          have hvm : (comp v).val < M := (comp v).isLt
          have hbv : M - (comp v).val ≤ b := by
            have : (comp u).val < (comp v).val := hlt
            grind
          exact ihb L v hbv
        calc
          ∑ v ∈ higher, countPathsFrom adj v L
              ≤ ∑ _v ∈ higher, (N * (L + 1)) ^ b := Finset.sum_le_sum hterm
          _ = higher.card * (N * (L + 1)) ^ b := Finset.sum_const _
          _ ≤ N * (N * (L + 1)) ^ b := by
                gcongr
                simpa using (Finset.card_le_univ higher)
      have hcomb : (N * (L + 1)) ^ (b + 1) + N * (N * (L + 1)) ^ b ≤
          (N * (L + 1 + 1)) ^ (b + 1) := by
        have hstep : (N * (L + 1)) ^ (b + 1) + N * (N * (L + 1)) ^ b =
            (N * (L + 1 + 1)) * (N * (L + 1)) ^ b := by
          rw [pow_succ']
          ring
        have hmono : (N * (L + 1)) ^ b ≤ (N * (L + 1 + 1)) ^ b :=
          Nat.pow_le_pow_left (by nlinarith) b
        calc
          (N * (L + 1)) ^ (b + 1) + N * (N * (L + 1)) ^ b
              = (N * (L + 1 + 1)) * (N * (L + 1)) ^ b := hstep
          _ ≤ (N * (L + 1 + 1)) * (N * (L + 1 + 1)) ^ b := by gcongr
          _ = (N * (L + 1 + 1)) ^ (b + 1) := (pow_succ' _ _).symm
      rw [hsplit]
      exact le_trans (Nat.add_le_add hsame hhigher) hcomb

/-- **Polynomial walk-count bound** under topological SCC ordering and no internal branching:
`totalPaths adj L ≤ N · (N · (L + 1))^M`. -/
public theorem totalPaths_poly_bound {N M : ℕ} (adj : Fin N → Fin N → Bool)
    (comp : Fin N → Fin M) (htopo : ∀ i j, adj i j = true → comp i ≤ comp j)
    (hnobranch : ∀ i, (Finset.univ.filter (fun j => adj i j = true ∧ comp j = comp i)).card ≤ 1)
    (L : ℕ) :
    totalPaths adj L ≤ N * (N * (L + 1)) ^ M := by
  unfold totalPaths
  have hterm : ∀ u ∈ Finset.univ, countPathsFrom adj u L ≤ (N * (L + 1)) ^ M := by
    intro u _
    exact countPathsFrom_poly_aux adj comp htopo hnobranch M L u (Nat.sub_le _ _)
  calc
    ∑ u : Fin N, countPathsFrom adj u L
        ≤ ∑ _u : Fin N, (N * (L + 1)) ^ M := Finset.sum_le_sum hterm
    _ = N * (N * (L + 1)) ^ M := by simp

private lemma prod_le_prod_nat_ze (s : Finset ℕ) (f g : ℕ → ℕ)
    (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Nat.mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih fun i hi => hfg i (Finset.mem_insert_of_mem hi))

private lemma poly_le_exp_aux (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ((L + 1 : ℕ) : ℝ) ^ M ≤ K * (1 + ε) ^ L := by
  refine ⟨((Nat.factorial M : ℝ) * (1 + ε) ^ M) / ε ^ M, by positivity, fun L => ?_⟩
  have hpow_le : (L + 1) ^ M ≤ Nat.factorial M * Nat.choose (L + M) M := by
    have hdesc : (L + M).descFactorial M = Nat.factorial M * Nat.choose (L + M) M :=
      Nat.descFactorial_eq_factorial_mul_choose (L + M) M
    rw [← hdesc, Nat.descFactorial_eq_prod_range]
    have hconst : ∏ _i ∈ Finset.range M, (L + 1) = (L + 1) ^ M := by simp
    rw [← hconst]
    refine prod_le_prod_nat_ze _ _ _ fun i hi => ?_
    have := Finset.mem_range.mp hi
    grind
  have hbin : (Nat.choose (L + M) M : ℝ) * ε ^ M ≤ (1 + ε) ^ (L + M) := by
    have hadd := add_pow ε (1 : ℝ) (L + M)
    rw [add_comm ε 1] at hadd
    have hmem : M ∈ Finset.range (L + M + 1) := Finset.mem_range.mpr (by grind)
    let term : ℕ → ℝ := fun k => ε ^ k * 1 ^ (L + M - k) * (Nat.choose (L + M) k : ℝ)
    have hle_sum : term M ≤ ∑ k ∈ Finset.range (L + M + 1), term k :=
      Finset.single_le_sum (fun k _ => by dsimp [term]; positivity) hmem
    have hterm_eq : (Nat.choose (L + M) M : ℝ) * ε ^ M = term M := by
      dsimp [term]
      simp [mul_comm]
    rw [hterm_eq]
    exact hadd ▸ hle_sum
  have h1 : ((L + 1 : ℕ) : ℝ) ^ M ≤ (Nat.factorial M : ℝ) * (Nat.choose (L + M) M : ℝ) := by
    exact_mod_cast hpow_le
  have hεM : (0 : ℝ) < ε ^ M := pow_pos hε M
  calc
    ((L + 1 : ℕ) : ℝ) ^ M
        ≤ (Nat.factorial M : ℝ) * (Nat.choose (L + M) M : ℝ) := h1
    _ = ((Nat.factorial M : ℝ) / ε ^ M) * ((Nat.choose (L + M) M : ℝ) * ε ^ M) := by
          field_simp [hεM.ne']
    _ ≤ ((Nat.factorial M : ℝ) / ε ^ M) * (1 + ε) ^ (L + M) := by gcongr
    _ = (((Nat.factorial M : ℝ) * (1 + ε) ^ M) / ε ^ M) * (1 + ε) ^ L := by
          rw [pow_add]; ring

/-- **Zero-topological-entropy mother theorem**: any `ZeroEntropyAutomaton` has zero symbolic
topological entropy (`totalPaths adj L ≤ C · (1 + ε)^L` for every `ε > 0`). -/
public theorem zero_entropy_of_no_branching_scc {p q N M : ℕ} {neg : Bool}
    (A : ZeroEntropyAutomaton p q neg N M) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ L : ℕ, (totalPaths (fun i j => hasBranchOverlap p q neg (A.cells i) (A.cells j)) L : ℝ) ≤
        C * (1 + ε) ^ L := by
  intro ε hε
  obtain ⟨K, hKpos, hK⟩ := poly_le_exp_aux M hε
  refine ⟨max 1 ((N : ℝ) ^ (M + 1) * K), by positivity, fun L => ?_⟩
  have hnat := totalPaths_poly_bound
    (fun i j => hasBranchOverlap p q neg (A.cells i) (A.cells j))
    A.comp A.htopo A.hnobranch L
  have hreal :
      (totalPaths (fun i j => hasBranchOverlap p q neg (A.cells i) (A.cells j)) L : ℝ) ≤
        (N : ℝ) ^ (M + 1) * ((L + 1 : ℕ) : ℝ) ^ M := by
    have hnat' : totalPaths (fun i j => hasBranchOverlap p q neg (A.cells i) (A.cells j)) L ≤
        N ^ (M + 1) * (L + 1) ^ M := by
      calc
        totalPaths (fun i j => hasBranchOverlap p q neg (A.cells i) (A.cells j)) L
            ≤ N * (N * (L + 1)) ^ M := hnat
        _ = N ^ (M + 1) * (L + 1) ^ M := by
            rw [mul_pow, pow_succ']; ring
    exact_mod_cast hnat'
  have hpow_pos : 0 ≤ (1 + ε) ^ L := by positivity
  calc
    (totalPaths (fun i j => hasBranchOverlap p q neg (A.cells i) (A.cells j)) L : ℝ)
        ≤ (N : ℝ) ^ (M + 1) * ((L + 1 : ℕ) : ℝ) ^ M := hreal
    _ ≤ (N : ℝ) ^ (M + 1) * (K * (1 + ε) ^ L) := by gcongr; exact hK L
    _ = ((N : ℝ) ^ (M + 1) * K) * (1 + ε) ^ L := by ring
    _ ≤ max 1 ((N : ℝ) ^ (M + 1) * K) * (1 + ε) ^ L :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow_pos

/-- Orbit soundness: any `L`-step `StepPQ`-orbit staying inside the `N` automaton cells traces a
valid `L`-step walk in the overlap graph. -/
public theorem automaton_orbit_sound {p q N M : ℕ} {neg : Bool} (hq : 1 ≤ q)
    (A : ZeroEntropyAutomaton p q neg N M) (orb : ℕ → ℚ) (L : ℕ)
    (hstep : ∀ t < L, StepPQ p q neg (orb t) (orb (t + 1)))
    (hin : ∀ t ≤ L, ∃ i : Fin N, (A.cells i).mem (orb t)) :
    ∃ idx : ℕ → Fin N, ∀ t < L,
      hasBranchOverlap p q neg (A.cells (idx t)) (A.cells (idx (t + 1))) = true := by
  choose idx hidx using hin
  refine ⟨fun t => if ht : t ≤ L then idx t ht else idx 0 (Nat.zero_le L), fun t ht => ?_⟩
  have ht0 : t ≤ L := ht.le
  have ht1 : t + 1 ≤ L := ht
  simp only [ht0, ht1, ↓reduceDIte]
  exact hasBranchOverlap_sound hq (A.hcells0 _) (A.hcells1 _) (hidx t ht0) (hidx (t + 1) ht1)
    (hstep t ht)


/-! ### 2b. Finite-depth survivor bridge `U → V_d` (pure kernel `decide`, zero axioms)

The zero-entropy certificates above live on the survivor cells `V_d` produced by the exact
preimage iteration in `scripts/generate_certificates.py --verify`.  This section closes the gap
between the target region `U` and those cells inside Lean itself: a rational closed interval
preimage iteration over-approximates the `d`-step survivor set, and a `decide`-checked containment
certificate places every such interval in the closed hull of one of the automaton cells.  Hence any
`StepPQ`-orbit that stays in `U` for `d` more steps has its point inside a certified cell.
-/

/-- A closed rational box with integer numerator/denominator endpoints.

The endpoints are kept integral on purpose: `ℚ` comparisons are not kernel-reducible, so a
certificate over `ℚ` cannot be discharged by `decide`.  Cross-multiplied integer comparisons are
reducible, which makes the final containment check a genuine kernel computation. -/
public structure PreBox where
  loN : ℤ
  loD : ℕ
  hiN : ℤ
  hiD : ℕ

namespace PreBox

/-- Lower endpoint as a rational. -/
@[expose] public def loQ (B : PreBox) : ℚ := (B.loN : ℚ) / (B.loD : ℚ)

/-- Upper endpoint as a rational. -/
@[expose] public def hiQ (B : PreBox) : ℚ := (B.hiN : ℚ) / (B.hiD : ℚ)

/-- Closed membership `lo ≤ x ≤ hi`. -/
@[expose] public def mem (B : PreBox) (x : ℚ) : Prop := B.loQ ≤ x ∧ x ≤ B.hiQ

instance (B : PreBox) (x : ℚ) : Decidable (B.mem x) := by
  unfold PreBox.mem
  infer_instance

/-- Integer cross-multiplied closed non-emptiness test. -/
@[expose] public def nonempty (B : PreBox) : Bool :=
  decide (B.loN * (B.hiD : ℤ) ≤ B.hiN * (B.loD : ℤ))

lemma nonempty_of_mem {B : PreBox} {x : ℚ} (hlo : 0 < B.loD) (hhi : 0 < B.hiD)
    (h : B.mem x) : B.nonempty = true := by
  unfold nonempty
  apply decide_eq_true
  have hle : B.loQ ≤ B.hiQ := le_trans h.1 h.2
  unfold PreBox.loQ PreBox.hiQ at hle
  rw [div_le_div_iff₀ (by exact_mod_cast hlo) (by exact_mod_cast hhi)] at hle
  exact_mod_cast hle

end PreBox

/-- Clip a closed box to a half-open rational interval, comparing by exact integers. -/
@[expose] public def clipBox (I : RatInterval) (B : PreBox) : PreBox :=
  if _ : I.ln * (B.loD : ℤ) ≤ B.loN * (I.ld : ℤ) then
    if _ : B.hiN * (I.hd : ℤ) ≤ I.hn * (B.hiD : ℤ) then
      { loN := B.loN, loD := B.loD, hiN := B.hiN, hiD := B.hiD }
    else
      { loN := B.loN, loD := B.loD, hiN := I.hn, hiD := I.hd }
  else
    if _ : B.hiN * (I.hd : ℤ) ≤ I.hn * (B.hiD : ℤ) then
      { loN := I.ln, loD := I.ld, hiN := B.hiN, hiD := B.hiD }
    else
      { loN := I.ln, loD := I.ld, hiN := I.hn, hiD := I.hd }

public lemma clipBox_mem {I : RatInterval} {B : PreBox} {x : ℚ}
    (hx : I.mem x) (hB : B.mem x) : (clipBox I B).mem x := by
  obtain ⟨hx1, hx2⟩ := hx
  simp only [PreBox.mem, PreBox.loQ, PreBox.hiQ] at hB ⊢
  unfold clipBox
  split_ifs <;>
    exact ⟨by first | exact hx1 | exact hB.1,
      by first | exact le_of_lt hx2 | exact hB.2⟩

/-- Closed affine preimage of a box on branch `(k, m)`, in integer endpoints. -/
@[expose] public def rawBox (neg : Bool) (J : PreBox) (p q : ℕ) (k : ℕ) (m : ℤ) : PreBox :=
  if neg then
    { loN := (k : ℤ) * (J.hiD : ℤ) - (q : ℤ) * (m * (J.hiD : ℤ) + J.hiN)
      loD := p * J.hiD
      hiN := (k : ℤ) * (J.loD : ℤ) - (q : ℤ) * (m * (J.loD : ℤ) + J.loN)
      hiD := p * J.loD }
  else
    { loN := (q : ℤ) * (J.loN + m * (J.loD : ℤ)) - (k : ℤ) * (J.loD : ℤ)
      loD := p * J.loD
      hiN := (q : ℤ) * (J.hiN + m * (J.hiD : ℤ)) - (k : ℤ) * (J.hiD : ℤ)
      hiD := p * J.hiD }

public lemma rawBox_loQ_false {p q : ℕ} (hp : 0 < p) {J : PreBox} {k : ℕ} {m : ℤ}
    (hJ : 0 < J.loD) :
    (rawBox false J p q k m).loQ =
      ((q : ℚ) * (J.loQ + (m : ℚ)) - (k : ℚ)) / (p : ℚ) := by
  unfold rawBox PreBox.loQ
  simp only [Bool.false_eq_true, ↓reduceIte]
  field_simp [hJ.ne', hp.ne']
  push_cast
  ring_nf

public lemma rawBox_hiQ_false {p q : ℕ} (hp : 0 < p) {J : PreBox} {k : ℕ} {m : ℤ}
    (hJ : 0 < J.hiD) :
    (rawBox false J p q k m).hiQ =
      ((q : ℚ) * (J.hiQ + (m : ℚ)) - (k : ℚ)) / (p : ℚ) := by
  unfold rawBox PreBox.hiQ
  simp only [Bool.false_eq_true, ↓reduceIte]
  field_simp [hJ.ne', hp.ne']
  push_cast
  ring_nf

public lemma rawBox_loQ_true {p q : ℕ} (hp : 0 < p) {J : PreBox} {k : ℕ} {m : ℤ}
    (hJ : 0 < J.hiD) :
    (rawBox true J p q k m).loQ =
      ((k : ℚ) - (m : ℚ) * (q : ℚ) - (q : ℚ) * J.hiQ) / (p : ℚ) := by
  unfold rawBox PreBox.loQ PreBox.hiQ
  simp only [↓reduceIte]
  field_simp [hJ.ne', hp.ne']
  push_cast
  ring_nf

public lemma rawBox_hiQ_true {p q : ℕ} (hp : 0 < p) {J : PreBox} {k : ℕ} {m : ℤ}
    (hJ : 0 < J.loD) :
    (rawBox true J p q k m).hiQ =
      ((k : ℚ) - (m : ℚ) * (q : ℚ) - (q : ℚ) * J.loQ) / (p : ℚ) := by
  unfold rawBox PreBox.hiQ PreBox.loQ
  simp only [↓reduceIte]
  field_simp [hJ.ne', hp.ne']
  push_cast
  ring_nf

public lemma rawBox_mem {p q : ℕ} (hp : 0 < p) {neg : Bool} {J : PreBox} {k : ℕ} {m : ℤ}
    {x y : ℚ} (hJlo : 0 < J.loD) (hJhi : 0 < J.hiD) (hy : J.mem y)
    (hrel : (q : ℚ) * (y + (m : ℚ)) =
      (if neg then -(p : ℚ) else (p : ℚ)) * x + (k : ℚ)) :
    (rawBox neg J p q k m).mem x := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  obtain ⟨hy1, hy2⟩ := hy
  cases neg with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrel
      have hxeq : x = ((q : ℚ) * (y + (m : ℚ)) - (k : ℚ)) / (p : ℚ) := by
        rw [eq_div_iff hpQ.ne']
        linarith
      rw [PreBox.mem, rawBox_loQ_false hp hJlo, rawBox_hiQ_false hp hJhi]
      constructor
      · rw [hxeq]
        gcongr
      · rw [hxeq]
        gcongr
  | true =>
      simp only [↓reduceIte] at hrel
      have hxeq : x = ((k : ℚ) - (m : ℚ) * (q : ℚ) - (q : ℚ) * y) / (p : ℚ) := by
        rw [eq_div_iff hpQ.ne']
        linarith
      rw [PreBox.mem, rawBox_loQ_true hp hJhi, rawBox_hiQ_true hp hJlo]
      constructor
      · rw [hxeq]
        gcongr
      · rw [hxeq]
        gcongr

/-- One backward step: all closed preimage boxes of `S` clipped to the target `U`. -/
@[expose] public def preBoxStep (p q : ℕ) (neg : Bool) (U : List RatInterval)
    (S : List PreBox) : List PreBox :=
  U.flatMap fun I => S.flatMap fun J => (List.range q).flatMap fun (k : ℕ) =>
    (List.range (2 * p + 3)).flatMap fun (idx : ℕ) =>
      let B := clipBox I (rawBox neg J p q k ((idx : ℤ) - (p : ℤ) - 1))
      if B.nonempty then [B] else []

/-- `d`-fold backward preimage iteration from the target `U`. -/
@[expose] public def preIterate (p q : ℕ) (neg : Bool) (U : List RatInterval) :
    ℕ → List PreBox
  | 0 => U.map fun I => ⟨I.ln, I.ld, I.hn, I.hd⟩
  | n + 1 => preBoxStep p q neg U (preIterate p q neg U n)

/-- Well-formedness invariant: every box has positive denominators. -/
@[expose] public def PreBox.wf (B : PreBox) : Prop := 0 < B.loD ∧ 0 < B.hiD

public lemma rawBox_wf {p q : ℕ} (hp : 0 < p) {neg : Bool} {J : PreBox} {k : ℕ} {m : ℤ}
    (hJ : J.wf) : (rawBox neg J p q k m).wf := by
  unfold rawBox
  cases neg with
  | false => exact ⟨Nat.mul_pos hp hJ.1, Nat.mul_pos hp hJ.2⟩
  | true => exact ⟨Nat.mul_pos hp hJ.2, Nat.mul_pos hp hJ.1⟩

public lemma clipBox_wf {I : RatInterval} {B : PreBox} (hB : B.wf) : (clipBox I B).wf := by
  simp only [PreBox.wf, clipBox]
  split_ifs <;>
    exact ⟨by first | exact I.ldPos | exact hB.1, by first | exact I.hdPos | exact hB.2⟩

public lemma preIterate_wf {p : ℕ} (hp : 0 < p) (q : ℕ) (neg : Bool) (U : List RatInterval) :
    ∀ (n : ℕ) (B : PreBox), B ∈ preIterate p q neg U n → B.wf := by
  intro n
  induction n with
  | zero =>
      intro B hB
      simp only [preIterate, List.mem_map] at hB
      obtain ⟨I, _, rfl⟩ := hB
      exact ⟨I.ldPos, I.hdPos⟩
  | succ n ih =>
      intro B hB
      simp only [preIterate, preBoxStep, List.mem_flatMap, List.mem_range] at hB
      obtain ⟨I, _, J, hJ, k, _, idx, _, hmem⟩ := hB
      by_cases hne : (clipBox I (rawBox neg J p q k ((idx : ℤ) - (p : ℤ) - 1))).nonempty = true
      · simp only [hne, ite_true, List.mem_singleton] at hmem
        subst hmem
        exact clipBox_wf (rawBox_wf hp (ih J hJ))
      · simp [hne] at hmem

public lemma preBoxStep_sound {p q : ℕ} (hp : 0 < p) {neg : Bool} {U : List RatInterval}
    {S : List PreBox} (hU0 : ∀ I ∈ U, 0 ≤ I.ln) (hU1 : ∀ I ∈ U, I.hn ≤ (I.hd : ℤ))
    (hwf : ∀ J ∈ S, J.wf)
    {x y : ℚ} (hx : ∃ I ∈ U, I.mem x) (hy : ∃ J ∈ S, J.mem y)
    (hstep : StepPQ p q neg x y) :
    ∃ B ∈ preBoxStep p q neg U S, B.mem x := by
  obtain ⟨I, hIU, hxI⟩ := hx
  obtain ⟨J, hJS, hyJ⟩ := hy
  obtain ⟨hy0, hy1, k, hk, m, hrel⟩ := hstep
  have hqpos : (0 : ℚ) < q := by
    have hq1 : (1 : ℕ) ≤ q := by omega
    exact_mod_cast hq1
  have hIlo : (0 : ℚ) ≤ I.lo := by
    unfold RatInterval.lo
    exact div_nonneg (by exact_mod_cast hU0 I hIU) (by positivity)
  have hIhi : I.hi ≤ 1 := by
    unfold RatInterval.hi
    rw [div_le_one (by exact_mod_cast I.hdPos)]
    exact_mod_cast hU1 I hIU
  have hx0 : 0 ≤ x := le_trans hIlo hxI.1
  have hx1 : x < 1 := lt_of_lt_of_le hxI.2 hIhi
  have hm_lo : -(p : ℤ) - 1 ≤ m := by
    have hq_lo : -(p : ℚ) ≤ (q : ℚ) * (y + (m : ℚ)) := by
      rw [hrel]
      cases neg <;> simp <;> nlinarith [show (0 : ℚ) ≤ k from by positivity,
        show (0 : ℚ) ≤ p from by positivity]
    have hm_gt : -((p : ℚ) / q) - 1 < (m : ℚ) := by
      have h1 : -((p : ℚ) / q) ≤ y + (m : ℚ) := by
        rw [← neg_div, div_le_iff₀ hqpos]
        linarith [hq_lo]
      linarith
    have hp_le : ((p : ℚ) / q) ≤ p :=
      div_le_self (by positivity) (by exact_mod_cast (show (1 : ℕ) ≤ q by omega))
    have : -((p : ℚ) + 1) < (m : ℚ) := by linarith
    have hmZ : -((p : ℤ) + 1) < m := by exact_mod_cast this
    grind
  have hm_hi : m ≤ (p : ℤ) + 1 := by
    have hq_hi : (q : ℚ) * (y + (m : ℚ)) < (p : ℚ) + q := by
      rw [hrel]
      have hk_lt : (k : ℚ) < q := by exact_mod_cast hk
      cases neg <;> simp <;> nlinarith [show (0 : ℚ) ≤ p from by positivity]
    have hm_lt : (m : ℚ) < (p : ℚ) / q + 1 := by
      have h1 : y + (m : ℚ) < (p : ℚ) / q + 1 := by
        have h1' : y + (m : ℚ) < ((p : ℚ) + q) / q := (lt_div_iff₀ hqpos).mpr (by linarith)
        have hadd : ((p : ℚ) + q) / q = (p : ℚ) / q + 1 := by field_simp [hqpos.ne']
        linarith
      linarith
    have hp_le : ((p : ℚ) / q) ≤ p :=
      div_le_self (by positivity) (by exact_mod_cast (show (1 : ℕ) ≤ q by omega))
    have : (m : ℚ) < (p : ℚ) + 1 := by linarith
    have hmZ : m < (p : ℤ) + 1 := by exact_mod_cast this
    grind
  let idx : ℕ := (m + (p : ℤ) + 1).toNat
  have hidx_lt : idx < 2 * p + 3 := by grind
  have hidx_eq : ((idx : ℤ) - (p : ℤ) - 1) = m := by grind
  have hJwf : J.wf := hwf J hJS
  let B : PreBox := clipBox I (rawBox neg J p q k m)
  have hBmem : B.mem x :=
    clipBox_mem hxI (rawBox_mem hp hJwf.1 hJwf.2 hyJ hrel)
  have hBwf : B.wf := clipBox_wf (rawBox_wf hp hJwf)
  have hBne : B.nonempty = true := PreBox.nonempty_of_mem hBwf.1 hBwf.2 hBmem
  refine ⟨B, ?_, hBmem⟩
  simp only [preBoxStep, List.mem_flatMap, List.mem_range]
  refine ⟨I, hIU, J, hJS, k, hk, idx, hidx_lt, ?_⟩
  rw [hidx_eq]
  change B ∈ (if B.nonempty then [B] else [])
  simp [hBne]

public lemma preIterate_sound {p q : ℕ} (hp : 0 < p) {neg : Bool} {U : List RatInterval}
    (hU0 : ∀ I ∈ U, 0 ≤ I.ln) (hU1 : ∀ I ∈ U, I.hn ≤ (I.hd : ℤ))
    {orb : ℕ → ℚ} {d : ℕ}
    (hstep : ∀ i < d, StepPQ p q neg (orb i) (orb (i + 1)))
    (hin : ∀ i ≤ d, ∃ I ∈ U, I.mem (orb i)) :
    ∃ B ∈ preIterate p q neg U d, B.mem (orb 0) := by
  induction d generalizing orb with
  | zero =>
      obtain ⟨I, hIU, hIx⟩ := hin 0 (Nat.zero_le 0)
      exact ⟨⟨I.ln, I.ld, I.hn, I.hd⟩,
        List.mem_map.mpr ⟨I, hIU, rfl⟩, ⟨hIx.1, le_of_lt hIx.2⟩⟩
  | succ d ih =>
      have hstep' : ∀ i < d, StepPQ p q neg (orb (i + 1)) (orb (i + 1 + 1)) := by
        intro i hi
        simpa [Nat.add_assoc] using hstep (i + 1) (by omega)
      have hin' : ∀ i ≤ d, ∃ I ∈ U, I.mem (orb (i + 1)) := by
        intro i hi
        exact hin (i + 1) (by omega)
      obtain ⟨B, hB, hBmem⟩ := ih (orb := fun i => orb (i + 1)) hstep' hin'
      exact preBoxStep_sound hp hU0 hU1 (preIterate_wf hp q neg U d) (hin 0 (Nat.zero_le _))
        ⟨B, hB, hBmem⟩ (hstep 0 (Nat.succ_pos d))

/-- Closed-hull containment test for a box in a `RatInterval`, by integer cross-multiplication. -/
@[expose] public def closedWithin (B : PreBox) (C : RatInterval) : Bool :=
  decide (C.ln * (B.loD : ℤ) ≤ B.loN * (C.ld : ℤ) ∧
    B.hiN * (C.hd : ℤ) ≤ C.hn * (B.hiD : ℤ))

public lemma closedWithin_sound {B : PreBox} {C : RatInterval} {x : ℚ}
    (hlo : 0 < B.loD) (hhi : 0 < B.hiD)
    (h : closedWithin B C = true) (hx : B.mem x) : C.closedMem x := by
  have h' := of_decide_eq_true h
  constructor
  · have hCB : C.lo ≤ B.loQ := by
      unfold RatInterval.lo PreBox.loQ
      rw [div_le_div_iff₀ (by exact_mod_cast C.ldPos) (by exact_mod_cast hlo)]
      exact_mod_cast h'.1
    exact le_trans hCB hx.1
  · have hBC : B.hiQ ≤ C.hi := by
      unfold PreBox.hiQ RatInterval.hi
      rw [div_le_div_iff₀ (by exact_mod_cast hhi) (by exact_mod_cast C.hdPos)]
      exact_mod_cast h'.2
    exact le_trans hx.2 hBC

public lemma any_closedWithin_sound {B : PreBox} {cells : List RatInterval} {x : ℚ}
    (hlo : 0 < B.loD) (hhi : 0 < B.hiD)
    (h : cells.any (closedWithin B) = true) (hx : B.mem x) :
    ∃ C ∈ cells, C.closedMem x := by
  rw [List.any_eq_true] at h
  obtain ⟨C, hC, hw⟩ := h
  exact ⟨C, hC, closedWithin_sound hlo hhi hw hx⟩

/-- **Survivor-partition bridge.** If the `d`-fold closed preimage certificate of `U` is contained
in the closed hull of the automaton cells, then every point of a `StepPQ`-orbit that stays in `U`
for `d` further steps lies in the closed hull of one of those cells.  All hypotheses are
kernel-decidable finite integer checks; no `native_decide` is involved. -/
public theorem orbit_closed_mem_cells_of_survives {p q : ℕ} (hp : 0 < p) {neg : Bool}
    {U cells : List RatInterval} {d : ℕ}
    (hU0 : ∀ I ∈ U, 0 ≤ I.ln) (hU1 : ∀ I ∈ U, I.hn ≤ (I.hd : ℤ))
    (hcheck : (preIterate p q neg U d).all (fun B => cells.any (closedWithin B)) = true)
    {orb : ℕ → ℚ} {L : ℕ}
    (hstep : ∀ t < L, StepPQ p q neg (orb t) (orb (t + 1)))
    (hin : ∀ t ≤ L, ∃ I ∈ U, I.mem (orb t))
    {t : ℕ} (ht : t + d ≤ L) :
    ∃ C ∈ cells, C.closedMem (orb t) := by
  have hstep' : ∀ i < d, StepPQ p q neg (orb (t + i)) (orb (t + i + 1)) := by
    intro i hi
    have hlt : t + i < L := by omega
    simpa [Nat.add_assoc] using hstep (t + i) hlt
  have hin' : ∀ i ≤ d, ∃ I ∈ U, I.mem (orb (t + i)) := by
    intro i hi
    exact hin (t + i) (by omega)
  obtain ⟨B, hB, hBmem⟩ := preIterate_sound hp hU0 hU1 hstep' hin'
  have hBwf : B.wf := preIterate_wf hp q neg U d B hB
  rw [List.all_eq_true] at hcheck
  exact any_closedWithin_sound hBwf.1 hBwf.2 (hcheck B hB) (by simpa using hBmem)


/-! ### 3. Concrete machine-checked zero-entropy certificates (`-5/3`, `-3/2`, `+5/3`) -/

public lemma cells_lo_nonneg {N : ℕ} (cells : Fin N → RatInterval)
    (h : ((List.finRange N).all fun i => decide (0 ≤ (cells i).ln)) = true) :
    ∀ i, 0 ≤ (cells i).lo := by
  intro i
  rw [List.all_eq_true] at h
  have hln : 0 ≤ (cells i).ln := by simpa using h i (List.mem_finRange i)
  unfold RatInterval.lo
  exact div_nonneg (by exact_mod_cast hln) (by positivity)

public lemma cells_hi_le_one {N : ℕ} (cells : Fin N → RatInterval)
    (h : ((List.finRange N).all fun i => decide ((cells i).hn ≤ ((cells i).hd : ℤ))) = true) :
    ∀ i, (cells i).hi ≤ 1 := by
  intro i
  rw [List.all_eq_true] at h
  have hhn : (cells i).hn ≤ ((cells i).hd : ℤ) := by simpa using h i (List.mem_finRange i)
  unfold RatInterval.hi
  have hhd : (0 : ℚ) < (cells i).hd := by exact_mod_cast (cells i).hdPos
  rw [div_le_one hhd]
  exact_mod_cast hhn

public lemma topo_from_decide {p q N M : ℕ} {neg : Bool}
    (cells : Fin N → RatInterval) (comp : Fin N → Fin M)
    (h : ((List.finRange N).all fun i =>
      (List.finRange N).all fun j =>
        !hasBranchOverlap p q neg (cells i) (cells j) || decide (comp i ≤ comp j)) = true) :
    ∀ i j, hasBranchOverlap p q neg (cells i) (cells j) = true → comp i ≤ comp j := by
  intro i j hadj
  rw [List.all_eq_true] at h
  have hi := h i (List.mem_finRange i)
  rw [List.all_eq_true] at hi
  have hij := hi j (List.mem_finRange j)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hij
  rcases hij with hno | hle
  · simp [hadj] at hno
  · exact hle

public lemma nobranch_from_decide {p q N M : ℕ} {neg : Bool}
    (cells : Fin N → RatInterval) (comp : Fin N → Fin M)
    (h : ((List.finRange N).all fun i =>
      decide ((List.finRange N).countP (fun j =>
        hasBranchOverlap p q neg (cells i) (cells j) && decide (comp j = comp i)) ≤ 1)) =
      true) :
    ∀ i, (Finset.univ.filter (fun j =>
      hasBranchOverlap p q neg (cells i) (cells j) = true ∧ comp j = comp i)).card ≤ 1 := by
  intro i
  rw [List.all_eq_true] at h
  have hcnt : (List.finRange N).countP (fun j =>
      hasBranchOverlap p q neg (cells i) (cells j) && decide (comp j = comp i)) ≤ 1 := by
    simpa using h i (List.mem_finRange i)
  have heq : (Finset.univ.filter (fun j =>
      hasBranchOverlap p q neg (cells i) (cells j) = true ∧ comp j = comp i)).card =
      (List.finRange N).countP (fun j =>
        hasBranchOverlap p q neg (cells i) (cells j) && decide (comp j = comp i)) := by
    rw [List.countP_eq_length_filter]
    have hnodup : ((List.finRange N).filter (fun j =>
        hasBranchOverlap p q neg (cells i) (cells j) && decide (comp j = comp i))).Nodup :=
      (List.nodup_finRange N).filter _
    rw [← List.toFinset_card_of_nodup hnodup]
    congr 1
    ext j
    simp [Finset.mem_filter]
  grind

@[expose] public def neg53List : List RatInterval :=
  [mkCell 89 250 483 1250, mkCell 517 1250 733 1250, mkCell 767 1250 161 250]

@[expose] public def neg53CompList : List ℕ := [2, 0, 1]

/-- Exact zero-entropy automaton certificate for the finite-depth survivor partition of `-5/3`
centered `[89/250, 161/250)` (width `36/125 = 0.2880`, `3` cells, `3` SCCs). -/
@[expose] public def cert_neg_5_3 : ZeroEntropyAutomaton 5 3 true 3 3 where
  cells := fun i => getCell neg53List i.val
  comp := fun i => getComp 3 neg53CompList i.val
  hcells0 := cells_lo_nonneg _ (by decide)
  hcells1 := cells_hi_le_one _ (by decide)
  htopo := topo_from_decide _ _ (by decide)
  hnobranch := nobranch_from_decide _ _ (by decide)

public theorem cert_neg_5_3_width :
    (mkCell 89 250 161 250).width = 36 / 125 := by
  norm_num [RatInterval.width, RatInterval.lo, RatInterval.hi, mkCell]

public theorem cert_neg_5_3_zero_entropy :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ L : ℕ, (totalPaths (fun i j =>
        hasBranchOverlap 5 3 true (cert_neg_5_3.cells i) (cert_neg_5_3.cells j)) L : ℝ) ≤
          C * (1 + ε) ^ L :=
  zero_entropy_of_no_branching_scc cert_neg_5_3

@[expose] public def neg32HoledList : List RatInterval :=
  [mkCell 147 1000 298 2025, mkCell 302 2025 323 2025,
   mkCell 352 2025 373 2025, mkCell 377 2025 1271 6075,
   mkCell 1279 6075 1321 6075, mkCell 1379 6075 1421 6075,
   mkCell 1429 6075 353 1500, mkCell 1604 6075 548 2025,
   mkCell 802 2025 2446 6075, mkCell 3629 6075 1223 2025,
   mkCell 1477 2025 4471 6075, mkCell 1147 1500 4646 6075,
   mkCell 4654 6075 4696 6075, mkCell 4754 6075 4796 6075,
   mkCell 4804 6075 1648 2025, mkCell 1652 2025 1673 2025,
   mkCell 1702 2025 1723 2025, mkCell 1727 2025 853 1000]

@[expose] public def neg32HoledCompList : List ℕ :=
  [14, 6, 5, 3, 4, 6, 9, 12, 8, 13, 7, 10, 6, 1, 0, 2, 6, 11]

/-- Exact zero-entropy automaton certificate for the finite-depth survivor partition of `-3/2`
holed union `[147/1000, 43/100) ∪ [57/100, 853/1000)` (width `283/500 = 0.5660 > 1/2`). -/
@[expose] public def cert_neg_3_2_holed : ZeroEntropyAutomaton 3 2 true 18 15 where
  cells := fun i => getCell neg32HoledList i.val
  comp := fun i => getComp 15 neg32HoledCompList i.val
  hcells0 := cells_lo_nonneg _ (by decide)
  hcells1 := cells_hi_le_one _ (by decide)
  htopo := topo_from_decide _ _ (by decide)
  hnobranch := nobranch_from_decide _ _ (by decide)

public theorem cert_neg_3_2_holed_width_gt_half :
    unionWidth [mkCell 147 1000 43 100, mkCell 57 100 853 1000] = 283 / 500 ∧
      (1 / 2 : ℚ) <
        unionWidth [mkCell 147 1000 43 100, mkCell 57 100 853 1000] := by
  norm_num [unionWidth, RatInterval.width, RatInterval.lo, RatInterval.hi, mkCell]

public theorem cert_neg_3_2_holed_zero_entropy :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ L : ℕ, (totalPaths (fun i j =>
        hasBranchOverlap 3 2 true (cert_neg_3_2_holed.cells i)
          (cert_neg_3_2_holed.cells j)) L : ℝ) ≤ C * (1 + ε) ^ L :=
  zero_entropy_of_no_branching_scc cert_neg_3_2_holed

@[expose] public def neg32CenteredList : List RatInterval :=
  [mkCell 1429 5000 14642 50625, mkCell 15358 50625 141068 455625,
   mkCell 143932 455625 3571 11250, mkCell 3929 11250 159818 455625,
   mkCell 162682 455625 18392 50625, mkCell 19108 50625 174818 455625,
   mkCell 177682 455625 555886 1366875, mkCell 561614 1366875 63034 151875,
   mkCell 64466 151875 585886 1366875, mkCell 591614 1366875 7321 16875,
   mkCell 7679 16875 623386 1366875, mkCell 629114 1366875 70534 151875,
   mkCell 71966 151875 3571 7500, mkCell 3929 7500 79909 151875,
   mkCell 81341 151875 737761 1366875, mkCell 743489 1366875 9196 16875,
   mkCell 9554 16875 775261 1366875, mkCell 780989 1366875 87409 151875,
   mkCell 88841 151875 805261 1366875, mkCell 810989 1366875 277943 455625,
   mkCell 280807 455625 31517 50625, mkCell 32233 50625 292943 455625,
   mkCell 295807 455625 7321 11250, mkCell 7679 11250 311693 455625,
   mkCell 314557 455625 35267 50625, mkCell 35983 50625 3571 5000]

@[expose] public def neg32CenteredCompList : List ℕ :=
  [15, 10, 14, 15, 9, 7, 5, 6, 8, 15, 13, 10, 15, 15, 10, 11, 15, 3, 1, 0, 2, 4, 15, 12, 10, 15]

/-- Exact zero-entropy automaton certificate for the finite-depth survivor partition of `-3/2`
centered `[1429/5000, 3571/5000)` (width `1071/2500 = 0.4284`, `26` cells, `16` SCCs). -/
@[expose] public def cert_neg_3_2_centered : ZeroEntropyAutomaton 3 2 true 26 16 where
  cells := fun i => getCell neg32CenteredList i.val
  comp := fun i => getComp 16 neg32CenteredCompList i.val
  hcells0 := cells_lo_nonneg _ (by decide)
  hcells1 := cells_hi_le_one _ (by decide)
  htopo := topo_from_decide _ _ (by decide)
  hnobranch := nobranch_from_decide _ _ (by decide)

public theorem cert_neg_3_2_centered_width :
    (mkCell 1429 5000 3571 5000).width = 1071 / 2500 := by
  norm_num [RatInterval.width, RatInterval.lo, RatInterval.hi, mkCell]

public theorem cert_neg_3_2_centered_zero_entropy :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ L : ℕ, (totalPaths (fun i j =>
        hasBranchOverlap 3 2 true (cert_neg_3_2_centered.cells i)
          (cert_neg_3_2_centered.cells j)) L : ℝ) ≤ C * (1 + ε) ^ L :=
  zero_entropy_of_no_branching_scc cert_neg_3_2_centered

@[expose] public def pos53CenteredList : List RatInterval :=
  [mkCell 697 2000 17727 50000, mkCell 18273 50000 95181 250000,
   mkCell 96819 250000 3909 10000, mkCell 4091 10000 103181 250000,
   mkCell 104819 250000 21727 50000, mkCell 22273 50000 115181 250000,
   mkCell 116819 250000 133181 250000, mkCell 134819 250000 27727 50000,
   mkCell 28273 50000 145181 250000, mkCell 146819 250000 5909 10000,
   mkCell 6091 10000 153181 250000, mkCell 154819 250000 31727 50000,
   mkCell 32273 50000 1303 2000]

@[expose] public def pos53CenteredCompList : List ℕ :=
  [8, 5, 6, 8, 4, 3, 0, 1, 2, 8, 7, 5, 8]

/-- Exact zero-entropy automaton certificate for the finite-depth survivor partition of `+5/3`
centered `[697/2000, 1303/2000)` (width `303/1000 = 0.3030`, `13` cells, `9` SCCs). -/
@[expose] public def cert_pos_5_3_centered : ZeroEntropyAutomaton 5 3 false 13 9 where
  cells := fun i => getCell pos53CenteredList i.val
  comp := fun i => getComp 9 pos53CenteredCompList i.val
  hcells0 := cells_lo_nonneg _ (by decide)
  hcells1 := cells_hi_le_one _ (by decide)
  htopo := topo_from_decide _ _ (by decide)
  hnobranch := nobranch_from_decide _ _ (by decide)

public theorem cert_pos_5_3_centered_width :
    (mkCell 697 2000 1303 2000).width = 303 / 1000 := by
  norm_num [RatInterval.width, RatInterval.lo, RatInterval.hi, mkCell]

public theorem cert_pos_5_3_centered_zero_entropy :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ L : ℕ, (totalPaths (fun i j =>
        hasBranchOverlap 5 3 false (cert_pos_5_3_centered.cells i)
          (cert_pos_5_3_centered.cells j)) L : ℝ) ≤ C * (1 + ε) ^ L :=
  zero_entropy_of_no_branching_scc cert_pos_5_3_centered

/-! ### 4. End-to-end `U → V_d` bridge for the four certified regions -/

/-- Target region of the `-5/3` centered certificate. -/
@[expose] public def neg53Target : List RatInterval := [mkCell 89 250 161 250]

/-- Target region of the `-3/2` holed certificate. -/
@[expose] public def neg32HoledTarget : List RatInterval :=
  [mkCell 147 1000 43 100, mkCell 57 100 853 1000]

/-- Target region of the `-3/2` centered certificate. -/
@[expose] public def neg32CenteredTarget : List RatInterval := [mkCell 1429 5000 3571 5000]

/-- Target region of the `+5/3` centered certificate. -/
@[expose] public def pos53CenteredTarget : List RatInterval := [mkCell 697 2000 1303 2000]

/-- `-5/3` survivor bridge: one additional `StepPQ` step inside `U` already forces the point into
the closed hull of one of the three certified cells. -/
public theorem cert_neg_5_3_survivor_bridge {orb : ℕ → ℚ} {L : ℕ}
    (hstep : ∀ t < L, StepPQ 5 3 true (orb t) (orb (t + 1)))
    (hin : ∀ t ≤ L, ∃ I ∈ neg53Target, I.mem (orb t))
    {t : ℕ} (ht : t + 1 ≤ L) :
    ∃ C ∈ neg53List, C.closedMem (orb t) :=
  orbit_closed_mem_cells_of_survives (p := 5) (q := 3) (neg := true)
    (U := neg53Target) (cells := neg53List) (d := 1) (by norm_num) (by decide) (by decide)
    (by decide) hstep hin ht

/-- `-3/2` holed survivor bridge: six additional `StepPQ` steps inside the holed union force the
point into the closed hull of one of the eighteen certified cells. -/
public theorem cert_neg_3_2_holed_survivor_bridge {orb : ℕ → ℚ} {L : ℕ}
    (hstep : ∀ t < L, StepPQ 3 2 true (orb t) (orb (t + 1)))
    (hin : ∀ t ≤ L, ∃ I ∈ neg32HoledTarget, I.mem (orb t))
    {t : ℕ} (ht : t + 6 ≤ L) :
    ∃ C ∈ neg32HoledList, C.closedMem (orb t) :=
  orbit_closed_mem_cells_of_survives (p := 3) (q := 2) (neg := true)
    (U := neg32HoledTarget) (cells := neg32HoledList) (d := 6) (by norm_num) (by decide) (by decide)
    (by decide) hstep hin ht

/-- `-3/2` centered survivor bridge: seven additional steps inside `U` force the point into the
closed hull of one of the twenty-six certified cells. -/
public theorem cert_neg_3_2_centered_survivor_bridge {orb : ℕ → ℚ} {L : ℕ}
    (hstep : ∀ t < L, StepPQ 3 2 true (orb t) (orb (t + 1)))
    (hin : ∀ t ≤ L, ∃ I ∈ neg32CenteredTarget, I.mem (orb t))
    {t : ℕ} (ht : t + 7 ≤ L) :
    ∃ C ∈ neg32CenteredList, C.closedMem (orb t) :=
  orbit_closed_mem_cells_of_survives (p := 3) (q := 2) (neg := true)
    (U := neg32CenteredTarget) (cells := neg32CenteredList) (d := 7) (by norm_num) (by decide)
    (by decide) (by decide) hstep hin ht

/-- `+5/3` centered survivor bridge: three additional steps inside `U` force the point into the
closed hull of one of the thirteen certified cells. -/
public theorem cert_pos_5_3_centered_survivor_bridge {orb : ℕ → ℚ} {L : ℕ}
    (hstep : ∀ t < L, StepPQ 5 3 false (orb t) (orb (t + 1)))
    (hin : ∀ t ≤ L, ∃ I ∈ pos53CenteredTarget, I.mem (orb t))
    {t : ℕ} (ht : t + 3 ≤ L) :
    ∃ C ∈ pos53CenteredList, C.closedMem (orb t) :=
  orbit_closed_mem_cells_of_survives (p := 5) (q := 3) (neg := false)
    (U := pos53CenteredTarget) (cells := pos53CenteredList) (d := 3) (by norm_num) (by decide)
    (by decide) (by decide) hstep hin ht

end Mahler32.ZeroEntropyAutomaton

end
