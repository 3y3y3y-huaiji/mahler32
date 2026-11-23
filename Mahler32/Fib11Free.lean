module

public import Mathlib

/-!
# Task 7 — 11-free 3-adic reverse pruning and the Fibonacci count

This module formalises the exact `3`-adic reverse pruning process of the task sheet:

* `bstep y = (2*y)/3` undoes one ternary digit;
* `good11FreeAux k prevOdd y` decides whether `k` reverse steps from `y` are legal, banning
  residues `≡ 1 (mod 3)` and forbidding two consecutive residues `≡ 2 (mod 3)`;
* `countBelow P N` counts the `y < N` with `P y = true`.

The main result `fib_count` shows that among `[0, 3^k)` exactly `fib (k+2)` classes survive.
Everything is proved on the genuine `bstep` dynamics, with no abstract list model.
-/

public section

namespace Mahler32.Fib11Free

open scoped BigOperators

/-- One inverse ternary step: `bstep y = (2*y)/3`. -/
@[expose] public def bstep (y : Nat) : Nat := (2 * y) / 3

/-- `k` steps of `3`-adic reverse pruning from `y` are legal, where `prevOdd` records whether
the previous residue was `2`. -/
@[expose] public def good11FreeAux : Nat → Bool → Nat → Bool
  | 0, _, _ => true
  | k + 1, prevOdd, y =>
      if y % 3 = 1 then false
      else if y % 3 = 2 then
        if prevOdd then false else good11FreeAux k true (bstep y)
      else
        good11FreeAux k false (bstep y)

/-- `11`-free legality starting with no previous odd step. -/
@[expose] public def good11Free (k : Nat) (y : Nat) : Bool := good11FreeAux k false y

/-- Fibonacci numbers with `fib 0 = 0`, `fib 1 = 1`. -/
@[expose] public def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Number of `y < N` with `P y = true`. -/
@[expose] public def countBelow (P : Nat → Bool) (N : Nat) : Nat :=
  (List.range N).countP P

/-- Number of survivors after `k` `11`-free reverse steps, starting with `prevOdd = false`. -/
@[expose] public def A (k : Nat) : Nat := countBelow (good11FreeAux k false) (3 ^ k)

/-- Number of survivors after `k` `11`-free reverse steps, starting with `prevOdd = true`. -/
@[expose] public def B (k : Nat) : Nat := countBelow (good11FreeAux k true) (3 ^ k)

/-! ### Theorem 1: periodicity modulo `3^k` -/

/-- Shifting the input by `3*m` shifts the reverse step by `2*m`. -/
theorem bstep_add_three_mul (y m : Nat) : bstep (y + 3 * m) = bstep y + 2 * m := by
  unfold bstep
  have h : 2 * (y + 3 * m) = 2 * y + (2 * m) * 3 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 3)]

/-- `bstep` of a multiple of three. -/
lemma bstep_three_mul (q : Nat) : bstep (3 * q) = 2 * q := by
  unfold bstep
  rw [show 2 * (3 * q) = (2 * q) * 3 by ring]
  exact Nat.mul_div_left (2 * q) (by norm_num)

/-- `bstep` of `3*q+2`. -/
lemma bstep_three_mul_add_two (q : Nat) : bstep (3 * q + 2) = 2 * q + 1 := by
  unfold bstep
  rw [show 2 * (3 * q + 2) = 1 + (2 * q + 1) * 3 by ring]
  rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 3)]
  simp

/-- At a residue `0` the state is reset to `false`. -/
lemma good11FreeAux_succ_three_mul (k : Nat) (prevOdd : Bool) (q : Nat) :
    good11FreeAux (k + 1) prevOdd (3 * q) = good11FreeAux k false (2 * q) := by
  rw [good11FreeAux.eq_2]
  rw [ite_eq_right (by omega : ¬ (3 * q) % 3 = 1),
    ite_eq_right (by omega : ¬ (3 * q) % 3 = 2), bstep_three_mul]

/-- At a residue `1` the answer is `false`. -/
lemma good11FreeAux_succ_three_mul_add_one (k : Nat) (prevOdd : Bool) (q : Nat) :
    good11FreeAux (k + 1) prevOdd (3 * q + 1) = false := by
  rw [good11FreeAux.eq_2, ite_eq_left (by omega : (3 * q + 1) % 3 = 1)]

/-- At a residue `2` with `prevOdd = false` the next state is `true`. -/
lemma good11FreeAux_succ_three_mul_add_two_false (k : Nat) (q : Nat) :
    good11FreeAux (k + 1) false (3 * q + 2) = good11FreeAux k true (2 * q + 1) := by
  rw [good11FreeAux.eq_2]
  rw [ite_eq_right (by omega : ¬ (3 * q + 2) % 3 = 1),
    ite_eq_left (by omega : (3 * q + 2) % 3 = 2)]
  simp [bstep_three_mul_add_two]

/-- At a residue `2` with `prevOdd = true` the answer is `false`. -/
lemma good11FreeAux_succ_three_mul_add_two_true (k : Nat) (q : Nat) :
    good11FreeAux (k + 1) true (3 * q + 2) = false := by
  rw [good11FreeAux.eq_2]
  rw [ite_eq_right (by omega : ¬ (3 * q + 2) % 3 = 1),
    ite_eq_left (by omega : (3 * q + 2) % 3 = 2)]
  simp

/-- The state after `k` steps is invariant under adding `3^k * t`. -/
lemma good11FreeAux_add_pow_mul (k : Nat) (prevOdd : Bool) (y t : Nat) :
    good11FreeAux k prevOdd (y + 3 ^ k * t) = good11FreeAux k prevOdd y := by
  induction k generalizing prevOdd y t with
  | zero => simp [good11FreeAux]
  | succ k ih =>
    conv_lhs => rw [good11FreeAux.eq_2]
    conv_rhs => rw [good11FreeAux.eq_2]
    have hp : 3 ^ (k + 1) * t = 3 * (3 ^ k * t) := by rw [pow_succ]; ring
    have hmod : (y + 3 ^ (k + 1) * t) % 3 = y % 3 := by
      rw [hp, Nat.add_mul_mod_self_left]
    have hb : bstep (y + 3 ^ (k + 1) * t) = bstep y + 3 ^ k * (2 * t) := by
      rw [hp, bstep_add_three_mul]
      ring
    rw [hmod]
    by_cases h1 : y % 3 = 1
    · simp [h1]
    · by_cases h2 : y % 3 = 2
      · cases prevOdd with
        | false =>
          simp only [h2, Bool.false_eq_true, ite_false]
          rw [hb]
          exact ih true (bstep y) (2 * t)
        | true => simp [h2]
      · simp only [h1, h2]
        rw [hb]
        exact ih false (bstep y) (2 * t)

/-- **Theorem 1**: one can walk `k` `11`-free reverse steps from `y` exactly when one can walk
them from `y % 3^k`. -/
theorem good11FreeAux_mod (k : Nat) (prevOdd : Bool) (y : Nat) :
    good11FreeAux k prevOdd y = good11FreeAux k prevOdd (y % 3 ^ k) := by
  conv_lhs => rw [← Nat.mod_add_div y (3 ^ k)]
  rw [good11FreeAux_add_pow_mul]

/-! ### Counting infrastructure -/

/-- `countBelow` as a cardinality of a filtered `Finset`. -/
lemma countBelow_eq_card (P : Nat → Bool) (N : Nat) :
    countBelow P N = ((Finset.range N).filter (fun x => P x = true)).card := by
  have h : countBelow P N = Nat.count (fun x => P x = true) N := by
    unfold countBelow Nat.count
    apply List.countP_congr
    intro x _
    simp
  rw [h, Nat.count_eq_card_filter_range]

/-- `countBelow` as a sum of indicators. -/
lemma countBelow_eq_sum (P : Nat → Bool) (N : Nat) :
    countBelow P N = ∑ x ∈ Finset.range N, (if P x = true then 1 else 0) := by
  rw [countBelow_eq_card, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Regroup a sum over `[0, 3*M)` into the three residue classes modulo `3`. -/
lemma sum_range_three_mul (F : Nat → Nat) (M : Nat) :
    ∑ y ∈ Finset.range (3 * M), F y =
      ∑ q ∈ Finset.range M, (F (3 * q) + F (3 * q + 1) + F (3 * q + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 3 * (M + 1) = 3 * M + 2 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-! ### Elementary modular arithmetic for odd moduli -/

lemma mul_mod_mod (a m N : Nat) : (m * (a % N)) % N = (m * a) % N := by
  calc (m * (a % N)) % N = (m % N) * ((a % N) % N) % N := Nat.mul_mod m (a % N) N
    _ = (m % N) * (a % N) % N := by rw [Nat.mod_mod]
    _ = (m * a) % N := (Nat.mul_mod m a N).symm

lemma mod_add_mod (a c N : Nat) : ((a % N) + c) % N = (a + c) % N := by
  calc ((a % N) + c) % N = ((a % N) % N + c % N) % N := Nat.add_mod _ _ _
    _ = (a % N + c % N) % N := by rw [Nat.mod_mod]
    _ = (a + c) % N := (Nat.add_mod a c N).symm

lemma add_mod_self (x N : Nat) : (x + N) % N = x % N := by
  rw [Nat.add_mod]
  simp

lemma three_pow_mod_two (k : Nat) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]

/-! ### Theorem 2: multiplication by `2` preserves the count -/

/-- **Theorem 2a**: for `N` odd and `P` periodic with period `N`, the substitution
`q ↦ 2*q` preserves the number of hits. -/
lemma countBelow_two_mul_odd (N : Nat) (hN : N % 2 = 1) (P : Nat → Bool)
    (hP : ∀ x, P x = P (x % N)) :
    countBelow (fun q => P (2 * q)) N = countBelow P N := by
  rw [countBelow_eq_card, countBelow_eq_card]
  have hNpos : 0 < N := by omega
  have hdvd : 2 ∣ N + 1 := by
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hm : 2 * ((N + 1) / 2) = N + 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdvd
  have hinv : ∀ q < N, (((N + 1) / 2) * ((2 * q) % N)) % N = q := by
    intro q hq
    rw [mul_mod_mod]
    rw [show ((N + 1) / 2) * (2 * q) = (2 * ((N + 1) / 2)) * q by ring, hm]
    rw [show (N + 1) * q = q + q * N by ring, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hq]
  have hfwd : ∀ x < N, (2 * ((((N + 1) / 2) * x) % N)) % N = x := by
    intro x hx
    rw [mul_mod_mod]
    rw [show 2 * (((N + 1) / 2) * x) = (2 * ((N + 1) / 2)) * x by ring, hm]
    rw [show (N + 1) * x = x + x * N by ring, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hx]
  refine Finset.card_bij (fun q _ => (2 * q) % N) ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact ⟨Nat.mod_lt _ hNpos, by rw [← hP (2 * q)]; exact hq.2⟩
  · intro q1 hq1 q2 hq2 heq
    rw [Finset.mem_filter, Finset.mem_range] at hq1 hq2
    have h := congrArg (fun z => (((N + 1) / 2) * z) % N) heq
    rw [hinv q1 hq1.1, hinv q2 hq2.1] at h
    exact h
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    refine ⟨(((N + 1) / 2) * x) % N, ?_, hfwd x hx.1⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hNpos, ?_⟩
    rw [hP (2 * ((((N + 1) / 2) * x) % N)), hfwd x hx.1, hx.2]

/-- **Theorem 2b**: cyclic shift by one preserves the count for a periodic predicate. -/
lemma countBelow_shift (N : Nat) (hNpos : 0 < N) (P : Nat → Bool)
    (hP : ∀ x, P x = P (x % N)) :
    countBelow (fun x => P (x + 1)) N = countBelow P N := by
  have hinv : ∀ x < N, (((x + 1) % N) + (N - 1)) % N = x := by
    intro x hx
    rw [mod_add_mod]
    rw [show x + 1 + (N - 1) = x + N by omega]
    rw [add_mod_self, Nat.mod_eq_of_lt hx]
  have hfwd : ∀ x < N, (((x + (N - 1)) % N) + 1) % N = x := by
    intro x hx
    rw [mod_add_mod]
    rw [show x + (N - 1) + 1 = x + N by omega]
    rw [add_mod_self, Nat.mod_eq_of_lt hx]
  rw [countBelow_eq_card, countBelow_eq_card]
  refine Finset.card_bij (fun x _ => (x + 1) % N) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨Nat.mod_lt _ hNpos, by rw [← hP (x + 1)]; exact hx.2⟩
  · intro x1 hx1 x2 hx2 heq
    rw [Finset.mem_filter, Finset.mem_range] at hx1 hx2
    have h := congrArg (fun z => (z + (N - 1)) % N) heq
    rw [hinv x1 hx1.1, hinv x2 hx2.1] at h
    exact h
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    refine ⟨(x + (N - 1)) % N, ?_, hfwd x hx.1⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hNpos, ?_⟩
    rw [hP ((x + (N - 1)) % N + 1), hfwd x hx.1, hx.2]

/-- **Theorem 2c**: for `N` odd and `P` periodic with period `N`, the substitution
`q ↦ 2*q + 1` preserves the number of hits. -/
lemma countBelow_two_mul_add_one_odd (N : Nat) (hN : N % 2 = 1) (P : Nat → Bool)
    (hP : ∀ x, P x = P (x % N)) :
    countBelow (fun q => P (2 * q + 1)) N = countBelow P N := by
  have hNpos : 0 < N := by omega
  let P' : Nat → Bool := fun x => P (x + 1)
  have hP' : ∀ x, P' x = P' (x % N) := by
    intro x
    show P (x + 1) = P (x % N + 1)
    rw [hP (x + 1), hP (x % N + 1), mod_add_mod]
  have h1 : countBelow (fun q => P (2 * q + 1)) N = countBelow (fun q => P' (2 * q)) N := rfl
  rw [h1, countBelow_two_mul_odd N hN P' hP', countBelow_shift N hNpos P hP]

/-- **Theorem 2**: for `P` periodic with period `3^k`, `q ↦ 2*q` preserves the count. -/
theorem countBelow_two_mul (k : Nat) (P : Nat → Bool)
    (hP : ∀ x, P x = P (x % 3 ^ k)) :
    countBelow (fun q => P (2 * q)) (3 ^ k) = countBelow P (3 ^ k) :=
  countBelow_two_mul_odd (3 ^ k) (three_pow_mod_two k) P hP

/-- **Theorem 2**: for `P` periodic with period `3^k`, `q ↦ 2*q + 1` preserves the count. -/
theorem countBelow_two_mul_add_one (k : Nat) (P : Nat → Bool)
    (hP : ∀ x, P x = P (x % 3 ^ k)) :
    countBelow (fun q => P (2 * q + 1)) (3 ^ k) = countBelow P (3 ^ k) :=
  countBelow_two_mul_add_one_odd (3 ^ k) (three_pow_mod_two k) P hP

/-! ### Theorem 3: the recurrences for `A` and `B` -/

theorem A_zero : A 0 = 1 := by
  simp [A, countBelow, good11FreeAux]

theorem B_zero : B 0 = 1 := by
  simp [B, countBelow, good11FreeAux]

theorem A_succ (k : Nat) : A (k + 1) = A k + B k := by
  unfold A B
  rw [show 3 ^ (k + 1) = 3 * 3 ^ k by rw [pow_succ]; ring]
  conv_lhs => rw [countBelow_eq_sum, sum_range_three_mul]
  have hpt : ∀ q,
      (if good11FreeAux (k + 1) false (3 * q) = true then 1 else 0) +
        (if good11FreeAux (k + 1) false (3 * q + 1) = true then 1 else 0) +
        (if good11FreeAux (k + 1) false (3 * q + 2) = true then 1 else 0) =
      (if good11FreeAux k false (2 * q) = true then 1 else 0) +
        (if good11FreeAux k true (2 * q + 1) = true then 1 else 0) := by
    intro q
    rw [good11FreeAux_succ_three_mul, good11FreeAux_succ_three_mul_add_one,
      good11FreeAux_succ_three_mul_add_two_false]
    simp
  rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib,
    ← countBelow_eq_sum, ← countBelow_eq_sum]
  rw [countBelow_two_mul k (good11FreeAux k false) (good11FreeAux_mod k false),
    countBelow_two_mul_add_one k (good11FreeAux k true) (good11FreeAux_mod k true)]

theorem B_succ (k : Nat) : B (k + 1) = A k := by
  unfold A B
  rw [show 3 ^ (k + 1) = 3 * 3 ^ k by rw [pow_succ]; ring]
  conv_lhs => rw [countBelow_eq_sum, sum_range_three_mul]
  have hpt : ∀ q,
      (if good11FreeAux (k + 1) true (3 * q) = true then 1 else 0) +
        (if good11FreeAux (k + 1) true (3 * q + 1) = true then 1 else 0) +
        (if good11FreeAux (k + 1) true (3 * q + 2) = true then 1 else 0) =
      (if good11FreeAux k false (2 * q) = true then 1 else 0) := by
    intro q
    rw [good11FreeAux_succ_three_mul, good11FreeAux_succ_three_mul_add_one,
      good11FreeAux_succ_three_mul_add_two_true]
    simp
  rw [Finset.sum_congr rfl (fun q _ => hpt q), ← countBelow_eq_sum]
  rw [countBelow_two_mul k (good11FreeAux k false) (good11FreeAux_mod k false)]

/-! ### The closed Fibonacci count -/

lemma fib_AB : ∀ k, A k = fib (k + 2) ∧ B k = fib (k + 1) := by
  intro k
  induction k with
  | zero =>
    constructor
    · rw [A_zero]; norm_num [fib]
    · rw [B_zero]; norm_num [fib]
  | succ k ih =>
    obtain ⟨ha, hb⟩ := ih
    constructor
    · rw [A_succ, ha, hb]
      conv_rhs => rw [fib]
    · rw [B_succ, ha]

/-- **Main theorem**: exactly `fib (k+2)` classes in `[0, 3^k)` survive `k` reverse steps. -/
theorem fib_count (k : Nat) : countBelow (good11Free k) (3 ^ k) = fib (k + 2) := by
  change countBelow (good11FreeAux k false) (3 ^ k) = fib (k + 2)
  exact (fib_AB k).1

/-- The `k = 4` instance: `8` classes survive. -/
theorem survivors_four : countBelow (good11Free 4) (3 ^ 4) = 8 := by
  rw [fib_count]
  norm_num [fib]

end Mahler32.Fib11Free

end
