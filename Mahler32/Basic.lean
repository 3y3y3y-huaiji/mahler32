/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib

/-!
# The Mahler `3/2` recursion `a(n+1) = a n + ⌈a n / 2⌉`

`a` is OEIS A061419 (`a 0 = 1`).  This file records the exact arithmetic skeleton of the parity
problem `a n % 2`; every statement is a closed-form local law, proved with `omega` alone.

* `step_eq` : the ceiling-free form `step x = (3 * x + x % 2) / 2`;
* `step_parity` : `step x % 2 = x / 2 % 2`, i.e. the parity of the next term is the *second
  binary digit* of the current term.  This is the sharp reason why a base-`6` window propagates
  and a base-`3` window does not;
* `step_mod_three` : `step x % 3 = 2 * (x % 2)`, so the last ternary digit is `2 * (x % 2)` and
  is never `1`;
* `a_mod_six` : the last base-`6` digit is a bijective encoding of the pair of consecutive
  parities `(a (n+1) % 2, a n % 2)`, so it only takes the values `0, 2, 3, 5`;
* `step_parity_hex` : the base-`6` two-digit local law `b 0' = (t 0 + b 1) % 2`;
* `step_injective` : `step` is injective, so no information is lost;
* `step_shift` / `step_pow_shift` : adding a multiple of `2 ^ (j+1)` changes `step` by a multiple
  of `2 ^ j`, iterated `k` times with increment `2 ^ (m - k)` — the "one binary digit per step"
  law in exact form;
* `parity_window` / `parity_window_hex` / `a_parity_window` : `m` binary (equivalently `m`
  base-`6`) digits determine the next `m` parities;
* `cliff_sharp` : the window is sharp — `0` and `6 ^ m` agree on `m` base-`6` digits yet differ
  in parity at step `m`.
* `run_spec` / `ternary_machine` : the base-`3` two-state machine (append `x % 2`, then divide by
  `2` digit by digit with a carry in `{0, 1}`) computes `step x`;
* `good_card` : exactly `2 ^ k` legal residue classes modulo `3 ^ k`, via the bijection
  `x ↦ step^[k] x` from `{x < 2 ^ k}` onto `{y < 3 ^ k : good k y}`;
* `light_cone_flip_hex` / `parity_linear_split` : flipping bit `k` (or adding `6 ^ k`) always
  flips step-`k` parity, and `step^[k] x % 2` splits linearly on bit `k`;
* `bstep_mod_three_pow` / `good_mod_iff` : `bstep` and `good k` depend only on `y % 3 ^ k`;
* `good11Free_card` : `11`-free legal predecessors modulo `3 ^ k` count `Nat.fib (k + 2)`;
* `walsh_zero_of_bit_zero` / `walsh_eq_two_mul_core` : Walsh-Hadamard zero-correlation when the
  top bit of the mask is `0`, and factor-of-`2` reduction to `walshCore` when it is `1`.
-/

public section

namespace Mahler32

/-- `a n` is A061419: `a 0 = 1` and `a (n+1) = a n + ⌈a n / 2⌉`. -/
@[expose] public def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => a n + (a n + 1) / 2

/-- The step map `x ↦ x + ⌈x / 2⌉` of the recursion. -/
@[expose] public def step (x : ℕ) : ℕ := x + (x + 1) / 2

@[simp] lemma a_zero : a 0 = 1 := rfl

lemma step_eq_a (n : ℕ) : step (a n) = a (n + 1) := rfl

/-- The orbit is the orbit of `step`. -/
lemma a_add (n k : ℕ) : a (n + k) = step^[k] (a n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, ← step_eq_a, ih, Function.iterate_succ_apply']

/-- Splitting a natural number by parity. -/
lemma two_cases (n : ℕ) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := h
    exact Or.inl ⟨k, by ring⟩
  · obtain ⟨k, rfl⟩ := h
    exact Or.inr ⟨k, by ring⟩

/-- Ceiling-free form: `step x = ⌈3 * x / 2⌉ = (3 * x + x % 2) / 2`. -/
lemma step_eq (x : ℕ) : step x = (3 * x + x % 2) / 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

/-- The parity of the next term is the second binary digit of the current one. -/
theorem step_parity (x : ℕ) : step x % 2 = x / 2 % 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

/-- Doubling clears the ceiling: `2 * step z = 3 * z + z % 2`. -/
lemma two_mul_step (z : ℕ) : 2 * step z = 3 * z + z % 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases z <;> unfold step <;> omega

/-- The last ternary digit of the next term is `2 * (x % 2)`. -/
theorem step_mod_three (x : ℕ) : step x % 3 = 2 * (x % 2) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

/-- The base-`6` two-digit parity law: with `b j = d j % 2` and `t j = d j / 2`, the new least
significant bit is `(t 0 + b 1) % 2`. -/
theorem step_parity_hex (x : ℕ) : step x % 2 = ((x % 6) / 2 + x / 6 % 2) % 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

lemma a_succ_eq (n : ℕ) : a (n + 1) = (3 * a n + a n % 2) / 2 := step_eq (a n)

lemma a_succ_mod_three (n : ℕ) : a (n + 1) % 3 = 2 * (a n % 2) := step_mod_three (a n)

/-- The parity of `a (n+1)` is the second binary digit of `a n`. -/
theorem a_succ_parity (n : ℕ) : a (n + 1) % 2 = a n / 2 % 2 := step_parity (a n)

/-- No term with index `≥ 1` is `≡ 1 (mod 3)`. -/
theorem a_mod_three_ne_one {n : ℕ} (hn : 1 ≤ n) : a n % 3 ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ_mod_three]
  omega

/-- Every term is positive. -/
lemma a_pos (n : ℕ) : 0 < a n := by
  induction n with
  | zero => decide
  | succ n ih => rw [show a (n + 1) = step (a n) from rfl, step_eq]; omega

/-- The sequence is strictly increasing. -/
lemma a_lt_succ (n : ℕ) : a n < a (n + 1) := by
  have := a_pos n
  rw [show a (n + 1) = step (a n) from rfl, step_eq]
  omega

lemma a_mono : StrictMono a := strictMono_nat_of_lt_succ a_lt_succ

/-- The last base-`6` digit of `a (n+1)` is a bijective encoding of the pair of consecutive
parities `(a (n+1) % 2, a n % 2)`. -/
theorem a_mod_six (n : ℕ) : a (n + 1) % 6 = 3 * (a (n + 1) % 2) + 2 * (a n % 2) := by
  have h3 := a_succ_mod_three n
  have h2 : a (n + 1) % 6 % 2 = a (n + 1) % 2 := by omega
  have h1 : a (n + 1) % 6 % 3 = a (n + 1) % 3 := by omega
  omega

/-- Hence the last base-`6` digit never equals `1` or `4`. -/
theorem a_mod_six_mem (n : ℕ) : a (n + 1) % 6 = 0 ∨ a (n + 1) % 6 = 2 ∨
    a (n + 1) % 6 = 3 ∨ a (n + 1) % 6 = 5 := by
  have h := a_mod_six n
  have hp : a (n + 1) % 2 = 0 ∨ a (n + 1) % 2 = 1 := by omega
  have hq : a n % 2 = 0 ∨ a n % 2 = 1 := by omega
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> omega

/-- The step map is injective: the recursion is reversible. -/
theorem step_injective {x y : ℕ} (h : step x = step y) : x = y := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;>
    obtain ⟨l, rfl⟩ | ⟨l, rfl⟩ := two_cases y <;> unfold step at h <;> omega

/-! ### The ternary two-state machine

Read the base-`3` digits of `x` most significant first, append `w = x % 2`, and divide by `2`
digit by digit with a carry in `{0, 1}`:

`val = 3 * carry + d`, output `val / 2`, new carry `val % 2`.

This is exactly the transducer of the problem statement; `ternary_machine` says it computes
`step x`.  Note that no bound on the digits is needed — the invariant is pure algebra. -/

/-- Value of a most-significant-digit-first digit list in base `3`. -/
@[expose] public def val : List ℕ → ℕ
  | [] => 0
  | d :: ds => d * 3 ^ ds.length + val ds

@[simp] lemma val_nil : val [] = 0 := rfl

lemma val_cons (d : ℕ) (ds : List ℕ) : val (d :: ds) = d * 3 ^ ds.length + val ds := rfl

lemma val_append_singleton (L : List ℕ) (d : ℕ) : val (L ++ [d]) = val L * 3 + d := by
  induction L with
  | nil => simp [val]
  | cons e es ih =>
    rw [List.cons_append, val_cons, ih, val_cons]
    have h : 3 ^ (es ++ [d]).length = 3 ^ es.length * 3 := by
      rw [List.length_append, List.length_singleton, pow_succ]
    rw [h]
    ring

lemma val_reverse_eq_ofDigits (L : List ℕ) : val L.reverse = Nat.ofDigits 3 L := by
  induction L with
  | nil => simp
  | cons d ds ih =>
    rw [List.reverse_cons, val_append_singleton, ih, Nat.ofDigits_cons]
    omega

/-- The MSB-first digit list of `x` evaluates back to `x`. -/
lemma val_digits (x : ℕ) : val (Nat.digits 3 x).reverse = x := by
  rw [val_reverse_eq_ofDigits, Nat.ofDigits_digits]

/-- Quotient digits produced by the scan. -/
@[expose] public def runOut : List ℕ → ℕ → List ℕ
  | [], _ => []
  | d :: ds, r => (3 * r + d) / 2 :: runOut ds ((3 * r + d) % 2)

/-- Final carry of the scan. -/
@[expose] public def runRem : List ℕ → ℕ → ℕ
  | [], r => r
  | d :: ds, r => runRem ds ((3 * r + d) % 2)

lemma runOut_length (L : List ℕ) (r : ℕ) : (runOut L r).length = L.length := by
  induction L generalizing r with
  | nil => rfl
  | cons d ds ih => simp [runOut, ih]

lemma runRem_lt_two (L : List ℕ) (r : ℕ) (hr : r < 2) : runRem L r < 2 := by
  induction L generalizing r with
  | nil => simpa [runRem] using hr
  | cons d ds ih =>
    simp only [runRem]
    exact ih _ (by omega)

/-- Long-division invariant: the emitted digits and the final carry reconstruct `3 ^ |L| * r +
val L`. -/
theorem run_spec (L : List ℕ) (r : ℕ) :
    2 * val (runOut L r) + runRem L r = r * 3 ^ L.length + val L := by
  induction L generalizing r with
  | nil => simp [runOut, runRem, val]
  | cons d ds ih =>
    have h2 : 2 * ((3 * r + d) / 2) + (3 * r + d) % 2 = 3 * r + d := by omega
    calc 2 * val (runOut (d :: ds) r) + runRem (d :: ds) r
        = 2 * (((3 * r + d) / 2) * 3 ^ ds.length + val (runOut ds ((3 * r + d) % 2)))
            + runRem ds ((3 * r + d) % 2) := by
          simp only [runOut, runRem, val_cons, runOut_length]
      _ = 2 * ((3 * r + d) / 2) * 3 ^ ds.length
            + (2 * val (runOut ds ((3 * r + d) % 2)) + runRem ds ((3 * r + d) % 2)) := by
          ring
      _ = 2 * ((3 * r + d) / 2) * 3 ^ ds.length
            + ((3 * r + d) % 2 * 3 ^ ds.length + val ds) := by
          rw [ih]
      _ = (2 * ((3 * r + d) / 2) + (3 * r + d) % 2) * 3 ^ ds.length + val ds := by
          ring
      _ = (3 * r + d) * 3 ^ ds.length + val ds := by rw [h2]
      _ = r * 3 ^ (d :: ds).length + val (d :: ds) := by
          rw [val_cons, List.length_cons, pow_succ]
          ring

/-- **The two-state machine computes `step`.**  Appending the parity digit and running the
divide-by-`2` scan over the base-`3` digits reproduces `⌈3x/2⌉`. -/
theorem ternary_machine (x : ℕ) :
    val (runOut ((Nat.digits 3 x).reverse ++ [x % 2]) 0) = step x := by
  have hspec := run_spec ((Nat.digits 3 x).reverse ++ [x % 2]) 0
  have hval : val ((Nat.digits 3 x).reverse ++ [x % 2]) = 3 * x + x % 2 := by
    rw [val_append_singleton, val_digits]
    omega
  have hrem := runRem_lt_two ((Nat.digits 3 x).reverse ++ [x % 2]) 0 (by norm_num)
  have hstep := two_mul_step x
  rw [hval, Nat.zero_mul, Nat.zero_add] at hspec
  omega

/-! ### The information window (the "cliff")

Each iteration spends exactly one binary digit: `step x` is determined modulo `2 ^ j` by `x`
modulo `2 ^ (j+1)`, so `m` binary digits buy exactly `m` future parities and not one more.
The two theorems `parity_window_hex` and `cliff_sharp` are the two halves of that statement. -/

/-- Adding a multiple of `2 ^ (j+1)` changes `step` by a multiple of `2 ^ j`, explicitly. -/
theorem step_shift (j t x : ℕ) :
    step (x + 2 ^ (j + 1) * t) = step x + 2 ^ j * (3 * t) := by
  have h2 : (x + 2 ^ (j + 1) * t) % 2 = x % 2 := by
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ (j + 1) * t = 2 * s := ⟨2 ^ j * t, by rw [pow_succ]; ring⟩
    rw [hs]
    omega
  have key : 2 * step (x + 2 ^ (j + 1) * t) = 2 * (step x + 2 ^ j * (3 * t)) := by
    have hexp : 2 * (step x + 2 ^ j * (3 * t)) = 2 * step x + 2 * (2 ^ j * (3 * t)) := by
      ring
    rw [hexp, two_mul_step, two_mul_step, h2]
    simp only [pow_succ]
    ring
  exact Nat.mul_left_cancel (n := 2) (by norm_num) key

/-- Iterated form: after `k` steps the increment is `2 ^ (m - k)` times an integer. -/
theorem step_pow_shift (m k : ℕ) (hk : k ≤ m) (t x : ℕ) :
    step^[k] (x + 2 ^ m * t) = step^[k] x + 2 ^ (m - k) * (3 ^ k * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ m := by omega
    have hlt : k < m := by omega
    rw [Function.iterate_succ_apply', ih hk', Function.iterate_succ_apply']
    have hshift := step_shift (m - k - 1) (3 ^ k * t) (step^[k] x)
    rw [show m - k - 1 + 1 = m - k from by omega] at hshift
    rw [hshift, show m - k - 1 = m - (k + 1) from by omega, pow_succ]
    ring

/-- `m` binary digits determine the next `m` parities. -/
theorem parity_window (m k t x : ℕ) (hk : k < m) :
    (step^[k] (x + 2 ^ m * t)) % 2 = (step^[k] x) % 2 := by
  rw [step_pow_shift m k (by omega) t x]
  obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
  have hcomm : 2 ^ (m - k) * (3 ^ k * t) = (2 ^ d * (3 ^ k * t)) * 2 := by
    rw [hd, pow_succ]
    ring
  rw [hcomm, Nat.add_mul_mod_self_right]

/-- `m` base-`6` digits determine the next `m` parities (one digit carries one binary digit). -/
theorem parity_window_hex (m k t x : ℕ) (hk : k < m) :
    (step^[k] (x + 6 ^ m * t)) % 2 = (step^[k] x) % 2 := by
  have h : 6 ^ m * t = 2 ^ m * (3 ^ m * t) := by
    rw [show (6 : ℕ) = 2 * 3 from by norm_num, mul_pow]
    ring
  rw [h]
  exact parity_window m k (3 ^ m * t) x hk

/-- Sequence form: any number congruent to `a n` modulo `6 ^ m` produces the same next `m`
parities as the true orbit does. -/
theorem a_parity_window (m k t n : ℕ) (hk : k < m) :
    a (n + k) % 2 = (step^[k] (a n + 6 ^ m * t)) % 2 := by
  rw [a_add, parity_window_hex m k t (a n) hk]

lemma step_two_pow_mul (j c : ℕ) : step (2 ^ (j + 1) * c) = 3 * (2 ^ j * c) := by
  have h : 2 ^ (j + 1) * c = 2 * (2 ^ j * c) := by rw [pow_succ]; ring
  rw [h]
  unfold step
  have hdiv : (2 * (2 ^ j * c) + 1) / 2 = 2 ^ j * c := by omega
  rw [hdiv]
  ring

/-- The orbit of `6 ^ m` sits exactly on the boundary: after `m` exact halvings it is the odd
number `3 ^ m * 3 ^ m`. -/
theorem step_pow_six (m k : ℕ) (hk : k ≤ m) :
    step^[k] (6 ^ m) = 3 ^ k * (2 ^ (m - k) * 3 ^ m) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, one_mul, Nat.sub_zero]
    rw [show (6 : ℕ) = 2 * 3 from by norm_num, mul_pow]
  | succ k ih =>
    have hk' : k ≤ m := by omega
    have hlt : k < m := by omega
    rw [Function.iterate_succ_apply', ih hk']
    obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
    have hsplit : 3 ^ k * (2 ^ (m - k) * 3 ^ m) = 2 ^ (d + 1) * (3 ^ k * 3 ^ m) := by
      rw [← hd]
      ring
    rw [hsplit, step_two_pow_mul, show d = m - (k + 1) from by omega, pow_succ]
    ring

/-- Powers of `3` are odd. -/
lemma three_pow_mod_two (k : ℕ) : (3 : ℕ) ^ k % 2 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

/-- The window is sharp: two numbers agreeing on `m` base-`6` digits can still differ in parity
at step `m` (`0` versus `6 ^ m`). -/
theorem cliff_sharp (m : ℕ) :
    ∃ x y : ℕ, x % 6 ^ m = y % 6 ^ m ∧ (step^[m] x) % 2 ≠ (step^[m] y) % 2 := by
  refine ⟨0, 6 ^ m, by simp, ?_⟩
  have hzero : step^[m] 0 = 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih]; simp [step]
  have hsix := step_pow_six m m le_rfl
  have h3 := three_pow_mod_two m
  rw [hzero, hsix, show m - m = 0 from by omega, pow_zero, one_mul, Nat.mul_mod, h3]
  norm_num

/-! ### Period doubling

Scanning a block `B` twice, the carry after the first copy is `r + ones B` (mod `2`): the parity
of the number of odd digits is exactly the affine part of the state map.  So

* odd `ones B`  : the carry flips, the two output blocks differ, and `|B|` is **not** a period
  of the two-block output — the period strictly doubles to `2 * |B|`;
* even `ones B` : the carry returns, the two output blocks coincide, so `|B|` survives.
-/

/-- Number of odd digits of a digit list. -/
@[expose] public def ones (L : List ℕ) : ℕ := (L.map (fun d => d % 2)).sum

@[simp] lemma ones_nil : ones [] = 0 := rfl

lemma ones_cons (d : ℕ) (ds : List ℕ) : ones (d :: ds) = d % 2 + ones ds := rfl

/-- **One-period state transition**: the carry after a block is `r + ones B` mod `2`. -/
theorem runRem_eq (L : List ℕ) (r : ℕ) (hr : r < 2) : runRem L r = (r + ones L) % 2 := by
  induction L generalizing r with
  | nil => simp [runRem, ones]; omega
  | cons d ds ih =>
    rw [runRem, ones_cons, ih ((3 * r + d) % 2) (by omega)]
    have hstep : (3 * r + d) % 2 = (r + d % 2) % 2 := by omega
    rw [hstep]
    omega

/-- The scan is a monoid homomorphism on concatenation, with the carry threaded through. -/
theorem runOut_append (L₁ L₂ : List ℕ) (r : ℕ) :
    runOut (L₁ ++ L₂) r = runOut L₁ r ++ runOut L₂ (runRem L₁ r) := by
  induction L₁ generalizing r with
  | nil => simp [runOut, runRem]
  | cons d ds ih => simp only [List.cons_append, runOut, runRem, ih]

/-- Two copies of a block: the second copy starts from the carry `(r + ones B) % 2`. -/
theorem runOut_two_blocks (B : List ℕ) (r : ℕ) (hr : r < 2) :
    runOut (B ++ B) r = runOut B r ++ runOut B ((r + ones B) % 2) := by
  rw [runOut_append, runRem_eq B r hr]

/-- Odd number of odd digits: the carry flips. -/
theorem runOut_two_blocks_odd (B : List ℕ) (hodd : ones B % 2 = 1) (r : ℕ) (hr : r < 2) :
    runOut (B ++ B) r = runOut B r ++ runOut B (1 - r) := by
  rw [runOut_two_blocks B r hr]
  have h : (r + ones B) % 2 = 1 - r := by omega
  rw [h]

/-- Even number of odd digits: the carry returns, so the block repeats. -/
theorem runOut_two_blocks_even (B : List ℕ) (heven : ones B % 2 = 0) (r : ℕ) (hr : r < 2) :
    runOut (B ++ B) r = runOut B r ++ runOut B r := by
  rw [runOut_two_blocks B r hr]
  have h : (r + ones B) % 2 = r := by omega
  rw [h]

/-- The two output blocks differ in their first digit, because the incoming carries differ. -/
theorem runOut_blocks_ne (B : List ℕ) (hd : ∀ d ∈ B, d < 3) (hB : B ≠ []) (r : ℕ) (hr : r < 2) :
    runOut B r ≠ runOut B (1 - r) := by
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, B = d :: ds := by
    cases B with
    | nil => exact absurd rfl hB
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hd3 : d < 3 := hd d (by simp)
  simp only [runOut]
  intro hcons
  have := List.cons.inj hcons
  omega

/-- **Period doubling (odd case).**  For a block with an odd number of odd digits, the scan of
`B ++ B` has the two halves different, i.e. `|B|` is not a period: the period doubles. -/
theorem period_doubling (B : List ℕ) (hd : ∀ d ∈ B, d < 3) (hB : B ≠ [])
    (hodd : ones B % 2 = 1) (r : ℕ) (hr : r < 2) :
    (runOut (B ++ B) r).take B.length ≠ (runOut (B ++ B) r).drop B.length := by
  rw [runOut_two_blocks_odd B hodd r hr, ← runOut_length B r, List.take_left, List.drop_left]
  exact runOut_blocks_ne B hd hB r hr

/-- **No doubling (even case).**  For a block with an even number of odd digits, the two halves
of the scan of `B ++ B` coincide, so `|B|` remains a period. -/
theorem period_persists (B : List ℕ) (heven : ones B % 2 = 0) (r : ℕ) (hr : r < 2) :
    (runOut (B ++ B) r).take B.length = (runOut (B ++ B) r).drop B.length := by
  rw [runOut_two_blocks_even B heven r hr, ← runOut_length B r, List.take_left, List.drop_left]


/-! ### The inverse branch and legal predecessors

`bstep y = (2y - 2y % 3) / 3` undoes one step: it is the base-`3` "shift the digits right" rule,
defined exactly when `y ≢ 1 (mod 3)`.  Being a *local* rule, it contracts `3`-adically, so the
`k`-fold predecessors of a point form `2 ^ k` residue classes modulo `3 ^ k` — one per history of
parity digits. -/

/-- Inverse branch of `step`: undo one base-`3` digit. -/
@[expose] public def bstep (y : ℕ) : ℕ := (2 * y - 2 * y % 3) / 3

/-- Clearing the division: `3 * bstep y + 2y % 3 = 2y`. -/
lemma bstep_mul (y : ℕ) : 3 * bstep y + 2 * y % 3 = 2 * y := by
  have hmod : (2 * y - 2 * y % 3) % 3 = 0 := by omega
  have hd := Nat.div_add_mod (2 * y - 2 * y % 3) 3
  rw [hmod, Nat.add_zero] at hd
  unfold bstep
  omega

/-- The digit emitted by the inverse branch is `2y % 3`, and it is `0` or `1`. -/
lemma bstep_parity (y : ℕ) (h : y % 3 ≠ 1) : bstep y % 2 = 2 * y % 3 := by
  have hc : 2 * y % 3 < 2 := by omega
  have hm := bstep_mul y
  omega

/-- The inverse branch and the step map are mutually inverse (where defined). -/
theorem step_bstep (y : ℕ) (h : y % 3 ≠ 1) : step (bstep y) = y := by
  have hc : 2 * y % 3 < 2 := by omega
  have hm := bstep_mul y
  rw [step_eq]
  omega

/-- One step followed by one inverse step returns. -/
theorem bstep_step (x : ℕ) : bstep (step x) = x := by
  have hstep := two_mul_step x
  have hpar : 2 * step x % 3 = x % 2 := by omega
  have hm := bstep_mul (step x)
  rw [hpar] at hm
  omega

/-- `k` inverse steps undo `k` steps. -/
theorem bstep_pow_step (k : ℕ) (x : ℕ) : bstep^[k] (step^[k] x) = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', bstep_step]
    exact ih

/-- The legality predicate: the first `k` inverse steps never hit `≡ 1 (mod 3)`. -/
@[expose] public def good (k y : ℕ) : Prop := ∀ j, j < k → (bstep^[j] y) % 3 ≠ 1

lemma good.zero (y : ℕ) : good 0 y := fun j hj => absurd hj (Nat.not_lt_zero j)

lemma good.succ {k y : ℕ} (h : good (k + 1) y) : y % 3 ≠ 1 ∧ good k (bstep y) := by
  refine ⟨h 0 (by omega), fun j hj => ?_⟩
  have := h (j + 1) (by omega)
  rwa [Function.iterate_succ_apply] at this

/-- `k` inverse steps invert `k` steps, provided the path stays legal. -/
theorem step_pow_bstep : ∀ k y : ℕ, good k y → step^[k] (bstep^[k] y) = y
  | 0, y, _ => by simp
  | k + 1, y, h => by
    obtain ⟨h0, hk⟩ := good.succ h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply,
      step_pow_bstep k (bstep y) hk, step_bstep y h0]


/-! ### The `2 ^ k` legal residue classes

`step` is strictly monotone, and `k` steps map the window boundary `2 ^ k` exactly onto
`3 ^ k`.  Hence `x ↦ step^[k] x` is a bijection from `{x < 2 ^ k}` onto the legal set
`{y < 3 ^ k : good k y}`, whose cardinality is therefore `2 ^ k`: one class per history. -/

/-- `step` increases strictly. -/
theorem step_lt_succ (n : ℕ) : step n < step (n + 1) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases n <;> unfold step <;> omega

theorem step_strictMono : StrictMono step := strictMono_nat_of_lt_succ step_lt_succ

theorem step_pow_strictMono (k : ℕ) : StrictMono (step^[k]) := step_strictMono.iterate k

lemma step_pow_zero (k : ℕ) : step^[k] 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih]; simp [step]

/-- `k` steps carry the window boundary `2 ^ k` onto `3 ^ k`. -/
theorem step_pow_two_pow (k : ℕ) : step^[k] (2 ^ k) = 3 ^ k := by
  have h := step_pow_shift k k le_rfl 1 0
  simpa [step_pow_zero] using h

/-- A positive iterate of `step` is never `≡ 1 (mod 3)`. -/
lemma step_pow_mod_three_ne_one {n : ℕ} (hn : 0 < n) (x : ℕ) : step^[n] x % 3 ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply', step_mod_three]
  omega

/-- Every point of the `k`-th image is legal. -/
theorem good_step_pow (k x : ℕ) : good k (step^[k] x) := by
  intro j hj
  have hjk : j ≤ k := by omega
  have hsplit : step^[k] x = step^[j] (step^[k - j] x) := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hjk]
  rw [hsplit, bstep_pow_step]
  exact step_pow_mod_three_ne_one (by omega) x

public instance decidableGood (k : ℕ) : DecidablePred (good k) := fun y =>
  Nat.decidableBallLT k (fun j _ => (bstep^[j] y) % 3 ≠ 1)

/-- **The `2 ^ k` legal classes.**  The `k`-th iterate of `step` is a bijection from
`{x < 2 ^ k}` onto `{y < 3 ^ k : good k y}`. -/
theorem good_card (k : ℕ) :
    ((Finset.range (3 ^ k)).filter (fun y => good k y)).card = 2 ^ k := by
  have hbij : (Finset.range (2 ^ k)).card =
      ((Finset.range (3 ^ k)).filter (fun y => good k y)).card := by
    refine Finset.card_bij (fun x _ => step^[k] x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      refine ⟨?_, good_step_pow k x⟩
      rw [← step_pow_two_pow k]
      exact (step_pow_strictMono k).lt_iff_lt.mpr hx
    · intro x₁ _ x₂ _ h
      exact (step_pow_strictMono k).injective h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨hy3, hyg⟩ := hy
      refine ⟨bstep^[k] y, ?_, step_pow_bstep k y hyg⟩
      rw [Finset.mem_range, ← (step_pow_strictMono k).lt_iff_lt, step_pow_bstep k y hyg,
        step_pow_two_pow]
      exact hy3
  rw [← hbij, Finset.card_range]


/-! ### Light-cone flip and linear splitting

Flipping bit `k` of `x` (`x ↦ x + 2 ^ k`) adds `3 ^ k` after `k` steps, which is odd, so parity
always flips.  In base `6`, adding `6 ^ k` shifts by `9 ^ k`, flipping parity at step `k`.
Algebraically, `step^[k] x % 2` separates linearly as
`((step^[k] (x % 2 ^ k)) % 2 + (x / 2 ^ k) % 2) % 2`. -/

/-- Shifting by `2 ^ k` shifts `step^[k]` by `3 ^ k`. -/
theorem step_pow_add_two_pow (k x : ℕ) : step^[k] (x + 2 ^ k) = step^[k] x + 3 ^ k := by
  simpa using step_pow_shift k k le_rfl 1 x

/-- Shifting by `6 ^ k` shifts `step^[k]` by `9 ^ k` (base-`6` light-cone growth). -/
theorem step_pow_add_six_pow (k x : ℕ) : step^[k] (x + 6 ^ k) = step^[k] x + 9 ^ k := by
  have h6 : 6 ^ k = 2 ^ k * 3 ^ k := by
    rw [show (6 : ℕ) = 2 * 3 from by norm_num, mul_pow]
  have h9 : 3 ^ k * 3 ^ k = 9 ^ k := by
    rw [← mul_pow]
    norm_num
  simpa [h6, h9] using step_pow_shift k k le_rfl (3 ^ k) x

/-- Flipping bit `k` always flips the parity after `k` steps. -/
theorem step_pow_add_two_pow_parity (k x : ℕ) :
    (step^[k] (x + 2 ^ k)) % 2 = 1 - (step^[k] x) % 2 := by
  rw [step_pow_add_two_pow]
  have h3 := three_pow_mod_two k
  omega

/-- **Hexadecimal light-cone flip**: adding `6 ^ k` always flips the parity at step `k`. -/
theorem light_cone_flip_hex (k x : ℕ) :
    (step^[k] (x + 6 ^ k)) % 2 ≠ (step^[k] x) % 2 := by
  rw [step_pow_add_six_pow]
  have h9 : 9 ^ k % 2 = 1 := by
    have h3 := three_pow_mod_two k
    rw [show (9 : ℕ) = 3 * 3 from by norm_num, mul_pow, Nat.mul_mod, h3]
  omega

/-- **`F₂` linear splitting**: `step^[k] x % 2` separates linearly on bit `k`
(`(x / 2 ^ k) % 2`) and a nonlinear core depending only on `x % 2 ^ k`. -/
theorem parity_linear_split (k x : ℕ) :
    (step^[k] x) % 2 = ((step^[k] (x % 2 ^ k)) % 2 + (x / 2 ^ k) % 2) % 2 := by
  have hsplit : x = x % 2 ^ k + 2 ^ k * (x / 2 ^ k) := (Nat.mod_add_div x (2 ^ k)).symm
  conv_lhs => rw [hsplit, step_pow_shift k k le_rfl (x / 2 ^ k) (x % 2 ^ k)]
  have h3 := three_pow_mod_two k
  simp only [Nat.sub_self, pow_zero, one_mul]
  rw [Nat.add_mod, Nat.mul_mod, h3]
  omega


/-! ### The 3-adic backward window

Adding a multiple of `3 ^ (j + 1)` to `y` changes `bstep y` by a multiple of `3 ^ j`.
Consequently, `bstep` depends locally on `y % 3 ^ (j + 1)`, and `good k y` depends only on
`y % 3 ^ k`. -/

/-- Adding a multiple of `3 ^ (j + 1)` shifts `bstep` by `3 ^ j * (2 * t)`. -/
theorem bstep_add_three_pow (j t y : ℕ) :
    bstep (y + 3 ^ (j + 1) * t) = bstep y + 3 ^ j * (2 * t) := by
  have h3 : 3 ^ (j + 1) * t = 3 * (3 ^ j * t) := by rw [pow_succ]; ring
  have hmod : 2 * (y + 3 ^ (j + 1) * t) % 3 = 2 * y % 3 := by rw [h3]; omega
  have hmul : 2 * (y + 3 ^ (j + 1) * t) = 2 * y + 3 * (3 ^ j * (2 * t)) := by
    rw [h3]
    ring
  have hm1 := bstep_mul (y + 3 ^ (j + 1) * t)
  have hm2 := bstep_mul y
  rw [hmod, hmul] at hm1
  omega

/-- Local symmetry window for `bstep`: `bstep y % 3 ^ j` depends only on `y % 3 ^ (j + 1)`. -/
theorem bstep_mod_three_pow (j y : ℕ) :
    bstep y % 3 ^ j = bstep (y % 3 ^ (j + 1)) % 3 ^ j := by
  conv_lhs => rw [← Nat.mod_add_div y (3 ^ (j + 1))]
  rw [bstep_add_three_pow, Nat.add_mul_mod_self_left]

/-- Iterated `3`-adic shift of `bstep`. -/
theorem bstep_pow_add_three_pow (m k : ℕ) (hk : k ≤ m) (t y : ℕ) :
    bstep^[k] (y + 3 ^ m * t) = bstep^[k] y + 3 ^ (m - k) * (2 ^ k * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ m := by omega
    rw [Function.iterate_succ_apply', ih hk', Function.iterate_succ_apply']
    have hshift := bstep_add_three_pow (m - k - 1) (2 ^ k * t) (bstep^[k] y)
    obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
    have hd' : d = m - (k + 1) := by omega
    rw [show m - k - 1 = d from by omega] at hshift
    rw [hd, hshift, hd', pow_succ]
    ring

/-- The first `k` digits emitted by `bstep` are invariant under shifts by `3 ^ k`. -/
lemma bstep_pow_mod_three_of_lt {k j : ℕ} (hj : j < k) (t y : ℕ) :
    (bstep^[j] (y + 3 ^ k * t)) % 3 = (bstep^[j] y) % 3 := by
  rw [bstep_pow_add_three_pow k j (by omega) t y]
  obtain ⟨d, hd⟩ : ∃ d, k - j = d + 1 := ⟨k - j - 1, by omega⟩
  have hcomm : 3 ^ (k - j) * (2 ^ j * t) = (3 ^ d * (2 ^ j * t)) * 3 := by
    rw [hd, pow_succ]
    ring
  rw [hcomm, Nat.add_mul_mod_self_right]

/-- Shifting by `3 ^ k` preserves `k`-step legality. -/
theorem good_add_three_pow (k t y : ℕ) : good k (y + 3 ^ k * t) ↔ good k y := by
  constructor
  · intro h j hj
    have hmod := bstep_pow_mod_three_of_lt hj t y
    exact hmod ▸ h j hj
  · intro h j hj
    have hmod := bstep_pow_mod_three_of_lt hj t y
    exact hmod.symm ▸ h j hj

/-- Legality for `k` backward steps depends only on `y % 3 ^ k`. -/
theorem good_mod_iff (k y : ℕ) : good k y ↔ good k (y % 3 ^ k) := by
  conv_lhs => rw [← Nat.mod_add_div y (3 ^ k)]
  exact good_add_three_pow k (y / 3 ^ k) (y % 3 ^ k)


/-! ### 11-free backward pruning and Fibonacci count

Imposing the Mahler Z-number `11`-free condition (forbidding two consecutive odd backward steps,
i.e., two consecutive `≡ 2 (mod 3)` steps) reduces the surviving residue classes modulo `3 ^ k`
from `2 ^ k` to the Fibonacci number `Nat.fib (k + 2)`. -/

/-- `y` has a legal `k`-step backward orbit with no two consecutive odd outputs (`11`-free). -/
@[expose] public def good11Free (k y : ℕ) : Prop :=
  good k y ∧ ∀ j, j < k - 1 → ¬ ((bstep^[j] y) % 3 = 2 ∧ (bstep^[j + 1] y) % 3 = 2)

public instance decidableGood11Free (k : ℕ) : DecidablePred (good11Free k) := fun y =>
  @instDecidableAnd _ _ (decidableGood k y)
    (Nat.decidableBallLT (k - 1)
      (fun j _ => ¬ ((bstep^[j] y) % 3 = 2 ∧ (bstep^[j + 1] y) % 3 = 2)))

/-- Shifting by `3 ^ k` preserves the `k`-step `11`-free condition. -/
theorem good11Free_add_three_pow (k t y : ℕ) :
    good11Free k (y + 3 ^ k * t) ↔ good11Free k y := by
  unfold good11Free
  rw [good_add_three_pow]
  refine and_congr_right fun _ => ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · have h1 := bstep_pow_mod_three_of_lt (by omega : j < k) t y
    have h2 := bstep_pow_mod_three_of_lt (by omega : j + 1 < k) t y
    have := h j hj
    rwa [h1, h2] at this
  · have h1 := bstep_pow_mod_three_of_lt (by omega : j < k) t y
    have h2 := bstep_pow_mod_three_of_lt (by omega : j + 1 < k) t y
    have := h j hj
    rwa [← h1, ← h2] at this

/-- `11`-free legality for `k` backward steps depends only on `y % 3 ^ k`. -/
theorem good11Free_mod_iff (k y : ℕ) : good11Free k y ↔ good11Free k (y % 3 ^ k) := by
  conv_lhs => rw [← Nat.mod_add_div y (3 ^ k)]
  exact good11Free_add_three_pow k (y / 3 ^ k) (y % 3 ^ k)

lemma bstep_three_mul (q : ℕ) : bstep (3 * q) = 2 * q := by
  have hm := bstep_mul (3 * q)
  omega

lemma bstep_three_mul_add_two (q : ℕ) : bstep (3 * q + 2) = 2 * q + 1 := by
  have hm := bstep_mul (3 * q + 2)
  omega

lemma good11Free_succ_of_mod_three_eq_zero {k y : ℕ} (h0 : y % 3 = 0) :
    good11Free (k + 1) y ↔ good11Free k (bstep y) := by
  constructor
  · rintro ⟨hg, h11⟩
    refine ⟨(good.succ hg).2, fun j hj => ?_⟩
    have := h11 (j + 1) (by omega)
    simpa [Function.iterate_succ_apply] using this
  · rintro ⟨hg, h11⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero => simp [h0]
      | succ j =>
        rw [Function.iterate_succ_apply]
        exact hg j (by omega)
    · cases j with
      | zero => simp [h0]
      | succ j =>
        have := h11 j (by omega)
        simpa [Function.iterate_succ_apply] using this

lemma good11Free_succ_succ_of_mod_three_eq_two {k y : ℕ} (h2 : y % 3 = 2) :
    good11Free (k + 2) y ↔ good11Free (k + 1) (bstep y) ∧ (bstep y) % 3 = 0 := by
  constructor
  · rintro ⟨hg, h11⟩
    have hsucc := (good.succ hg).2
    have hb1 : (bstep y) % 3 ≠ 1 := (good.succ hsucc).1
    have h0 := h11 0 (by omega)
    simp only [Function.iterate_zero_apply, Nat.zero_add, Function.iterate_one, h2,
      true_and] at h0
    refine ⟨⟨hsucc, fun j hj => ?_⟩, by omega⟩
    have := h11 (j + 1) (by omega)
    simpa [Function.iterate_succ_apply] using this
  · rintro ⟨⟨hg, h11⟩, hb0⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero => simp [h2]
      | succ j =>
        rw [Function.iterate_succ_apply]
        exact hg j (by omega)
    · cases j with
      | zero => simp [hb0]
      | succ j =>
        have := h11 j (by omega)
        simpa [Function.iterate_succ_apply] using this

lemma eq_of_add_mod_two_eq {q₁ q₂ r : ℕ} (h1 : q₁ < 2) (h2 : q₂ < 2)
    (heq : (q₁ + r) % 2 = (q₂ + r) % 2) : q₁ = q₂ := by
  omega

lemma eq_of_mod_three_pow_eq_of_lt {m a₁ a₂ : ℕ} (ha1 : a₁ < 2 * 3 ^ m) (ha2 : a₂ < 2 * 3 ^ m)
    (hpar : a₁ % 2 = a₂ % 2) (hmod : a₁ % 3 ^ m = a₂ % 3 ^ m) : a₁ = a₂ := by
  have hpow : 0 < 3 ^ m := pow_pos (by norm_num) m
  have hq1 : a₁ / 3 ^ m < 2 := by rw [Nat.div_lt_iff_lt_mul hpow]; omega
  have hq2 : a₂ / 3 ^ m < 2 := by rw [Nat.div_lt_iff_lt_mul hpow]; omega
  have h3mod : 3 ^ m % 2 = 1 := three_pow_mod_two m
  have hp1 : (a₁ / 3 ^ m + a₁ % 3 ^ m) % 2 = a₁ % 2 := by
    have hdm := congrArg (· % 2) (Nat.div_add_mod a₁ (3 ^ m))
    rw [Nat.add_mod, Nat.mul_mod, h3mod] at hdm
    omega
  have hp2 : (a₂ / 3 ^ m + a₂ % 3 ^ m) % 2 = a₂ % 2 := by
    have hdm := congrArg (· % 2) (Nat.div_add_mod a₂ (3 ^ m))
    rw [Nat.add_mod, Nat.mul_mod, h3mod] at hdm
    omega
  rw [hmod, hpar] at hp1
  have hqeq : a₁ / 3 ^ m = a₂ / 3 ^ m := eq_of_add_mod_two_eq hq1 hq2 (hp1.trans hp2.symm)
  rw [← Nat.div_add_mod a₁ (3 ^ m), ← Nat.div_add_mod a₂ (3 ^ m), hqeq, hmod]

lemma card_good11Free_mod_zero (k : ℕ) :
    ((Finset.range (3 ^ (k + 1))).filter (fun y => good11Free (k + 1) y ∧ y % 3 = 0)).card =
      ((Finset.range (3 ^ k)).filter (fun w => good11Free k w)).card := by
  refine Finset.card_bij (fun y _ => bstep y % 3 ^ k) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
    refine ⟨Nat.mod_lt _ (pow_pos (by norm_num) k), ?_⟩
    rw [← good11Free_mod_iff]
    exact (good11Free_succ_of_mod_three_eq_zero hy.2.2).mp hy.2.1
  · intro y₁ hy₁ y₂ hy₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hy₁ hy₂
    have h3k : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
    have hy1_eq : y₁ = 3 * (y₁ / 3) := by omega
    have hy2_eq : y₂ = 3 * (y₂ / 3) := by omega
    have hb1 : bstep y₁ = 2 * (y₁ / 3) := by
      conv_lhs => rw [hy1_eq]
      exact bstep_three_mul _
    have hb2 : bstep y₂ = 2 * (y₂ / 3) := by
      conv_lhs => rw [hy2_eq]
      exact bstep_three_mul _
    have hbeq : bstep y₁ = bstep y₂ :=
      eq_of_mod_three_pow_eq_of_lt (by omega) (by omega) (by omega) heq
    omega
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwlt, hwg⟩ := hw
    have h3k : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
    have h3mod : 3 ^ k % 2 = 1 := three_pow_mod_two k
    by_cases hwpar : w % 2 = 0
    · refine ⟨3 * (w / 2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_, by omega⟩
        rw [good11Free_succ_of_mod_three_eq_zero (by omega), bstep_three_mul]
        have : 2 * (w / 2) = w := by omega
        rwa [this]
      · rw [bstep_three_mul, show 2 * (w / 2) = w from by omega, Nat.mod_eq_of_lt hwlt]
    · refine ⟨3 * ((w + 3 ^ k) / 2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_, by omega⟩
        rw [good11Free_succ_of_mod_three_eq_zero (by omega), bstep_three_mul]
        have hsum : 2 * ((w + 3 ^ k) / 2) = w + 3 ^ k := by omega
        rw [hsum, ← Nat.mul_one (3 ^ k)]
        exact (good11Free_add_three_pow k 1 w).mpr hwg
      · rw [bstep_three_mul, show 2 * ((w + 3 ^ k) / 2) = w + 3 ^ k from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hwlt]

lemma card_good11Free_mod_two (k : ℕ) :
    ((Finset.range (3 ^ (k + 2))).filter (fun y => good11Free (k + 2) y ∧ y % 3 = 2)).card =
      ((Finset.range (3 ^ (k + 1))).filter
        (fun w => good11Free (k + 1) w ∧ w % 3 = 0)).card := by
  refine Finset.card_bij (fun y _ => bstep y % 3 ^ (k + 1)) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
    obtain ⟨hyg, hb0⟩ := (good11Free_succ_succ_of_mod_three_eq_two hy.2.2).mp hy.2.1
    refine ⟨Nat.mod_lt _ (pow_pos (by norm_num) (k + 1)), ?_, ?_⟩
    · rwa [← good11Free_mod_iff]
    · have hdvd : 3 ∣ 3 ^ (k + 1) := ⟨3 ^ k, by rw [pow_succ]; ring⟩
      rw [Nat.mod_mod_of_dvd _ hdvd, hb0]
  · intro y₁ hy₁ y₂ hy₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hy₁ hy₂
    have h3k : 3 ^ (k + 2) = 3 * 3 ^ (k + 1) := by rw [pow_succ]; ring
    have hy1_eq : y₁ = 3 * (y₁ / 3) + 2 := by omega
    have hy2_eq : y₂ = 3 * (y₂ / 3) + 2 := by omega
    have hb1 : bstep y₁ = 2 * (y₁ / 3) + 1 := by
      conv_lhs => rw [hy1_eq]
      exact bstep_three_mul_add_two _
    have hb2 : bstep y₂ = 2 * (y₂ / 3) + 1 := by
      conv_lhs => rw [hy2_eq]
      exact bstep_three_mul_add_two _
    have hbeq : bstep y₁ = bstep y₂ :=
      eq_of_mod_three_pow_eq_of_lt (by omega) (by omega) (by omega) heq
    omega
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwlt, hwg, hw0⟩ := hw
    have h3k : 3 ^ (k + 2) = 3 * 3 ^ (k + 1) := by rw [pow_succ]; ring
    have h3pos : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h3mod : 3 ^ (k + 1) % 2 = 1 := three_pow_mod_two (k + 1)
    have h3div3 : 3 ^ (k + 1) % 3 = 0 := by
      rw [pow_succ]
      omega
    by_cases hwpar : w % 2 = 1
    · refine ⟨3 * ((w - 1) / 2) + 2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_, by omega⟩
        rw [good11Free_succ_succ_of_mod_three_eq_two (by omega), bstep_three_mul_add_two]
        have : 2 * ((w - 1) / 2) + 1 = w := by omega
        rw [this]
        exact ⟨hwg, hw0⟩
      · rw [bstep_three_mul_add_two, show 2 * ((w - 1) / 2) + 1 = w from by omega,
          Nat.mod_eq_of_lt hwlt]
    · refine ⟨3 * ((w + 3 ^ (k + 1) - 1) / 2) + 2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_, by omega⟩
        rw [good11Free_succ_succ_of_mod_three_eq_two (by omega), bstep_three_mul_add_two]
        have hsum : 2 * ((w + 3 ^ (k + 1) - 1) / 2) + 1 = w + 3 ^ (k + 1) := by omega
        rw [hsum]
        refine ⟨?_, by omega⟩
        rw [← Nat.mul_one (3 ^ (k + 1))]
        exact (good11Free_add_three_pow (k + 1) 1 w).mpr hwg
      · rw [bstep_three_mul_add_two,
          show 2 * ((w + 3 ^ (k + 1) - 1) / 2) + 1 = w + 3 ^ (k + 1) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hwlt]

/-- **11-free Fibonacci count**: the number of `k`-step `11`-free legal residue classes modulo
`3 ^ k` is `Nat.fib (k + 2)`. -/
theorem good11Free_card : ∀ k : ℕ,
    ((Finset.range (3 ^ k)).filter (fun y => good11Free k y)).card = Nat.fib (k + 2)
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    have ih1 := good11Free_card (k + 1)
    have ih0 := good11Free_card k
    let S := (Finset.range (3 ^ (k + 2))).filter (fun y => good11Free (k + 2) y)
    have hpart := Finset.card_filter_add_card_filter_not (s := S) (fun y => y % 3 = 0)
    have h0 : (S.filter (fun y => y % 3 = 0)).card =
        ((Finset.range (3 ^ (k + 2))).filter
          (fun y => good11Free (k + 2) y ∧ y % 3 = 0)).card := by
      simp [S, Finset.filter_filter]
    have h2 : (S.filter (fun y => ¬ y % 3 = 0)).card =
        ((Finset.range (3 ^ (k + 2))).filter
          (fun y => good11Free (k + 2) y ∧ y % 3 = 2)).card := by
      congr 1
      ext y
      simp only [S, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hy, hg⟩, hne⟩
        have hy1 : y % 3 ≠ 1 := hg.1 0 (by omega)
        exact ⟨hy, hg, by omega⟩
      · rintro ⟨hy, hg, hy2⟩
        exact ⟨⟨hy, hg⟩, by omega⟩
    rw [h0, h2, card_good11Free_mod_zero (k + 1), card_good11Free_mod_two k,
      card_good11Free_mod_zero k, ih1, ih0] at hpart
    rw [← hpart, Nat.fib_add_two (n := k + 2), show k + 2 + 1 = k + 1 + 2 from by omega,
      Nat.add_comm]


/-! ### Walsh-Hadamard zero correlation

By `parity_linear_split`, the Boolean function `x ↦ step^[k] x % 2` on `k + 1` bits has the top
bit `x_k` separated as an independent linear XOR summand.  Consequently, any Walsh-Hadamard mask
`u` with `k`-th bit `0` has correlation `walsh k u = 0`, and any mask with `k`-th bit `1`
doubles the Walsh coefficient of the nonlinear core on `k` bits. -/

/-- Bitwise dot product modulo `2` over the lowest `n` bits. -/
@[expose] public def bitDot (n u x : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n, (u / 2 ^ i % 2) * (x / 2 ^ i % 2)) % 2

/-- Walsh-Hadamard coefficient of `x ↦ step^[k] x % 2` on `k + 1` bits at linear mask `u`. -/
@[expose] public def walsh (k u : ℕ) : ℤ :=
  ∑ x ∈ Finset.range (2 ^ (k + 1)), (-1 : ℤ) ^ ((step^[k] x) % 2 + bitDot (k + 1) u x)

/-- Walsh-Hadamard coefficient of the nonlinear core `g_k` on the low `k` bits at mask `u`. -/
@[expose] public def walshCore (k u : ℕ) : ℤ :=
  ∑ x ∈ Finset.range (2 ^ k), (-1 : ℤ) ^ ((step^[k] x) % 2 + bitDot k u x)

lemma div_two_pow_add_two_pow_mod_two {k i : ℕ} (hi : i < k) (x : ℕ) :
    (x + 2 ^ k) / 2 ^ i % 2 = x / 2 ^ i % 2 := by
  obtain ⟨d, hd⟩ : ∃ d, k = i + (d + 1) := ⟨k - i - 1, by omega⟩
  have hpow : 2 ^ k = 2 ^ i * (2 ^ d * 2) := by rw [hd, pow_add, pow_succ]
  rw [hpow, Nat.add_mul_div_left _ _ (pow_pos (by norm_num) i)]
  omega

lemma bitDot_succ_of_lt {k u x : ℕ} (hx : x < 2 ^ k) :
    bitDot (k + 1) u x = bitDot k u x := by
  simp only [bitDot, Finset.sum_range_succ, Nat.div_eq_of_lt hx, Nat.zero_mod, mul_zero,
    add_zero]

lemma bitDot_succ_add_two_pow {k u x : ℕ} (hx : x < 2 ^ k) :
    bitDot (k + 1) u (x + 2 ^ k) = (bitDot k u x + u / 2 ^ k % 2) % 2 := by
  unfold bitDot
  rw [Finset.sum_range_succ]
  have hsum : ∑ i ∈ Finset.range k, (u / 2 ^ i % 2) * ((x + 2 ^ k) / 2 ^ i % 2) =
      ∑ i ∈ Finset.range k, (u / 2 ^ i % 2) * (x / 2 ^ i % 2) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [div_two_pow_add_two_pow_mod_two (Finset.mem_range.mp hi) x]
  have htop : (x + 2 ^ k) / 2 ^ k % 2 = 1 := by
    rw [show x + 2 ^ k = x + 2 ^ k * 1 from by ring,
      Nat.add_mul_div_left x 1 (pow_pos (by norm_num) k), Nat.div_eq_of_lt hx]
  rw [hsum, htop, mul_one]
  omega

lemma bitDot_add_two_pow (k u x : ℕ) : bitDot k (u + 2 ^ k) x = bitDot k u x := by
  unfold bitDot
  have hsum : ∑ i ∈ Finset.range k, ((u + 2 ^ k) / 2 ^ i % 2) * (x / 2 ^ i % 2) =
      ∑ i ∈ Finset.range k, (u / 2 ^ i % 2) * (x / 2 ^ i % 2) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [div_two_pow_add_two_pow_mod_two (Finset.mem_range.mp hi) u]
  rw [hsum]

lemma neg_one_pow_eq_mod_two (n : ℕ) : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_mul]
  norm_num

lemma walsh_split (k u : ℕ) :
    walsh k u = ∑ x ∈ Finset.range (2 ^ k),
      ((-1 : ℤ) ^ ((step^[k] x) % 2 + bitDot (k + 1) u x) +
        (-1 : ℤ) ^ ((step^[k] (x + 2 ^ k)) % 2 + bitDot (k + 1) u (x + 2 ^ k))) := by
  unfold walsh
  rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k from by rw [pow_succ, mul_two]]
  rw [Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.add_comm (2 ^ k) x]

/-- **Walsh zero-correlation theorem**: any mask omitting bit `k` has Walsh coefficient `0`. -/
theorem walsh_zero_of_bit_zero (k u : ℕ) (hu : u / 2 ^ k % 2 = 0) : walsh k u = 0 := by
  rw [walsh_split]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hxlt := Finset.mem_range.mp hx
  rw [step_pow_add_two_pow_parity, bitDot_succ_of_lt hxlt, bitDot_succ_add_two_pow hxlt, hu,
    Nat.add_zero]
  have ha : (step^[k] x) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb : bitDot k u x < 2 := Nat.mod_lt _ (by norm_num)
  rw [neg_one_pow_eq_mod_two ((step^[k] x) % 2 + bitDot k u x),
    neg_one_pow_eq_mod_two (1 - (step^[k] x) % 2 + bitDot k u x % 2)]
  rcases (by omega : ((step^[k] x) % 2 + bitDot k u x) % 2 = 0 ∨
      ((step^[k] x) % 2 + bitDot k u x) % 2 = 1) with h | h
  · have h' : (1 - (step^[k] x) % 2 + bitDot k u x % 2) % 2 = 1 := by omega
    rw [h, h']
    norm_num
  · have h' : (1 - (step^[k] x) % 2 + bitDot k u x % 2) % 2 = 0 := by omega
    rw [h, h']
    norm_num

/-- **Walsh core reduction**: when bit `k` of the mask is `1`, `walsh k u = 2 * walshCore k u`. -/
theorem walsh_eq_two_mul_core (k u : ℕ) (hu : u / 2 ^ k % 2 = 1) :
    walsh k u = 2 * walshCore k u := by
  rw [walsh_split]
  unfold walshCore
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxlt := Finset.mem_range.mp hx
  rw [step_pow_add_two_pow_parity, bitDot_succ_of_lt hxlt, bitDot_succ_add_two_pow hxlt, hu]
  have ha : (step^[k] x) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb : bitDot k u x < 2 := Nat.mod_lt _ (by norm_num)
  have hpair : (1 - (step^[k] x) % 2 + (bitDot k u x + 1) % 2) % 2 =
      ((step^[k] x) % 2 + bitDot k u x) % 2 := by omega
  rw [neg_one_pow_eq_mod_two ((step^[k] x) % 2 + bitDot k u x),
    neg_one_pow_eq_mod_two (1 - (step^[k] x) % 2 + (bitDot k u x + 1) % 2), hpair,
    ← neg_one_pow_eq_mod_two]
  ring

/-- Explicit mask form for `u = u' + 2 ^ k` with `u' < 2 ^ k`. -/
theorem walsh_add_two_pow {k u' : ℕ} (hu : u' < 2 ^ k) :
    walsh k (u' + 2 ^ k) = 2 * walshCore k u' := by
  have hbit : (u' + 2 ^ k) / 2 ^ k % 2 = 1 := by
    rw [show u' + 2 ^ k = u' + 2 ^ k * 1 from by ring,
      Nat.add_mul_div_left u' 1 (pow_pos (by norm_num) k), Nat.div_eq_of_lt hu]
  rw [walsh_eq_two_mul_core k (u' + 2 ^ k) hbit]
  unfold walshCore
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun x _ => ?_)
  rw [bitDot_add_two_pow]


end Mahler32

end
