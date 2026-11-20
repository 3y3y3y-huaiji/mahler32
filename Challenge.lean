module

public import Mathlib

/-!
# Advertised statements

The statement surface of the submission: the definitions needed to read the claims, and the
claims themselves.  Every proof here is `sorry`; `Solution.lean` discharges the same names
against `Mahler32.Basic`.

The object is OEIS A061419, `a (n+1) = a n + ⌈a n / 2⌉`, i.e. the `3/2` map of Mahler (1968).
`step` is the one-step map, `bstep` its inverse branch, `good k y` says that `y` has a `k`-step
backward orbit, and `val` / `runOut` / `runRem` are the base-`3` long-division transducer.
-/

public section

namespace Mahler32

/-- A061419: `a 0 = 1`, `a (n+1) = a n + ⌈a n / 2⌉`. -/
@[expose] public def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => a n + (a n + 1) / 2

/-- The one-step map `x ↦ x + ⌈x / 2⌉ = ⌈3x/2⌉`. -/
@[expose] public def step (x : ℕ) : ℕ := x + (x + 1) / 2

/-- The inverse branch: undo one base-`3` digit. -/
@[expose] public def bstep (y : ℕ) : ℕ := (2 * y - 2 * y % 3) / 3

/-- `y` has a legal `k`-step backward orbit. -/
@[expose] public def good (k y : ℕ) : Prop := ∀ j, j < k → (bstep^[j] y) % 3 ≠ 1

/-- Value of a most-significant-digit-first base-`3` digit list. -/
@[expose] public def val : List ℕ → ℕ
  | [] => 0
  | d :: ds => d * 3 ^ ds.length + val ds

/-- Quotient digits of the divide-by-`2` scan. -/
@[expose] public def runOut : List ℕ → ℕ → List ℕ
  | [], _ => []
  | d :: ds, r => (3 * r + d) / 2 :: runOut ds ((3 * r + d) % 2)

/-- Final carry of the divide-by-`2` scan. -/
@[expose] public def runRem : List ℕ → ℕ → ℕ
  | [], r => r
  | d :: ds, r => runRem ds ((3 * r + d) % 2)

/-- Number of odd digits. -/
@[expose] public def ones (L : List ℕ) : ℕ := (L.map (fun d => d % 2)).sum

public instance decidableGood (k : ℕ) : DecidablePred (good k) := fun y =>
  Nat.decidableBallLT k (fun j _ => (bstep^[j] y) % 3 ≠ 1)

/-- The next parity is the second binary digit of the current term. -/
theorem step_parity (x : ℕ) : step x % 2 = x / 2 % 2 := by
  sorry

/-- The last base-`6` digit is a bijective encoding of consecutive parities. -/
theorem a_mod_six (n : ℕ) : a (n + 1) % 6 = 3 * (a (n + 1) % 2) + 2 * (a n % 2) := by
  sorry

/-- `m` base-`6` digits determine exactly the next `m` parities. -/
theorem parity_window_hex (m k t x : ℕ) (hk : k < m) :
    (step^[k] (x + 6 ^ m * t)) % 2 = (step^[k] x) % 2 := by
  sorry

/-- The window is sharp: `m` base-`6` digits do not determine the `(m+1)`-st parity. -/
theorem cliff_sharp (m : ℕ) :
    ∃ x y : ℕ, x % 6 ^ m = y % 6 ^ m ∧ (step^[m] x) % 2 ≠ (step^[m] y) % 2 := by
  sorry

/-- The base-`3` two-state machine computes `⌈3x/2⌉`. -/
theorem ternary_machine (x : ℕ) :
    val (runOut ((Nat.digits 3 x).reverse ++ [x % 2]) 0) = step x := by
  sorry

/-- Exactly `2 ^ k` legal residue classes modulo `3 ^ k`. -/
theorem good_card (k : ℕ) :
    ((Finset.range (3 ^ k)).filter (fun y => good k y)).card = 2 ^ k := by
  sorry

/-- Odd number of odd digits: `|B|` is not a period of the scan of `B ++ B`. -/
theorem period_doubling (B : List ℕ) (hd : ∀ d ∈ B, d < 3) (hB : B ≠ [])
    (hodd : ones B % 2 = 1) (r : ℕ) (hr : r < 2) :
    (runOut (B ++ B) r).take B.length ≠ (runOut (B ++ B) r).drop B.length := by
  sorry

end Mahler32

end
