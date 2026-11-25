/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
module

public import Mathlib
public import Mahler32.TwoWorldPadeCriterion
public import Mahler32.Model94GlobalDecay

/-!
# Pure Definitions for General Coprime `(p, q)` Bases & Rational Zero-Entropy Automata

This file collects the core `@[expose] public def` definitions and structures for the general
`(p, q)` formalization (Issue #17) without proofs, enabling direct inspection by human reviewers:

1. **Symbolic word weights and `q`-adic / Archimedean limit**:
   `wordWeightPQ`, `validWordPQ`, `matchesWordPQ`, `qStarPQ`.
2. **Consecutive-digit `(p, q)` tunnel model & Fourier transform**:
   `TunnelModelPQ`, `TunnelModelPQ.step`, `TunnelModelPQ.iter`, `TunnelModelPQ.survives`,
   `TunnelModelPQ.survivorsSet`, `TunnelModelPQ.hatMu`.
3. **Signed rational multi-branch automaton**:
   `RatInterval`, `StepPQ`, `hasOverlapBranch`, `hasBranchOverlap`, `ZeroEntropyAutomaton`,
   `unionWidth`, `countPathsFrom`, `totalPaths`, `getCell`, `getComp`.
-/

public section

open scoped BigOperators

namespace Mahler32

open Mahler32.TwoWorldPadeCriterion
open Mahler32.Model94GlobalDecay

/-! ### 1. Symbolic `(p, q)` word weights & limit -/

/-- Weighted `(p, q)`-word accumulation `∑_{j=0}^{L-1} d_j · p^{L-1-j} · q^j` (MSB-first). -/
@[expose] public def wordWeightPQ (p q : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: rest => d * p ^ rest.length + q * wordWeightPQ p q rest

/-- Digit-range admissibility for `(p, q)` symbolic words. -/
@[expose] public def validWordPQ (dmin dmax : ℕ) (W : List ℕ) : Prop :=
  ∀ d ∈ W, dmin ≤ d ∧ d ≤ dmax

/-- `g0` matches word `W` for `W.length` steps of `q g_{k+1} = p g_k + d_k`. -/
@[expose] public def matchesWordPQ (p q g0 : ℕ) (W : List ℕ) : Prop :=
  ∃ gN : ℕ, q ^ W.length * gN = p ^ W.length * g0 + wordWeightPQ p q W

/-- The `q`-adic / Archimedean limit `q*(U, V)` attached to `U V^∞`. -/
@[expose] public def qStarPQ (p q : ℕ) (U V : List ℕ) : ℚ :=
  -((((p : ℤ) ^ V.length - q ^ V.length) * (wordWeightPQ p q U : ℤ) +
      (q : ℤ) ^ U.length * (wordWeightPQ p q V : ℤ) : ℤ) : ℚ) /
    ((p : ℚ) ^ U.length * ((p : ℚ) ^ V.length - (q : ℚ) ^ V.length))


/-! ### 2. Consecutive-digit `(p, q)` tunnel model -/

/-- Two-branch consecutive-digit `(p, q)` model `q · g' = p · g + d` (`d ∈ {d₀ + 1, d₀}`). -/
public structure TunnelModelPQ where
  p : ℕ
  q : ℕ
  d0 : ℕ
  r1 : ℕ
  r2 : ℕ
  hq : 2 ≤ q
  hpq : q < p
  hcop : Nat.Coprime p q
  hr1_lt : r1 < q
  hr2_lt : r2 < q
  hr_ne : r1 ≠ r2
  hmod1 : (p * r1 + (d0 + 1)) % q = 0
  hmod2 : (p * r2 + d0) % q = 0

/-- One-step `(p, q)` tunnel map on `r₁, r₂ (mod q)`. -/
@[expose] public def TunnelModelPQ.step (M : TunnelModelPQ) (g : ℕ) : Option ℕ :=
  if g % M.q = M.r1 then some ((M.p * g + (M.d0 + 1)) / M.q)
  else if g % M.q = M.r2 then some ((M.p * g + M.d0) / M.q)
  else none

/-- `K`-step iteration of `M.step`. -/
@[expose] public def TunnelModelPQ.iter (M : TunnelModelPQ) : ℕ → ℕ → Option ℕ
  | 0, g => some g
  | k + 1, g => (M.step g).bind (M.iter k)

/-- `K`-step survival predicate. -/
@[expose] public def TunnelModelPQ.survives (M : TunnelModelPQ) (K g : ℕ) : Prop :=
  M.iter K g ≠ none

public instance (M : TunnelModelPQ) (K g : ℕ) : Decidable (M.survives K g) :=
  inferInstanceAs (Decidable (M.iter K g ≠ none))

/-- Survivor finset in `[0, q^K)`. -/
@[expose] public def TunnelModelPQ.survivorsSet (M : TunnelModelPQ) (K : ℕ) : Finset ℕ :=
  (Finset.range (M.q ^ K)).filter (fun g => M.survives K g)

/-- Normalised Fourier transform `μ̂_K(u) = 2^{-K} ∑_{g ∈ S_K} e(u g / q^K)`. -/
@[expose] public noncomputable def TunnelModelPQ.hatMu (M : TunnelModelPQ) (K : ℕ) (u : ℤ) : ℂ :=
  ((2 : ℂ) ^ K)⁻¹ *
    ∑ g ∈ M.survivorsSet K, eChar ((u * (g : ℤ) : ℝ) / (M.q : ℝ) ^ K)


/-! ### 3. Signed rational intervals and zero-entropy automaton definitions -/

/-- Exact rational half-open interval `[ln/ld, hn/hd)` represented via reduced/explicit integer
numerators and positive natural denominators for fast kernel `decide` checking. -/
public structure RatInterval where
  ln : ℤ
  ld : ℕ
  hn : ℤ
  hd : ℕ
  ldPos : 0 < ld
  hdPos : 0 < hd
  lt : ln * (hd : ℤ) < hn * (ld : ℤ)
  deriving DecidableEq

/-- Lower rational endpoint `ln / ld`. -/
@[expose] public def RatInterval.lo (I : RatInterval) : ℚ :=
  (I.ln : ℚ) / (I.ld : ℚ)

/-- Upper rational endpoint `hn / hd`. -/
@[expose] public def RatInterval.hi (I : RatInterval) : ℚ :=
  (I.hn : ℚ) / (I.hd : ℚ)

/-- Half-open interval membership `lo ≤ x < hi`. -/
@[expose] public def RatInterval.mem (I : RatInterval) (x : ℚ) : Prop :=
  I.lo ≤ x ∧ x < I.hi

/-- Closed hull membership `lo ≤ x ≤ hi`; used by the finite-depth survivor bridge, whose
preimage certificates are closed at the endpoints that the half-open convention leaves out. -/
@[expose] public def RatInterval.closedMem (I : RatInterval) (x : ℚ) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

/-- Width `hi - lo` of a rational interval. -/
@[expose] public def RatInterval.width (I : RatInterval) : ℚ :=
  I.hi - I.lo

/-- Construct a `RatInterval` directly from numerator/denominator pairs. -/
@[expose] public def mkCell (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ)
    (hld : 0 < ld := by decide) (hhd : 0 < hd := by decide)
    (hlt : ln * (hd : ℤ) < hn * (ld : ℤ) := by decide) : RatInterval :=
  ⟨ln, ld, hn, hd, hld, hhd, hlt⟩

/-- Signed multi-branch map on `[0, 1)` for `α = ±p/q`: `q(y + m) = (±p)x + k` (`0 ≤ k < q`). -/
@[expose] public def StepPQ (p q : ℕ) (neg : Bool) (x y : ℚ) : Prop :=
  0 ≤ y ∧ y < 1 ∧ ∃ k : ℕ, k < q ∧ ∃ m : ℤ,
    (q : ℚ) * (y + (m : ℚ)) = (if neg then -(p : ℚ) else (p : ℚ)) * x + (k : ℚ)

/-- Pure integer cross-multiplied overlap check on branch `(k, m)`. -/
@[expose] public def hasOverlapBranch (p q : ℕ) (neg : Bool) (I J : RatInterval)
    (k : ℕ) (m : ℤ) : Bool :=
  let shift : ℤ := (k : ℤ) - m * (q : ℤ)
  if neg then
    let numLo : ℤ := -(p : ℤ) * I.hn + shift * (I.hd : ℤ)
    let denLo : ℤ := (q : ℤ) * (I.hd : ℤ)
    let numHi : ℤ := -(p : ℤ) * I.ln + shift * (I.ld : ℤ)
    let denHi : ℤ := (q : ℤ) * (I.ld : ℤ)
    decide (numLo * (J.hd : ℤ) < J.hn * denLo ∧ J.ln * denHi ≤ numHi * (J.ld : ℤ))
  else
    let numLo : ℤ := (p : ℤ) * I.ln + shift * (I.ld : ℤ)
    let denLo : ℤ := (q : ℤ) * (I.ld : ℤ)
    let numHi : ℤ := (p : ℤ) * I.hn + shift * (I.hd : ℤ)
    let denHi : ℤ := (q : ℤ) * (I.hd : ℤ)
    decide (numLo * (J.hd : ℤ) < J.hn * denLo ∧ J.ln * denHi ≤ numHi * (J.ld : ℤ))

/-- Exact decidable branch-image overlap test between `I` and `J` under `StepPQ p q neg`. -/
@[expose] public def hasBranchOverlap (p q : ℕ) (neg : Bool) (I J : RatInterval) : Bool :=
  (List.range q).any fun k =>
    (List.range (2 * p + 3)).any fun idx =>
      hasOverlapBranch p q neg I J k ((idx : ℤ) - (p : ℤ) - 1)

/-- Kernel-reducible list lookup for `RatInterval`. -/
@[expose] public def getCell : List RatInterval → ℕ → RatInterval
  | [], _ => mkCell 0 1 1 1
  | x :: _, 0 => x
  | _ :: xs, n + 1 => getCell xs n

/-- Kernel-reducible list lookup for component indices `Fin M`. -/
@[expose] public def getComp (M : ℕ) [NeZero M] : List ℕ → ℕ → Fin M
  | [], _ => 0
  | x :: _, 0 => Fin.ofNat M x
  | _ :: xs, n + 1 => getComp M xs n

/-- Finite rational symbolic automaton certifying zero topological entropy via topological SCCs
with no internal branching (`≤ 1` intra-component edge per vertex). -/
public structure ZeroEntropyAutomaton (p q : ℕ) (neg : Bool) (N M : ℕ) where
  cells : Fin N → RatInterval
  comp : Fin N → Fin M
  hcells0 : ∀ i, 0 ≤ (cells i).lo
  hcells1 : ∀ i, (cells i).hi ≤ 1
  htopo : ∀ i j, hasBranchOverlap p q neg (cells i) (cells j) = true → comp i ≤ comp j
  hnobranch : ∀ i,
    (Finset.univ.filter (fun j =>
      hasBranchOverlap p q neg (cells i) (cells j) = true ∧ comp j = comp i)).card ≤ 1

/-- Total width of a list of rational intervals. -/
@[expose] public def unionWidth : List RatInterval → ℚ
  | [] => 0
  | I :: rest => I.width + unionWidth rest

/-- Number of `L`-step walks in a directed Boolean graph starting at vertex `u`. -/
@[expose] public def countPathsFrom {N : ℕ} (adj : Fin N → Fin N → Bool) : Fin N → ℕ → ℕ
  | _, 0 => 1
  | u, L + 1 => ∑ v : Fin N, if adj u v then countPathsFrom adj v L else 0

/-- Total number of `L`-step walks in a directed Boolean graph. -/
@[expose] public def totalPaths {N : ℕ} (adj : Fin N → Fin N → Bool) (L : ℕ) : ℕ :=
  ∑ u : Fin N, countPathsFrom adj u L

end Mahler32

end
