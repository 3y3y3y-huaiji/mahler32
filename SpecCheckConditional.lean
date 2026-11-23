module

public import Mahler32Conditional.AlgebraicPairBranch

/-!
# `SpecCheckConditional` — the task-11 lock

Sibling of `SpecCheck.lean` for the *conditional* module.  It is deliberately a separate file so
that the zero-axiom core never imports `Mahler32Conditional`.  It locks, by `exact`:

* the **exact type** of the one permitted axiom `Mahler32Conditional.schlickewei_subspace_Q3`;
* the **exact final theorem type** `Mahler32Conditional.algebraic_pair_branch_finite`.

Any weakening (an extra hypothesis, a changed quantifier, a dropped `T.Finite`, a modified error
bound `ϑ^c`) makes the `exact` fail to unify, so CI rejects it.
-/

public section

namespace SpecCheck.Conditional

open Mahler32Conditional

/-- Lock: the verbatim type of the permitted external axiom. -/
example (δ : ℝ) (hδ : IsAlgebraic ℚ δ)
    (ϑ : ℚ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (T : Set (ℕ × ℕ)) (hT : T.Infinite)
    (hac : ∀ p ∈ T, 2 ≤ p.1 ∧ p.1 < p.2)
    (n : ℕ × ℕ → ℤ)
    (happrox : ∀ p ∈ T,
      |δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1) - (n p : ℝ)| ≤ (ϑ : ℝ) ^ p.2) :
    ∃ T' ⊆ T, T'.Infinite ∧
      ∃ A B C : ℚ, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
        ∀ p ∈ T', (A : ℝ) * (3 / 2 : ℝ) ^ p.2 + (B : ℝ) * (3 / 2 : ℝ) ^ p.1 +
          (C : ℝ) * (n p : ℝ) = 0 :=
  schlickewei_subspace_Q3 δ hδ ϑ hϑ0 hϑ1 T hT hac n happrox

/-- Lock: the verbatim main-theorem type of task 11. -/
example (δ : ℝ) (hδalg : IsAlgebraic ℚ δ) (hδirr : Irrational δ)
    (ϑ : ℚ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (T : Set (ℕ × ℕ))
    (hgap : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T)
    (hac : ∀ p ∈ T, 2 ≤ p.1 ∧ p.1 < p.2)
    (n : ℕ × ℕ → ℤ)
    (happrox : ∀ p ∈ T,
      |δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1) - (n p : ℝ)| ≤ (ϑ : ℝ) ^ p.2) :
    T.Finite :=
  algebraic_pair_branch_finite δ hδalg hδirr ϑ hϑ0 hϑ1 T hgap hac n happrox

end SpecCheck.Conditional

end
