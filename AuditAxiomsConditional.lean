module

public import Mahler32Conditional.AlgebraicPairBranch

/-!
# Kernel axiom audit for the conditional module (task 11)

Unlike `AuditAxioms.lean`, this audit allows exactly one extra axiom,
`Mahler32Conditional.schlickewei_subspace_Q3` (together with the Lean standard triple).
CI runs `scripts/check_axioms.py` with that whitelist, and additionally verifies that the
zero-axiom core never mentions `schlickewei_subspace_Q3`.
-/

public section

#print axioms Mahler32Conditional.algebraic_pair_branch_finite

end
