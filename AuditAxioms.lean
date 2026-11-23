module

public import Mahler32Core

/-!
# Kernel axiom audit for the zero-axiom core (tasks 1–10)

Run with

```bash
lake env lean AuditAxioms.lean
```

CI wraps this in `scripts/check_axioms.py AuditAxioms.lean propext,Quot.sound,Classical.choice`,
which additionally rejects `sorryAx` and any axiom outside the Lean standard triple.
-/

public section

#print axioms Mahler32.Base6LightCone.light_cone_flip
#print axioms Mahler32.Base6LightCone.good_mod_iff

#print axioms Mahler32.SyracuseGates.odd_step_mod_twelve
#print axioms Mahler32.SyracuseGates.short_jump_mod_256
#print axioms Mahler32.SyracuseGates.mod_768_gate

#print axioms Mahler32.ArnoldTongue5State.nextInterval_exact
#print axioms Mahler32.ArnoldTongue5State.countPaths_zero

#print axioms Mahler32.ArnoldTongue7State.nextInterval7_exact
#print axioms Mahler32.ArnoldTongue7State.countPaths7_zero

#print axioms Mahler32.DAGBoundedGap.dag_bounded_gap
#print axioms Mahler32.DAGBoundedGap.zStepNat_add_128
#print axioms Mahler32.DAGBoundedGap.S7_iff_hits

#print axioms Mahler32.TwoWorldPadeCriterion.two_world_identity
#print axioms Mahler32.TwoWorldPadeCriterion.integer_divisibility_bound
#print axioms Mahler32.TwoWorldPadeCriterion.two_world_iff
#print axioms Mahler32.TwoWorldPadeCriterion.two_pow_dvd_eq_zero

#print axioms Mahler32.ArnoldTongue5State.T_false_maps
#print axioms Mahler32.ArnoldTongue7State.T_true_maps

#print axioms Mahler32.ZeroEntropyCages.exclusion_integer
#print axioms Mahler32.ZeroEntropyCages.cage_two_sevenths

#print axioms Mahler32.DiscreteFluidCertificates.cup_cycle
#print axioms Mahler32.DiscreteFluidCertificates.cup_period_three

#print axioms Mahler32.Fib11Free.fib_count
#print axioms Mahler32.Fib11Free.survivors_four

#print axioms Mahler32.WalshZeroCorr.walsh_top_bit_zero
#print axioms Mahler32.WalshZeroCorr.walsh_top_bit_double

#print axioms Mahler32.HInvariance.affine_phase_shift
#print axioms Mahler32.HInvariance.fourier_norm_invariant

#print axioms Mahler32.SyracuseBijection.syracuse_bijective
#print axioms Mahler32.SyracuseBijection.force_b_ge_five

end
