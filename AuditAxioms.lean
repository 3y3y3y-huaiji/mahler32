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
#print axioms Mahler32.DAGBoundedGap.gapPot_strictMono
#print axioms Mahler32.DAGBoundedGap.gap_acyclic
#print axioms Mahler32.DAGBoundedGap.gap_reachable_isPartialOrder
#print axioms Mahler32.DAGBoundedGap.carry_self_loop_127
#print axioms Mahler32.DAGBoundedGap.nat_uniform_eleven_fails

#print axioms Mahler32.TwoWorldPadeCriterion.two_world_identity
#print axioms Mahler32.TwoWorldPadeCriterion.integer_divisibility_bound
#print axioms Mahler32.TwoWorldPadeCriterion.two_world_iff
#print axioms Mahler32.TwoWorldPadeCriterion.two_pow_dvd_eq_zero

#print axioms Mahler32.ArnoldTongue5State.T_false_maps
#print axioms Mahler32.ArnoldTongue7State.T_true_maps

#print axioms Mahler32.ZeroEntropyCages.exclusion_integer
#print axioms Mahler32.ZeroEntropyCages.cage_two_sevenths
#print axioms Mahler32.ZeroEntropyCages.joint_orbit_two_sevenths
#print axioms Mahler32.ZeroEntropyCages.joint_cycle_two_fifths
#print axioms Mahler32.ZeroEntropyCages.joint_cycle_four_thirteenths
#print axioms Mahler32.ZeroEntropyCages.holed_cage_two_cycle
#print axioms Mahler32.ZeroEntropyCages.holed_cage_transients

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

-- Task 2: the `9/4` finite-roof arithmetic obstruction (seven theorem groups)
#print axioms Mahler32.Model94Obstructions.mirror_conservation_94
#print axioms Mahler32.Model94Obstructions.even_rung_mirror_annihilation
#print axioms Mahler32.Model94Obstructions.forbidden_sum_c2_mod4
#print axioms Mahler32.Model94Obstructions.odd_rung_klein4_exclusion
#print axioms Mahler32.Model94Obstructions.odd_rung_klein4_no_four
#print axioms Mahler32.Model94Obstructions.survives94_add_four_pow
#print axioms Mahler32.Model94Obstructions.iter94_add_four_pow
#print axioms Mahler32.Model94Obstructions.sum_shadow_exact
#print axioms Mahler32.Model94Obstructions.diff_shadow_exact
#print axioms Mahler32.Model94Obstructions.base9_transducer_exact
#print axioms Mahler32.Model94Obstructions.base9_digit_sum_conservation
#print axioms Mahler32.Model94Obstructions.finite_roof_block_certificate

-- `Mahler32.Basic` (imported transitively by every task module above) and
-- `Mahler32.QuiverMonotone` (the mathlib4#44885 mirror consumed by `Mahler32.DAGBoundedGap`)
-- are audited here directly, so the module inventory of `scripts/verify_ssot.py` is complete.
#print axioms Mahler32.step_parity
#print axioms Quiver.StrictMono.isPartialOrder_reachable

end
