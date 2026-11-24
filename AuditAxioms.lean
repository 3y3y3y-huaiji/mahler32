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
#print axioms Mahler32.TwoWorldPadeCriterion.qStar_bounds
#print axioms Mahler32.TwoWorldPadeCriterion.two_world_ghost_bounds
#print axioms Mahler32.TwoWorldPadeCriterion.no_eventually_periodic_94
#print axioms Mahler32.TwoWorldPadeCriterion.nine_pow_200_lt_four_pow_317
#print axioms Mahler32.TwoWorldPadeCriterion.repetition_exponent_bound
#print axioms Mahler32.TwoWorldPadeCriterion.mod_nine_gate_rat
#print axioms Mahler32.TwoWorldPadeCriterion.mod_nine_gate
#print axioms Mahler32.TwoWorldPadeCriterion.mod_nine_gate_b2
#print axioms Mahler32.TwoWorldPadeCriterion.mod_nine_anti_misfire

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

-- Issue #12: 9/4 global Fourier decay, midpoint 36^K intersection, and A_K antipodal exclusion
#print axioms Mahler32.Model94GlobalDecay.iter94_exists_word
#print axioms Mahler32.Model94GlobalDecay.inSK_mod_36_pow
#print axioms Mahler32.Model94GlobalDecay.inAK_mod_36_pow
#print axioms Mahler32.Model94GlobalDecay.five_dvd_nine_pow_sub_four_pow
#print axioms Mahler32.Model94GlobalDecay.midpoint_double_cantor
#print axioms Mahler32.Model94GlobalDecay.inAK_scaled_interval_mul
#print axioms Mahler32.Model94GlobalDecay.inAK_scaled_interval
#print axioms Mahler32.Model94GlobalDecay.inAK_antipodal_exclusion
#print axioms Mahler32.Model94GlobalDecay.card_survivorsSet94
#print axioms Mahler32.Model94GlobalDecay.hatMu94_mul_four
#print axioms Mahler32.Model94GlobalDecay.hatMu94_four_pow_mul
#print axioms Mahler32.Model94GlobalDecay.norm_hatMu94_four_pow_mul
#print axioms Mahler32.Model94GlobalDecay.hatMu94_nine_mul
#print axioms Mahler32.Model94GlobalDecay.norm_hatMu94_nine_mul
#print axioms Mahler32.Model94GlobalDecay.hatMu94_mod_four_pow
#print axioms Mahler32.Model94GlobalDecay.norm_hatMu94_cosine_product
#print axioms Mahler32.Model94GlobalDecay.circleDist_step_exact
#print axioms Mahler32.Model94GlobalDecay.norm_hatMu94_le_cos_pow
#print axioms Mahler32.Model94GlobalDecay.global_odd_freq_decay
#print axioms Mahler32.Model94GlobalDecay.global_freq_decay_of_four_pow
#print axioms Mahler32.Model94GlobalDecay.DualPotentialCert.path_bound
#print axioms Mahler32.Model94GlobalDecay.DualPotentialCert.path_contraction
#print axioms Mahler32.Model94GlobalDecay.cert42_path_decay

-- Issue #17: General (p, q) repetition exclusion, Fourier decay, Karp cycle bound, and automata
-- (`Mahler32.RationalBaseDefs` contains pure definitions exercised via the modules below.)
#print axioms Mahler32.qStarPQ
#print axioms Mahler32.GeneralPQDecay.qStarPQ_bounds
#print axioms Mahler32.GeneralPQDecay.two_place_isolation_pq
#print axioms Mahler32.GeneralPQDecay.no_eventually_periodic_pq
#print axioms Mahler32.GeneralPQDecay.repetition_exponent_bound_pq
#print axioms Mahler32.GeneralPQDecay.card_survivorsSetPQ
#print axioms Mahler32.GeneralPQDecay.hatMuPQ_mul_q
#print axioms Mahler32.GeneralPQDecay.hatMuPQ_q_pow_mul
#print axioms Mahler32.GeneralPQDecay.norm_hatMuPQ_q_pow_mul
#print axioms Mahler32.GeneralPQDecay.hatMuPQ_p_mul
#print axioms Mahler32.GeneralPQDecay.norm_hatMuPQ_p_mul
#print axioms Mahler32.GeneralPQDecay.hatMuPQ_mod_q_pow
#print axioms Mahler32.GeneralPQDecay.norm_hatMuPQ_cosine_product
#print axioms Mahler32.GeneralPQDecay.norm_hatMuPQ_le_cos_pow
#print axioms Mahler32.GeneralPQDecay.global_coprime_freq_decay_pq
#print axioms Mahler32.GeneralPQDecay.global_freq_decay_of_q_pow_pq
#print axioms Mahler32.GeneralPQDecay.weyl_decay_3_2
#print axioms Mahler32.GeneralPQDecay.weyl_decay_4_3
#print axioms Mahler32.GeneralPQDecay.weyl_decay_5_4
#print axioms Mahler32.GeneralPQDecay.weyl_decay_5_3
#print axioms Mahler32.GeneralPQDecay.weyl_decay_7_4
#print axioms Mahler32.GeneralPQDecay.weyl_decay_8_3
#print axioms Mahler32.GeneralPQDecay.karp_cycle_bound
#print axioms Mahler32.GeneralPQDecay.cert44_path_decay
#print axioms Mahler32.GeneralPQDecay.cert44_cycle_bound

#print axioms Mahler32.ZeroEntropyAutomaton.hasBranchOverlap_sound
#print axioms Mahler32.ZeroEntropyAutomaton.totalPaths_poly_bound
#print axioms Mahler32.ZeroEntropyAutomaton.zero_entropy_of_no_branching_scc
#print axioms Mahler32.ZeroEntropyAutomaton.automaton_orbit_sound
#print axioms Mahler32.ZeroEntropyAutomaton.cert_neg_5_3_width
#print axioms Mahler32.ZeroEntropyAutomaton.cert_neg_5_3_zero_entropy
#print axioms Mahler32.ZeroEntropyAutomaton.cert_neg_3_2_holed_width_gt_half
#print axioms Mahler32.ZeroEntropyAutomaton.cert_neg_3_2_holed_zero_entropy
#print axioms Mahler32.ZeroEntropyAutomaton.cert_neg_3_2_centered_width
#print axioms Mahler32.ZeroEntropyAutomaton.cert_neg_3_2_centered_zero_entropy
#print axioms Mahler32.ZeroEntropyAutomaton.cert_pos_5_3_centered_width
#print axioms Mahler32.ZeroEntropyAutomaton.cert_pos_5_3_centered_zero_entropy

-- `Mahler32.Basic` (imported transitively by every task module above) and
-- `Mahler32.QuiverMonotone` (the mathlib4#44885 mirror consumed by `Mahler32.DAGBoundedGap`)
-- are audited here directly, so the module inventory of `scripts/verify_ssot.py` is complete.
#print axioms Mahler32.step_parity
#print axioms Quiver.StrictMono.isPartialOrder_reachable

end
