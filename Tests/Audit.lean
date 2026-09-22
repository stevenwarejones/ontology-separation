import OntologySeparation
import OntologySeparation.Catalog.Matrix
import OntologySeparation.Core.Assumptions
import OntologySeparation.Core.ExactFiniteChecker
import OntologySeparation.Recipes.Separation
import OntologySeparation.Adapters.FiniteCircuit

-- Selected audit roots and their transitive dependencies; not a census of all declarations.
-- Each #export_theorem / #export_scenario also automatically audits its own dependencies.
#print axioms OntologySeparation.RealizedProfileBound.realizable
#print axioms OntologySeparation.RealizedProfileBound.valid
#print axioms OntologySeparation.ClassicalWorld.realizedBound
#print axioms OntologySeparation.Separation.excludes
#print axioms OntologySeparation.Behavior.prob_le_one
#print axioms OntologySeparation.Behavior.mix
#print axioms OntologySeparation.inconsistent_profile
#print axioms OntologySeparation.Catalog.bellLocalClaim
#print axioms OntologySeparation.Catalog.bellQuantumClaim
#print axioms OntologySeparation.Catalog.bellPRClaim
#print axioms OntologySeparation.Catalog.lfBoundClaim
#print axioms OntologySeparation.Catalog.lfQuantumClaim
#print axioms OntologySeparation.Catalog.lfControlClaim
#print axioms OntologySeparation.Catalog.echoClaim
#print axioms OntologySeparation.Catalog.leakClaim
#print axioms OntologySeparation.Catalog.phaseClaim
#print axioms OntologySeparation.RealQuantum.probability_born
#print axioms OntologySeparation.RealQuantum.singlet_normalized
#print axioms OntologySeparation.LF.Component.read_charlie
#print axioms OntologySeparation.LF.Component.read_debbie

#print axioms OntologySeparation.Claim.sound
#print axioms OntologySeparation.Catalog.matrix
#print axioms OntologySeparation.Memory.registered_parameters_valid
#print axioms OntologySeparation.quantum_operator_bound
#print axioms OntologySeparation.profileTheory_empty


#print axioms OntologySeparation.Shared.LF_ns_sharp
#print axioms OntologySeparation.Shared.local_three_LF_bound
#print axioms OntologySeparation.Shared.singlet_noSignaling
#print axioms OntologySeparation.Shared.inner_score
#print axioms OntologySeparation.Shared.LF_contamination_required
#print axioms OntologySeparation.Shared.LF_mix_score
#print axioms OntologySeparation.DephasedSinglet.bell_noise_threshold
#print axioms OntologySeparation.DephasedSinglet.LF_noise_threshold
#print axioms OntologySeparation.Research.pairwise_consistent
#print axioms OntologySeparation.Research.triangle_mixture_bound
#print axioms OntologySeparation.Research.random_query_bound
#print axioms OntologySeparation.Research.passive_relabel
#print axioms OntologySeparation.Research.joint_recovery
#print axioms OntologySeparation.Research.phase_state_normalized
#print axioms OntologySeparation.Research.phase_state_entangled
#print axioms OntologySeparation.Research.noisy_order_probability
#print axioms OntologySeparation.Research.public_error_bound
#print axioms OntologySeparation.free_binary_extension
#print axioms OntologySeparation.ProfileBridge.excludes
#print axioms OntologySeparation.Bound.excluded_by_lower

#print axioms OntologySeparation.Research.phase_state_not_complex_product
#print axioms OntologySeparation.Research.real_randomized_recovery

#print axioms OntologySeparation.Shared.LF_NS_contamination_attained
#print axioms OntologySeparation.Shared.LF_NS_fraction_required
#print axioms OntologySeparation.Shared.saturating_is_LF
#print axioms OntologySeparation.OperationalBell.chsh_bound
#print axioms OntologySeparation.OperationalBell.singlet_excludes
#print axioms OntologySeparation.FriendRecords.probability_preserved
#print axioms OntologySeparation.FriendRecords.bound
#print axioms OntologySeparation.FriendRecords.singlet_excludes
#print axioms OntologySeparation.Qubit.twice_dephased
#print axioms OntologySeparation.Qubit.phase_then_dephase
#print axioms OntologySeparation.Qubit.hadamard_twice
#print axioms OntologySeparation.Qubit.density_invariants
#print axioms OntologySeparation.Channel.andThen_assoc
#print axioms OntologySeparation.Countermodels.signaling_score
#print axioms OntologySeparation.Countermodels.signaling_not_local
#print axioms OntologySeparation.Countermodels.dependent_score
#print axioms OntologySeparation.Countermodels.dependent_not_independent
#print axioms OntologySeparation.Qubit.protected_dephasing
#print axioms OntologySeparation.OperationalProfiles.bell_bound
#print axioms OntologySeparation.OperationalProfiles.lf_bound
#print axioms OntologySeparation.OperationalProfiles.bell_supported_count
#print axioms OntologySeparation.OperationalProfiles.lf_supported_count
#print axioms OntologySeparation.ClassicalWorld.chsh_bound
#print axioms OntologySeparation.ClassicalWorld.cannot_reproduce_singlet
#print axioms OntologySeparation.ClassicalWorld.constant_score
#print axioms OntologySeparation.Channel.andThen
#print axioms OntologySeparation.Channel.parallel
#print axioms OntologySeparation.Experiment.same_evolution
#print axioms OntologySeparation.ProfileBound.valid
#print axioms OntologySeparation.ProfileBound.under
#print axioms OntologySeparation.Qubit.dephase

#print axioms OntologySeparation.Countermodels.quantumFriend_not_readable
#print axioms OntologySeparation.Countermodels.rejected_records_realized

#print axioms OntologySeparation.Scenario.ExactPredictions.prediction

#print axioms OntologySeparation.Recipes.probability_correct
#print axioms OntologySeparation.Recipes.probability_bounds
#print axioms OntologySeparation.Recipes.compare

#print axioms OntologySeparation.TwoQubit.Gate.normSq
#print axioms OntologySeparation.TwoQubit.Pure.born
#print axioms OntologySeparation.TwoQubit.Pure.amplitude_normalized
#print axioms OntologySeparation.TwoQubit.State.normalized
#print axioms OntologySeparation.TwoQubit.no_signaling_alice
#print axioms OntologySeparation.TwoQubit.no_signaling_bob
#print axioms OntologySeparation.TwoQubit.chsh_correct
#print axioms OntologySeparation.TwoQubit.excludes_local
#print axioms OntologySeparation.TwoQubit.compare
#print axioms OntologySeparation.TwoQubit.singlet_matches_reference
#print axioms OntologySeparation.TwoQubit.prepare_singlet_circuit

#print axioms OntologySeparation.FriendProtocol.encode_norm
#print axioms OntologySeparation.FriendProtocol.record_agreement
#print axioms OntologySeparation.FriendProtocol.undo_friends
#print axioms OntologySeparation.FriendProtocol.recordZ_encoded
#print axioms OntologySeparation.FriendProtocol.output_norm
#print axioms OntologySeparation.FriendProtocol.pure_normalized
#print axioms OntologySeparation.FriendProtocol.probability_bridge
#print axioms OntologySeparation.LocalFriendlinessRecipe.probability_correct
#print axioms OntologySeparation.LocalFriendlinessRecipe.no_signaling
#print axioms OntologySeparation.LocalFriendlinessRecipe.score_correct
#print axioms OntologySeparation.LocalFriendlinessRecipe.matches_reference
#print axioms OntologySeparation.LocalFriendlinessRecipe.charlie_noise_threshold
#print axioms OntologySeparation.LocalFriendlinessRecipe.coherent_excludes_profile
#print axioms OntologySeparation.LocalFriendlinessRecipe.fully_dephased_realizes_profile

#print axioms OntologySeparation.ExperimentAccess.Separator.not_equivalent

#print axioms OntologySeparation.ExperimentAccess.Equivalent.statistic

#print axioms OntologySeparation.FiniteQuantum.Test.normalized

#print axioms OntologySeparation.FiniteQuantum.Test.prepend_prob

#print axioms OntologySeparation.FiniteQuantum.local_behavior_eq

#print axioms OntologySeparation.RecordAccess.dephased_entry

#print axioms OntologySeparation.RecordAccess.all_local_tests

#print axioms OntologySeparation.RecordAccess.recovery_isometry

#print axioms OntologySeparation.RecordAccess.coherent_recovery

#print axioms OntologySeparation.RecordAccess.dephased_recovery

#print axioms OntologySeparation.RecordAccess.joint_not_equivalent

#print axioms OntologySeparation.FiniteModels.score_mixture

#print axioms OntologySeparation.FiniteModels.compatible_bound

#print axioms OntologySeparation.FiniteModels.Exclusion.excludes

#print axioms OntologySeparation.FiniteModels.no_conflicting_certificates

#print axioms OntologySeparation.ModelCompatibility.passes_one_bound_but_excluded

#print axioms OntologySeparation.ModelCompatibility.coherent_excludes_dephased_class

#print axioms OntologySeparation.ModelCompatibility.recordBoundClaim


-- Automatic exact comparison and finite-intervention trust roots.
#print axioms OntologySeparation.ExactFinite.equivalent_iff_exact
#print axioms OntologySeparation.ExactFinite.domainAgreementOfExact
#print axioms OntologySeparation.ExactFinite.CheckedResult.sound
#print axioms OntologySeparation.RecipeSeparation.outcomeProbability_correct
#print axioms OntologySeparation.RecipeSeparation.coherenceSeparator
#print axioms OntologySeparation.RecipeSeparation.expandedSeparator
#print axioms OntologySeparation.FiniteQuantum.measureAfterIsometry_prob_eq_lift
#print axioms OntologySeparation.FiniteCircuit.Circuit.apply_cons
#print axioms OntologySeparation.FiniteCircuit.test_normalized
