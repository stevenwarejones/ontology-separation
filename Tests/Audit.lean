import OntologySeparation
import OntologySeparation.Catalog.Evidence
import OntologySeparation.Core.Assumptions

-- CI checks the transitive axioms of every proof-bearing report claim and core result.
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

#print axioms OntologySeparation.Catalog.resolve
#print axioms OntologySeparation.Catalog.claim_reference_consistent
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
