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
