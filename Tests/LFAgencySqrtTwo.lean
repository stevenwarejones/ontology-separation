import OntologySeparation.Operational.LFAgencySqrtTwo
import OntologySeparation.Experiments.LFAgencyAngleOptimality

namespace OntologySeparation.Tests.LFAgencySqrtTwo
open OntologySeparation.LFAgencyRelaxation
open OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate
noncomputable section

example : 0 < sqrtTwoDelta := sqrtTwoDelta_positive
example : Shared.NoSignaling sqrtTwoBehavior := sqrtTwoBehavior_public_noSignaling
example : RealQuantum.singletTheory 3 sqrtTwoBehavior := explicit_quantum_realized
#print axioms OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate.dual_feasible
#print axioms OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate.bound

end
end OntologySeparation.Tests.LFAgencySqrtTwo

#print axioms OntologySeparation.LFAgencyRelaxation.SqrtTwoPhysical.sum_recordTV_lower_bound
#print axioms OntologySeparation.LFAgencyRelaxation.SqrtTwoPhysical.explicit_angle_bound

-- Explicit-angle theorem is intentionally local in angle space.

-- Full proof target: explicit pi/8-grid quantum behavior.


#print axioms OntologySeparation.LFAgencyRelaxation.AngleOptimality.basisCorr_formula
#print axioms OntologySeparation.LFAgencyRelaxation.AngleOptimality.chshNumerator_le
#print axioms OntologySeparation.LFAgencyRelaxation.AngleOptimality.anchoredWitness_le_sqrtTwoDelta
#print axioms OntologySeparation.LFAgencyRelaxation.AngleOptimality.explicit_anchoredWitness
#print axioms OntologySeparation.LFAgencyRelaxation.AngleOptimality.anchoredWitness_global_optimum
