import OntologySeparation.Operational.LFAgencySqrtTwo

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
