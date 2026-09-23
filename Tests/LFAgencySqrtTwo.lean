import OntologySeparation.Certificates.LFAgencySqrtTwo

namespace OntologySeparation.Tests.LFAgencySqrtTwo
open OntologySeparation.LFAgencyRelaxation
open OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate
noncomputable section

example : 0 < sqrtTwoDelta := sqrtTwoDelta_positive
example : Shared.NoSignaling sqrtTwoBehavior := sqrtTwoBehavior_public_noSignaling
#print axioms OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate.dual_feasible
#print axioms OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate.bound

end
end OntologySeparation.Tests.LFAgencySqrtTwo
