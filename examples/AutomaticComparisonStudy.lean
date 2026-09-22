import OntologySeparation.Study

namespace AutomaticComparisonStudy

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite

noncomputable section

def ideal : Law := Law.dephasing 0 1
def noisy : Law := Law.dephasing 1 2

/-- The adopter supplies only nonempty experiment lists. Setting/outcome coverage
is derived automatically from their finite interface. -/
def calibrationFamily : ProtocolFamily Recipe :=
  ⟨calibrationProbe, []⟩

def coherenceFamily : ProtocolFamily Recipe :=
  ⟨coherenceProbe, []⟩

def calibrationResult :=
  certifyFamily exactBackend calibrationFamily ideal noisy

def coherenceResult :=
  certifyFamily exactBackend coherenceFamily ideal noisy

def calibrationClaim : Claim := calibrationResult.claim
def coherenceClaim : Claim := coherenceResult.claim

end
end AutomaticComparisonStudy

#export_claim AutomaticComparisonStudy.calibrationClaim
#export_claim AutomaticComparisonStudy.coherenceClaim
