import OntologySeparation.Core.AutomaticGrid
import OntologySeparation.Recipes.Separation
import Mathlib.Tactic

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite

noncomputable section

def autoIdeal : Law := Law.dephasing 0 1
def autoNoisy : Law := Law.dephasing 1 2

def calibrationFamily : ProtocolFamily Recipe :=
  ⟨calibrationProbe, []⟩

def coherenceFamily : ProtocolFamily Recipe :=
  ⟨coherenceProbe, []⟩

example : calibrationFamily.entries =
    [⟨calibrationProbe, (), false⟩, ⟨calibrationProbe, (), true⟩] := by
  rfl

example : coherenceFamily.entries =
    [⟨coherenceProbe, (), false⟩, ⟨coherenceProbe, (), true⟩] := by
  rfl

def autoCalibration :=
  certifyFamily exactBackend calibrationFamily autoIdeal autoNoisy

def autoCoherence :=
  certifyFamily exactBackend coherenceFamily autoIdeal autoNoisy

/-- The one-call API produces ordinary audited claims without a handwritten
Grid.covers proof at the call site. -/
example : autoCalibration.claim.statement := autoCalibration.sound
example : autoCoherence.claim.statement := autoCoherence.sound

end
