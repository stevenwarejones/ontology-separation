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

example : calibrationFamily.entries (E := binaryInterface) =
    [⟨calibrationProbe, (), false⟩, ⟨calibrationProbe, (), true⟩] := by
  rfl

example : coherenceFamily.entries (E := binaryInterface) =
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

/-- Exercise both protocol-list elements and both finite interface dimensions. -/
private abbrev multiInterface : Interface := ⟨Bool, Bool⟩

private def multiFamily : ProtocolFamily Bool := ⟨false, [true]⟩

example : (multiFamily.entries (E := multiInterface)).map
    (fun x => (x.protocol, x.setting, x.outcome)) =
    [(false, false, false), (false, false, true),
     (false, true, false), (false, true, true),
     (true, false, false), (true, false, true),
     (true, true, false), (true, true, true)] := by
  rfl

-- Also check compiled enumeration, not just a theorem about an opaque list.
/-- info: 8 -/
#guard_msgs in
#eval (multiFamily.entries (E := multiInterface)).length

example : Entry.mk true true true ∈ (multiFamily.grid (E := multiInterface)).entries :=
  (multiFamily.grid (E := multiInterface)).covers true (by simp [ProtocolFamily.allowed,
    ProtocolFamily.protocols, multiFamily]) true true

end
