import OntologySeparation.Study
import Mathlib.Tactic

namespace AutomaticComparisonStudy

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite

noncomputable section

def ideal : Law := Law.dephasing 0 1
def noisy : Law := Law.dephasing 1 2

def calibrationGrid : Grid Recipe binaryInterface calibrationOnly where
  entries := [⟨calibrationProbe, (), false⟩, ⟨calibrationProbe, (), true⟩]
  protocol := calibrationProbe
  included := rfl
  accessible := by
    intro x hx
    have hx' :
        x = (⟨calibrationProbe, (), false⟩ : Entry Recipe binaryInterface) ∨
        x = (⟨calibrationProbe, (), true⟩ : Entry Recipe binaryInterface) := by
      simpa using hx
    rcases hx' with h | h
    · cases h
      rfl
    · cases h
      rfl
  covers := by
    intro p hp s o
    subst p
    cases s
    cases o <;> simp

def coherenceOnly (r : Recipe) : Prop := r = coherenceProbe

def coherenceGrid : Grid Recipe binaryInterface coherenceOnly where
  entries := [⟨coherenceProbe, (), false⟩, ⟨coherenceProbe, (), true⟩]
  protocol := coherenceProbe
  included := rfl
  accessible := by
    intro x hx
    have hx' :
        x = (⟨coherenceProbe, (), false⟩ : Entry Recipe binaryInterface) ∨
        x = (⟨coherenceProbe, (), true⟩ : Entry Recipe binaryInterface) := by
      simpa using hx
    rcases hx' with h | h
    · cases h
      rfl
    · cases h
      rfl
  covers := by
    intro p hp s o
    subst p
    cases s
    cases o <;> simp

def calibrationResult :=
  certify exactBackend calibrationOnly calibrationGrid ideal noisy

def coherenceResult :=
  certify exactBackend coherenceOnly coherenceGrid ideal noisy

def calibrationClaim : Claim := calibrationResult.claim
def coherenceClaim : Claim := coherenceResult.claim

end
end AutomaticComparisonStudy

#export_claim AutomaticComparisonStudy.calibrationClaim
#export_claim AutomaticComparisonStudy.coherenceClaim
