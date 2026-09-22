import OntologySeparation.Core.ExactFiniteChecker
import OntologySeparation.Recipes.Separation
import Mathlib.Tactic

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite

noncomputable section

def checkerIdeal : Law := Law.dephasing 0 1
def checkerNoisy : Law := Law.dephasing 1 2

def calibrationGrid : Grid Recipe binaryInterface calibrationOnly where
  entries :=
    [⟨calibrationProbe, (), false⟩, ⟨calibrationProbe, (), true⟩]
  protocol := calibrationProbe
  included := rfl
  accessible := by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl <;> rfl
  covers := by
    intro p hp s o
    subst p
    cases s
    cases o <;> simp

def coherenceOnly (r : Recipe) : Prop := r = coherenceProbe

def coherenceGrid : Grid Recipe binaryInterface coherenceOnly where
  entries :=
    [⟨coherenceProbe, (), false⟩, ⟨coherenceProbe, (), true⟩]
  protocol := coherenceProbe
  included := rfl
  accessible := by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl <;> rfl
  covers := by
    intro p hp s o
    subst p
    cases s
    cases o <;> simp

def calibrationChecked :=
  certify exactBackend calibrationOnly calibrationGrid checkerIdeal checkerNoisy

def coherenceChecked :=
  certify exactBackend coherenceOnly coherenceGrid checkerIdeal checkerNoisy

/-- The calibration family is automatically certified as agreement. -/
example :
    match calibrationChecked with
    | .agreement _ => True
    | .separatesAB _ => False
    | .separatesBA _ => False := by
  native_decide

/-- The first coherence mismatch is the false outcome, where the noisy model has
the larger probability. The checker must therefore return the reverse orientation. -/
example :
    match coherenceChecked with
    | .agreement _ => False
    | .separatesAB _ => False
    | .separatesBA _ => True := by
  native_decide

end
