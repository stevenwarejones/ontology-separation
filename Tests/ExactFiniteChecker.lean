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
  entries :=
    [⟨coherenceProbe, (), false⟩, ⟨coherenceProbe, (), true⟩]
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

def calibrationChecked :=
  certify exactBackend calibrationOnly calibrationGrid checkerIdeal checkerNoisy

def coherenceChecked :=
  certify exactBackend coherenceOnly coherenceGrid checkerIdeal checkerNoisy


def scanTag {entries : List (Entry Recipe binaryInterface)} :
    ScanResult exactBackend checkerIdeal checkerNoisy entries → Nat
  | .agreement _ => 0
  | .separatesAB _ _ _ => 1
  | .separatesBA _ _ _ => 2

/-- Exercise the scanner itself: the covered calibration list takes the agreement branch. -/
example :
    scanTag (scan exactBackend checkerIdeal checkerNoisy calibrationGrid.entries) = 0 := by
  norm_num [scanTag, scan, compareEntry, calibrationGrid, exactBackend,
    outcomeProbability, calibration_probability, checkerIdeal, checkerNoisy,
    Law.dephasing, Rate.fraction]

/-- A single true coherence entry has A>B, exercising the AB branch. -/
example :
    scanTag (scan exactBackend checkerIdeal checkerNoisy
      [⟨coherenceProbe, (), true⟩]) = 1 := by
  norm_num [scanTag, scan, compareEntry, exactBackend, outcomeProbability,
    coherence_probability, checkerIdeal, checkerNoisy, Law.dephasing, Rate.fraction]

/-- With the false coherence entry first, the full coherence grid exercises BA. -/
example :
    scanTag (scan exactBackend checkerIdeal checkerNoisy coherenceGrid.entries) = 2 := by
  norm_num [scanTag, scan, compareEntry, coherenceGrid, exactBackend,
    outcomeProbability, coherence_probability, checkerIdeal, checkerNoisy,
    Law.dephasing, Rate.fraction]

/-- The exact arithmetic behind the calibration agreement is checked directly. -/
example (o : Bool) :
    exactBackend.probability checkerIdeal calibrationProbe () o =
      exactBackend.probability checkerNoisy calibrationProbe () o := by
  cases o <;>
    simp [exactBackend, outcomeProbability, calibration_probability]

/-- The first coherence entry has the reverse orientation: the noisy model has
more probability on the false outcome. No compiler-native decision shortcut is used. -/
example :
    exactBackend.probability checkerIdeal coherenceProbe () false <
      exactBackend.probability checkerNoisy coherenceProbe () false := by
  norm_num [exactBackend, outcomeProbability, coherence_probability,
    checkerIdeal, checkerNoisy, Law.dephasing, Rate.fraction]

/-- Both automatic results are proof-bearing claims in the ordinary reporting vocabulary. -/
example : calibrationChecked.claim.statement :=
  calibrationChecked.sound

example : coherenceChecked.claim.statement :=
  coherenceChecked.sound

end
