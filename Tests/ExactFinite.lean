import OntologySeparation.Recipes.Separation

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExperimentAccess

noncomputable section

def exactIdeal : Law := Law.dephasing 0 1
def exactNoisy : Law := Law.dephasing 1 2

example :
    ExactFinite.EquivalentQ exactBackend calibrationOnly exactIdeal exactNoisy := by
  intro r hr s o
  subst r
  cases s
  cases o <;> simp [exactBackend, outcomeProbability, calibration_probability]

example :
    Equivalent predict calibrationOnly exactIdeal exactNoisy :=
  ExactFinite.equivalent_of_exact exactBackend calibrationOnly exactIdeal exactNoisy (by
    intro r hr s o
    subst r
    cases s
    cases o <;> simp [exactBackend, outcomeProbability, calibration_probability])

example (a b : Law)
    (h : Equivalent predict calibrationOnly a b) :
    ExactFinite.EquivalentQ exactBackend calibrationOnly a b :=
  ExactFinite.exact_of_equivalent exactBackend calibrationOnly a b h

end
