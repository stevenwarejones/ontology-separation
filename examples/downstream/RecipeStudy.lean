import OntologySeparation.Recipes

open OntologySeparation.Recipes

-- A single recipe has the same preparation, operation order and readout in every row.
-- Fractions are numerator/denominator: zero denominators and rates above one fail.
-- No predicted formulas or user-written proofs are needed.
def recipeStudy := compare "Coherence: one recipe, several physical laws"
  [Law.dephasing 0 1, Law.dephasing 1 2, Law.dephasing 1 1]
  [ { prepare := .plus, steps := [.expose], measure := .x },
    { prepare := .plus, steps := [.phaseFlip, .expose], measure := .x },
    { prepare := .plus, steps := [.hadamard, .expose, .hadamard], measure := .x },
    { prepare := .plus, steps := [.expose, .expose], measure := .x } ]

#export_scenario recipeStudy
