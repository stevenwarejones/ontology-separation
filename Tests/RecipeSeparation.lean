import OntologySeparation.Recipes.Separation
import Mathlib.Tactic.NormNum

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExperimentAccess

noncomputable section

def adapterIdeal : Law := Law.dephasing 0 1
def adapterNoisy : Law := Law.dephasing 1 2

example (m : Law) :
    outcomeProbability m calibrationProbe true = 1 := by
  simp [outcomeProbability, calibration_probability]

example (m : Law) :
    outcomeProbability m calibrationProbe false = 0 := by
  simp [outcomeProbability, calibration_probability]

example :
    Equivalent predict calibrationOnly adapterIdeal adapterNoisy :=
  restricted_equivalent _ _

def adapterSeparator :
    Separator predict calibrationAndCoherence adapterIdeal adapterNoisy :=
  expandedSeparator _ _ (by
    norm_num [adapterIdeal, adapterNoisy, Law.dephasing, Rate.fraction])

example : adapterSeparator.gap = (1 / 4 : ℝ) := by
  change (((adapterNoisy.exposure.value - adapterIdeal.exposure.value) / 2 : ℚ) : ℝ) = 1 / 4
  norm_num [adapterIdeal, adapterNoisy, Law.dephasing, Rate.fraction]

example :
    ¬ Equivalent predict calibrationAndCoherence adapterIdeal adapterNoisy :=
  adapterSeparator.not_equivalent

example :
    (coherenceClaim adapterNoisy).quantity = some (3 / 4) := by
  change some (probability adapterNoisy coherenceProbe) = some (3 / 4)
  rw [coherence_probability]
  norm_num [adapterNoisy, Law.dephasing, Rate.fraction]

end
