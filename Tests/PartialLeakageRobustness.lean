import OntologySeparation.Experiments.PartialLeakageRobustness
import Mathlib.Tactic

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.PartialLeakage

noncomputable section

def robustPoint : Mechanism :=
  ⟨Rate.fraction 1 2, Rate.fraction 3 4⟩

example : realGap (1 / 2 : ℝ) (3 / 4 : ℝ) = 3 / 16 := by
  norm_num [realGap]

example : 0 < realGap (1 / 2 : ℝ) (3 / 4 : ℝ) := by
  norm_num [realGap]

example :
    probability robustPoint.wignerLaw coherenceProbe -
      probability friendLaw coherenceProbe = 3 / 16 := by
  norm_num [recovery_gap, robustPoint, Rate.fraction]

example :
    ExperimentAccess.Separator RecipeSeparation.predict
      (fun r => r = coherenceProbe) robustPoint.wignerLaw friendLaw :=
  separator robustPoint (by norm_num [robustPoint, Rate.fraction])
    (by norm_num [robustPoint, Rate.fraction])


-- Upper edges are included: the positive region is (0,1] × (0,1].
example : 0 < realGap 1 1 := by norm_num [realGap]

-- These are real physical channels, not only a cast of a rational evaluator.
example :
    (Qubit.experiment (Qubit.dephase
      (realNoise 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)))).behavior.prob () true -
    (Qubit.experiment (Qubit.dephase ⟨1, by norm_num, by norm_num⟩)).behavior.prob () true =
    realGap 1 1 := real_channel_gap 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
