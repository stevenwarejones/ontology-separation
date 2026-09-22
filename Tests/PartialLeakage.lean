import OntologySeparation.Experiments.PartialLeakage
import Mathlib.Tactic

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.PartialLeakage

def halfVisibility : Mechanism :=
  ⟨Rate.fraction 1 2, Rate.of 1⟩

def halfRecovery : Mechanism :=
  ⟨Rate.of 1, Rate.fraction 1 2⟩

example : probability halfVisibility.wignerLaw coherenceProbe = 3 / 4 := by
  norm_num [recovery_probability, halfVisibility, Rate.fraction, Rate.of]

example : probability halfRecovery.wignerLaw coherenceProbe = 3 / 4 := by
  norm_num [recovery_probability, halfRecovery, Rate.fraction, Rate.of]

example : probability halfVisibility.wignerLaw calibrationProbe =
    probability friendLaw calibrationProbe :=
  calibration_agreement halfVisibility

example : probability halfVisibility.wignerLaw coherenceProbe -
    probability friendLaw coherenceProbe = 1 / 4 := by
  norm_num [recovery_gap, halfVisibility, Rate.fraction, Rate.of]
