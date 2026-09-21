import Coherence
open OntologySeparation CoherenceStudy
-- A cell cannot silently move to another procedure or another scenario.
example : True := by
  fail_if_success
    have wrong : scenario.question.score (scenario.interpret .coherent .phaseFlipped) = (1 : ℝ) := by
      exact comparison.predictions.correct .coherent .direct
  fail_if_success
    have wrongValue : Scenario.ExactPredictions scenario :=
      ⟨fun _ _ => 0, predictions_correct⟩
  trivial
example : predicted .partiallyDephased .repeated = 5/8 := by norm_num [predicted, strength]
example : predicted .dephased .shielded = 1 := by norm_num [predicted]
