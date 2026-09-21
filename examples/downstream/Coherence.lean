import OntologySeparation.Core.Scenario
import OntologySeparation.Operational.Qubit

/-! Copy this file to define a scenario in your own project. No upstream registry edits.
These laws specify an effective channel per exposure, not an ontology of observers. -/
namespace CoherenceStudy
open OntologySeparation
inductive Model where
  | coherent | partiallyDephased | dephased
  deriving DecidableEq
inductive Protocol where
  | direct | phaseFlipped | shielded | repeated
  deriving DecidableEq
/-- Lost coherence per exposure: x becomes (1-p)x, while z stays fixed. -/
def strength : Model → ℚ
  | .coherent => 0
  | .partiallyDephased => 1/2
  | .dephased => 1
noncomputable def noise (m : Model) : Qubit.Noise :=
  ⟨(strength m : ℝ), by cases m <;> norm_num [strength],
    by cases m <;> norm_num [strength]⟩
noncomputable def procedure (m : Model) : Protocol → Procedure Qubit.State Qubit.State
  | .direct => Qubit.dephase (noise m)
  | .phaseFlipped => Qubit.phaseFlip.thenDo (Qubit.dephase (noise m))
  | .shielded => (Qubit.hadamard.thenDo (Qubit.dephase (noise m))).thenDo Qubit.hadamard
  | .repeated => (Qubit.dephase (noise m)).thenDo (Qubit.dephase (noise m))
/-- Each case prepares |+>, runs the chosen procedure, and measures X. -/
noncomputable def scenario : Scenario Model Protocol :=
  ⟨Qubit.question, fun m p => (Qubit.experiment (procedure m p)).behavior⟩
def predicted (m : Model) : Protocol → ℚ
  | .direct => 1 - strength m / 2
  | .phaseFlipped => strength m / 2
  | .shielded => 1
  | .repeated => (1 + (1-strength m)*(1-strength m))/2
/-- The one proof obligation that connects the whole numeric table to its physics. -/
theorem predictions_correct (m : Model) (p : Protocol) :
    scenario.question.score (scenario.interpret m p) = (predicted m p : ℝ) := by
  cases p with
  | direct =>
    change (Qubit.experiment (Qubit.dephase (noise m))).behavior.prob () true = _
    have h := (Qubit.prediction (noise m)).correct
    change (Qubit.experiment (Qubit.dephase (noise m))).behavior.prob () true =
      1 - (noise m).strength / 2 at h
    rw [h]
    cases m <;> norm_num [predicted, noise, strength]
  | phaseFlipped =>
    change (Qubit.experiment (Qubit.phaseFlip.thenDo (Qubit.dephase (noise m)))).behavior.prob () true = _
    rw [Qubit.phase_then_dephase]
    cases m <;> norm_num [predicted, noise, strength]
  | shielded =>
    change (Qubit.experiment ((Qubit.hadamard.thenDo (Qubit.dephase (noise m))).thenDo Qubit.hadamard)).behavior.prob () true = _
    rw [Qubit.protected_dephasing]
    norm_num [predicted]
  | repeated =>
    change (Qubit.experiment ((Qubit.dephase (noise m)).thenDo (Qubit.dephase (noise m)))).behavior.prob () true = _
    rw [Qubit.twice_dephased]
    cases m <;> norm_num [predicted, noise, strength]
def comparison : Scenario.Comparison scenario where
  title := "Coherence laws × experimental procedures"
  description := "Probability of + in X readout after preparing |+>. Each exposure maps (x,z) to ((1-p)x,z). The three effective laws use p=0, 1/2, and 1. These are calculated model predictions, not measured results or classifications of quantum interpretations."
  models := [("Preserved coherence (p=0)", .coherent),
    ("Partial dephasing (p=1/2)", .partiallyDephased), ("Complete dephasing (p=1)", .dephased)]
  protocols := [("One exposure", .direct), ("Phase flip, then exposure", .phaseFlipped),
    ("H, exposure, H", .shielded), ("Two exposures", .repeated)]
  models_nonempty := by decide
  protocols_nonempty := by decide
  predictions := ⟨predicted, predictions_correct⟩
/-- One procedure distinguishes these two concrete channel models. -/
theorem direct_separates :
    scenario.question.score (scenario.interpret .coherent .direct) ≠
    scenario.question.score (scenario.interpret .dephased .direct) := by
  rw [predictions_correct, predictions_correct]
  norm_num [predicted, strength]
/-- The protected statistic is insensitive to all three models. -/
theorem protected_equal (a b : Model) :
    scenario.question.score (scenario.interpret a .shielded) =
    scenario.question.score (scenario.interpret b .shielded) := by
  rw [predictions_correct, predictions_correct]
  rfl
end CoherenceStudy
