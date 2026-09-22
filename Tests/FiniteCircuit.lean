import OntologySeparation.Adapters.FiniteCircuit
import OntologySeparation.Experiments.RecordAccess

open OntologySeparation
open OntologySeparation.FiniteCircuit
open OntologySeparation.RecordAccess

noncomputable section

def recordDephase : QIT.Channel Registers Registers :=
  QIT.Channel.measure (QIT.POVM.coordinate Registers)

def recoveryMeasure : QIT.Channel Registers Registers :=
  QIT.Channel.measure recoveryReadout

def dephaseThenRecovery : Circuit Registers := [recordDephase, recoveryMeasure]
def recoveryThenDephase : Circuit Registers := [recoveryMeasure, recordDephase]

example (ρ : QIT.State Registers) :
    dephaseThenRecovery.channel.applyState ρ =
      recoveryMeasure.applyState (recordDephase.applyState ρ) := by
  rw [dephaseThenRecovery, Circuit.apply_cons, Circuit.apply_cons, Circuit.apply_nil]

/-- The two execution orders are physically distinguishable on the coherent
record. Dephase→recovery gives the established dephased recovery probability. -/
example :
    (FiniteCircuit.test dephaseThenRecovery
      (QIT.POVM.coordinate Registers)).prob coherent (false, false) = 337 / 625 := by
  rw [FiniteCircuit.test_prob]
  rw [dephaseThenRecovery, Circuit.apply_cons, Circuit.apply_cons, Circuit.apply_nil]
  change ((QIT.POVM.coordinate Registers).prob
    (recoveryMeasure.applyState dephased) (false, false) : ℝ) = 337 / 625
  rw [FiniteQuantum.coordinate_after_measure]
  exact dephased_recovery

/-- Reversing the same two channels gives probability one for the same final
coordinate outcome, so the regression would fail if execution order were reversed. -/
example :
    (FiniteCircuit.test recoveryThenDephase
      (QIT.POVM.coordinate Registers)).prob coherent (false, false) = 1 := by
  rw [FiniteCircuit.test_prob]
  rw [recoveryThenDephase, Circuit.apply_cons, Circuit.apply_cons, Circuit.apply_nil]
  change ((QIT.POVM.coordinate Registers).prob
    (recordDephase.applyState (recoveryMeasure.applyState coherent))
    (false, false) : ℝ) = 1
  rw [FiniteQuantum.coordinate_after_measure]
  rw [FiniteQuantum.coordinate_after_measure]
  exact coherent_recovery

/-- Any compiled multi-step circuit followed by a complete POVM remains a
normalized experiment through the existing FiniteQuantum semantics. -/
example :
    ∑ o, (FiniteCircuit.test dephaseThenRecovery
      (QIT.POVM.coordinate Registers)).prob coherent o = 1 :=
  FiniteCircuit.test_normalized dephaseThenRecovery
    (QIT.POVM.coordinate Registers) coherent

end
