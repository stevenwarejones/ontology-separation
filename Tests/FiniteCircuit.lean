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

/-- Two physically different measurement channels make execution order visible
in the expected compiled expression. -/
def dephaseThenRecovery : Circuit Registers := [recordDephase, recoveryMeasure]

example (ρ : QIT.State Registers) :
    dephaseThenRecovery.channel.applyState ρ =
      recoveryMeasure.applyState (recordDephase.applyState ρ) := by
  rw [dephaseThenRecovery, Circuit.apply_cons, Circuit.apply_cons, Circuit.apply_nil]

/-- Any compiled multi-step circuit followed by a complete POVM remains a
normalized experiment through the existing FiniteQuantum semantics. -/
example :
    ∑ o, (FiniteCircuit.test dephaseThenRecovery
      (QIT.POVM.coordinate Registers)).prob coherent o = 1 :=
  FiniteCircuit.test_normalized dephaseThenRecovery
    (QIT.POVM.coordinate Registers) coherent

end
