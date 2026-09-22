import OntologySeparation.Adapters.FiniteCircuit
import OntologySeparation.Experiments.RecordAccess

open OntologySeparation
open OntologySeparation.FiniteCircuit
open OntologySeparation.RecordAccess

noncomputable section

def recordDephase : QIT.Channel Registers Registers :=
  QIT.Channel.measure (QIT.POVM.coordinate Registers)

def twoDephasings : Circuit Registers := [recordDephase, recordDephase]

/-- A genuinely two-step circuit compiles in the stated execution order. -/
example (ρ : QIT.State Registers) :
    twoDephasings.channel.applyState ρ =
      recordDephase.applyState (recordDephase.applyState ρ) := by
  rw [twoDephasings, Circuit.apply_cons, Circuit.apply_cons, Circuit.apply_nil]

/-- Any compiled multi-step circuit followed by a complete POVM remains a
normalized experiment through the existing FiniteQuantum semantics. -/
example :
    ∑ o, (FiniteCircuit.test twoDephasings (QIT.POVM.coordinate Registers)).prob coherent o = 1 :=
  FiniteCircuit.test_normalized twoDephasings (QIT.POVM.coordinate Registers) coherent

end
