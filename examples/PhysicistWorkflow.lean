import OntologySeparation

/-! Edit physical parameters and operation order. No catalog registration needed. -/
namespace PhysicistWorkflow
open OntologySeparation
noncomputable section
def weakNoise : Qubit.Noise := ⟨1/4, by norm_num, by norm_num⟩
def strongNoise : Qubit.Noise := ⟨1/2, by norm_num, by norm_num⟩
def twoStage := Qubit.experiment ((Qubit.dephase weakNoise).thenDo (Qubit.dephase strongNoise))
theorem twoStage_prediction : twoStage.behavior.prob () true = 11/16 := by
  rw [show twoStage = Qubit.experiment
    ((Qubit.dephase weakNoise).thenDo (Qubit.dephase strongNoise)) from rfl, Qubit.twice_dephased]
  norm_num [weakNoise, strongNoise]
def phaseExperiment := Qubit.experiment (Qubit.phaseFlip.thenDo (Qubit.dephase weakNoise))
theorem phase_prediction : phaseExperiment.behavior.prob () true = 1/8 := by
  rw [show phaseExperiment = Qubit.experiment
    (Qubit.phaseFlip.thenDo (Qubit.dephase weakNoise)) from rfl, Qubit.phase_then_dephase]
  norm_num [weakNoise]
def phaseResult : Prediction Qubit.question phaseExperiment.behavior := ⟨1/8, phase_prediction⟩
theorem bell_conclusion {Λ : Type} [Fintype Λ] (m : OperationalBell.Model Λ)
    (screeningOff : OperationalBell.OutcomeIndependent m)
    (localResponses : OperationalBell.ParameterIndependent m)
    (independentChoices : OperationalBell.MeasurementIndependent m) : Bell.score m.behavior ≤ 2 :=
  OperationalBell.chsh_bound m screeningOff localResponses independentChoices
theorem friend_conclusion {Λ : Type} [Fintype Λ] (m : FriendRecords.Model Λ)
    (records : FriendRecords.ReadableRecords m)
    (localResponses : FriendRecords.ConditionalLocality m)
    (independentChoices : FriendRecords.IndependentPreparation m) : RealQuantum.genuineLF m.behavior ≤ 6 :=
  FriendRecords.bound m records localResponses independentChoices
def allRequired : AssumptionProfile := ⟨.require, .require, .require, .require⟩
def stricterBell {Λ : Type} [Fintype Λ] :=
  (OperationalBell.certified (Λ := Λ)).under allRequired (by decide)
def flipBit : Channel Bool Bool := Channel.deterministic not
def flipTwice : Channel Bool Bool := flipBit.andThen flipBit
theorem flipTwice_restores (b : Bool) : (flipTwice b).mass b = 1 := by
  cases b <;> simp [flipTwice, flipBit, Channel.andThen, Channel.deterministic]
end
end PhysicistWorkflow
