import OntologySeparation.Operational.Qubit
namespace MyLaboratory
open OntologySeparation
noncomputable section
structure TwoStageModel where
  first : Qubit.Noise
  second : Qubit.Noise
def predict (m : TwoStageModel) : Behavior binaryInterface :=
  (Qubit.experiment ((Qubit.dephase m.first).thenDo (Qubit.dephase m.second))).behavior
def FullyCoherent (m : TwoStageModel) : Prop := m.first.strength = 0 ∧ m.second.strength = 0
theorem coherent_prediction (m : TwoStageModel) (h : FullyCoherent m) : (predict m).prob () true = 1 := by
  unfold predict
  rw [Qubit.twice_dephased, h.1, h.2]
  norm_num
def fullyDephased : TwoStageModel := ⟨⟨1, by norm_num, by norm_num⟩, ⟨1, by norm_num, by norm_num⟩⟩
theorem dephased_prediction : (predict fullyDephased).prob () true = 1/2 := by
  unfold predict
  rw [Qubit.twice_dephased]
  norm_num [fullyDephased]
def result : Prediction Qubit.question (predict fullyDephased) := ⟨1/2, dephased_prediction⟩
end
end MyLaboratory
