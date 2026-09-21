import OntologySeparation
namespace OntologySeparation.OperationalTests
noncomputable section
def unitPrior : FiniteDistribution Unit := ⟨fun _ => 1, by simp, by simp⟩
def singletModel : OperationalBell.Model Unit := ⟨fun _ => unitPrior, fun _ => Bell.singletBehavior⟩
theorem singlet_independent : OperationalBell.MeasurementIndependent singletModel := by
  intro s t l; rfl
theorem singlet_local : OperationalBell.ParameterIndependent singletModel := by
  intro l
  exact Shared.singlet_noSignaling Bell.alice Bell.bob
theorem singlet_same_score : Bell.score singletModel.behavior = 1502/625 := by
  have h : singletModel.behavior = Bell.singletBehavior := by
    have he : singletModel.behavior.prob = Bell.singletBehavior.prob := by
      funext s o
      simp [OperationalBell.Model.behavior, singletModel, unitPrior]
    cases ha : singletModel.behavior
    cases hb : Bell.singletBehavior
    simp only [ha, hb] at he
    cases he
    rfl
  rw [h, Bell.singlet_score]
theorem singlet_not_screened : ¬ OperationalBell.OutcomeIndependent singletModel := by
  intro h
  have hb := OperationalBell.chsh_bound singletModel h singlet_local singlet_independent
  rw [singlet_same_score] at hb
  norm_num at hb
theorem rejected_realism_profile_realized :
    (AssumptionProfile.mk .reject .unspecified .require .require).Realizable
      (OperationalBell.vocabulary (Λ := Unit)) :=
  ⟨singletModel, singlet_not_screened, trivial, singlet_local, singlet_independent⟩
def prFriends : FriendRecords.Model Unit where
  preparation := fun _ => unitPrior
  response := fun _ => LF.prComponent.behavior
  charlie := fun _ => false
  debbie := fun _ => false
theorem prFriends_records : FriendRecords.ReadableRecords prFriends :=
  ⟨fun _ y => LF.prComponent.read_charlie y, fun _ x => LF.prComponent.read_debbie x⟩
theorem prFriends_local : FriendRecords.ConditionalLocality prFriends := fun _ => Shared.lf_noSignaling LF.prComponent
theorem prFriends_independent : FriendRecords.IndependentPreparation prFriends := by
  intro s t l; rfl
theorem prFriends_bound : RealQuantum.genuineLF prFriends.behavior ≤ 6 :=
  FriendRecords.bound prFriends prFriends_records prFriends_local prFriends_independent

def noNoise : Qubit.Noise := ⟨0, by norm_num, by norm_num⟩
-- Deliberately wrong claims must fail before they can be packaged.
example : True := by
  fail_if_success
    have wrong : Prediction Qubit.question (Qubit.experiment (Qubit.dephase noNoise)).behavior :=
      ⟨0, (Qubit.prediction noNoise).correct⟩
  trivial
example : True := by
  fail_if_success
    have wrong : Prediction Qubit.question (Qubit.experiment Qubit.phaseFlip).behavior := Qubit.prediction noNoise
  trivial
example : ¬ (AssumptionProfile.mk .require .require .reject .require).Extends OperationalBell.screeningOffProfile := by decide
example : (binaryProfiles.filter fun p => decide (p.Extends OperationalBell.screeningOffProfile)).length = 2 := by decide
example : (binaryProfiles.filter fun p => decide (p.Extends FriendRecords.profile)).length = 2 := by decide
end
end OntologySeparation.OperationalTests
