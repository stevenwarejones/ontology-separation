import OntologySeparation.Signaling

namespace OntologySeparation.SignalingTests
open HiddenInfluence
open scoped BigOperators

example : (SignalingStudy.design 0).ceiling = 6 := by norm_num [SignalingStudy.Study.ceiling, SignalingStudy.design]
example : (SignalingStudy.design (1/8)).ceiling = 7 := by norm_num [SignalingStudy.Study.ceiling, SignalingStudy.design]
example : (SignalingStudy.design (1/4)).ceiling = 8 := by norm_num [SignalingStudy.Study.ceiling, SignalingStudy.design]
example : (SignalingStudy.design (1/2)).usedSignaling = 1/4 := by
  norm_num [SignalingStudy.Study.usedSignaling, SignalingStudy.design]

-- Exact probabilities, including a direction with the opposite signed change.
example : difference Sharp.model.behavior 5 0 = 1/8 := by rw [Sharp.difference_exact]; norm_num [Sharp.diffNumerator]
example : difference Sharp.model.behavior 5 1 = -(1/8) := by rw [Sharp.difference_exact]; norm_num [Sharp.diffNumerator]
-- TV includes the factor 1/2; raw L1 distance is twice as large.
example : (∑ o, |difference Sharp.model.behavior 5 o|) = 1/2 := by
  have h := Sharp.tv_exact 5
  norm_num [tv] at h
  linarith
example : ¬ Within Sharp.model.behavior 0 := by
  intro h
  have := h 5
  rw [Sharp.tv_exact] at this
  norm_num at this
example : ¬ (∀ m : Model, score m.behavior ≤ 6+7*m.signaling) := by
  intro h
  have := coefficient_optimal 7 h
  norm_num at this

-- Bound and attainer cannot silently use different predicates or values.
example : ¬ Nonempty (SharpOptimum (fun _ : Unit => False) (fun _ => 0) 0) := by
  rintro ⟨s⟩
  exact s.satisfies
example : ¬ Nonempty (SharpOptimum (fun _ : Unit => True) (fun _ => 0) 1) := by
  rintro ⟨s⟩
  have := s.attains
  norm_num at this

-- Adopter supplies named outputs and ordinary finite distributions, no LP rows.
def zeroStrategy : Strategy := ⟨false, false, false, false, false, false⟩
noncomputable def zeroDistribution : FiniteDistribution Strategy where
  mass s := if s = zeroStrategy then 1 else 0
  nonneg s := by split <;> norm_num
  total := by simp
noncomputable def namedModel : Model := Model.fromStrategies (fun _ => zeroDistribution)
example : ∀ s, (∑ o, namedModel.behavior.prob s o) = 1 := namedModel.behavior.normalized

end OntologySeparation.SignalingTests
