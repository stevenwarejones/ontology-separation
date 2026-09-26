import OntologySeparation.Experiments.PathContextualityQuantum

/-! Complete finite countermodels to dropping the representation premises.
An unchanged final marginal is not an identity-channel decomposition. -/
namespace OntologySeparation.PathContextuality
noncomputable section

def fairPreparation : FiniteDistribution Bool :=
  ⟨fun _ => 1/2, by intro b; norm_num, by norm_num [Fintype.sum_bool]⟩
def bitFinal (b : Bool) : Behavior binaryInterface :=
  coin (if b then 0 else 1) (by cases b <;> norm_num) (by cases b <;> norm_num)

/-- Prepare a fair bit; pointer is fair; reset the final bit to the pointer. -/
def invasiveModel : Model Bool where
  preparation := fairPreparation
  probe _ := {
    mass o := if o.2 = o.1 then 1/2 else 0
    nonneg o := by split_ifs <;> norm_num
    total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool] }
  final := bitFinal

theorem invasive_cap : invasiveModel.ResponseCap (1/2) := by
  intro l
  norm_num [Model.negative, invasiveModel, Fintype.sum_bool]

theorem invasive_statistics : invasiveModel.pF = 1/2 ∧
    invasiveModel.pMinus = 1/2 ∧
    (∑ b, invasiveModel.observed.prob () (b,true)) = 1/2 := by
  norm_num [Model.pF, Model.pMinus, Model.observed, FiniteDistribution.mean,
    invasiveModel, fairPreparation, bitFinal, coin, Fintype.sum_bool]

theorem unchanged_marginal_not_zero_disturbance : ¬ invasiveModel.Disturbance 0 := by
  intro h
  have hb := invasiveModel.bound (1/2) 0 (by norm_num) invasive_cap h
  rw [invasive_statistics.1, invasive_statistics.2.1] at hb
  norm_num at hb

/-- The bit never moves; the pointer reveals it. Averaging over the sole fair
preparation hides violation of the ontic fair-pointer cap. -/
def contextualPointer : Model Bool where
  preparation := fairPreparation
  probe l := {
    mass o := if o = (l,l) then 1 else 0
    nonneg o := by split_ifs <;> norm_num
    total := by simp }
  final := bitFinal

theorem contextual_identity : contextualPointer.Disturbance 0 := by
  refine ⟨fun l => ⟨fun j => if j = l then 1 else 0,
    by intro j; dsimp only; split_ifs <;> norm_num, by simp⟩, ?_⟩
  intro l j
  cases l <;> cases j <;> norm_num [contextualPointer]

theorem contextual_statistics : contextualPointer.pF = 1/2 ∧
    contextualPointer.pMinus = 1/2 ∧
    (∑ f, contextualPointer.observed.prob () (false,f)) = 1/2 := by
  norm_num [Model.pF, Model.pMinus, Model.observed, FiniteDistribution.mean,
    contextualPointer, fairPreparation, bitFinal, coin, Fintype.sum_bool]

theorem operational_fairness_not_response_cap : ¬ contextualPointer.ResponseCap (1/2) := by
  intro h
  have hb := h false
  norm_num [Model.negative, contextualPointer, Fintype.sum_bool] at hb

/-- Distinct failures of the premises reproduce the entire same joint table. -/
theorem countermodels_same_joint :
    ObservationallyEquivalent invasiveModel.observed contextualPointer.observed := by
  intro s o
  rcases o with ⟨m,f⟩
  cases m <;> cases f <;>
    norm_num [Model.observed, invasiveModel, contextualPointer,
      fairPreparation, bitFinal, coin, Fintype.sum_bool]
end
end OntologySeparation.PathContextuality
