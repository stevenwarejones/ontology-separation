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
/-- Exact reference table with the cap dropped. `false` is S (success), `true`
is F (failure). The identity-mixture disturbance and bypass rate are retained. -/
def dropCapModel : Model Bool where
  preparation := {
    mass l := if l then 576/625 else 49/625
    nonneg l := by cases l <;> norm_num
    total := by norm_num [Fintype.sum_bool] }
  probe l := {
    mass o := if l then
      (if o.1 then (if o.2 then 49/100 else 0)
       else (if o.2 then 49/100 else 1/50))
      else (if o.2 then 0 else (if o.1 then 144/1225 else 1081/1225))
    nonneg o := by cases l <;> rcases o with ⟨m,j⟩ <;>
      cases m <;> cases j <;> norm_num
    total := by cases l <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool] }
  final := bitFinal

/-- Dropping only the cap restores the entire quantum joint table while keeping
its bypass probability and disturbance weight, not merely a similar anomaly. -/
theorem drop_cap_realizes_quantum : dropCapModel.Disturbance (1/50) ∧
    dropCapModel.pF = 49/625 ∧
    ObservationallyEquivalent dropCapModel.observed quantumJoint ∧
    ¬ dropCapModel.ResponseCap (16/25) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun _ => ⟨fun j => if j then 0 else 1,
      by intro j; cases j <;> norm_num, by norm_num [Fintype.sum_bool]⟩, ?_⟩
    intro l j
    cases l <;> cases j <;> norm_num [dropCapModel]
  · norm_num [Model.pF, FiniteDistribution.mean, dropCapModel, bitFinal, coin,
      Fintype.sum_bool]
  · intro s o
    rw [quantum_realizes_table s o]
    rcases o with ⟨m,f⟩
    cases m <;> cases f <;>
      norm_num [Model.observed, dropCapModel, bitFinal, coin, exactTable, Fintype.sum_bool]
  · intro h
    have hs := h false
    norm_num [Model.negative, dropCapModel, Fintype.sum_bool] at hs

private theorem zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem two_ne_one : (2 : Fin 3) ≠ 1 := by decide

/-- Exact reference table with only disturbance dropped. States 0,1,2 are L,S,F;
L has stochastic bypass success 49/625, while S/F succeed/fail deterministically. -/
def dropDisturbanceModel : Model (Fin 3) where
  preparation := {
    mass l := if l = 0 then 1 else 0
    nonneg l := by split_ifs <;> norm_num
    total := by simp }
  probe l := {
    mass o := if l = 0 then
      (if o.2 = 1 then exactTable.prob () (o.1,true)
       else if o.2 = 2 then exactTable.prob () (o.1,false) else 0)
      else if o.2 = l then 1/2 else 0
    nonneg o := by
      split_ifs <;> first | exact exactTable.nonneg _ _ | norm_num
    total := by
      fin_cases l <;>
        norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ, zero_ne_two, two_ne_one, exactTable] }
  final l := coin (if l = 0 then 49/625 else if l = 1 then 1 else 0)
    (by fin_cases l <;> norm_num) (by fin_cases l <;> norm_num)

/-- Dropping only disturbance restores the entire quantum joint table at the
same bypass rate and response cap. The old disturbance premise is false. -/
theorem drop_disturbance_realizes_quantum :
    dropDisturbanceModel.ResponseCap (16/25) ∧ dropDisturbanceModel.pF = 49/625 ∧
    ObservationallyEquivalent dropDisturbanceModel.observed quantumJoint ∧
    ¬ dropDisturbanceModel.Disturbance (1/50) := by
  have hq : dropDisturbanceModel.ResponseCap (16/25) := by
    intro l
    fin_cases l <;>
      norm_num [Model.negative, dropDisturbanceModel, Fin.sum_univ_succ, zero_ne_two, two_ne_one, exactTable]
  have hf : dropDisturbanceModel.pF = 49/625 := by
    norm_num [Model.pF, FiniteDistribution.mean, dropDisturbanceModel, coin,
      Fin.sum_univ_succ]
  have he : ObservationallyEquivalent dropDisturbanceModel.observed quantumJoint := by
    intro s o
    rw [quantum_realizes_table s o]
    rcases o with ⟨m,f⟩
    cases m <;> cases f <;>
      norm_num [Model.observed, dropDisturbanceModel, coin, exactTable, Fin.sum_univ_succ, zero_ne_two, two_ne_one]
  exact ⟨hq, hf, he, fun hD => quantum_exclusion dropDisturbanceModel hq hD hf he⟩

end
end OntologySeparation.PathContextuality
