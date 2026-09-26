import OntologySeparation.Experiments.PathContextualityCountermodels

/-! Complete-table compatibility for the reference instrument. These are ontic
representation bounds; calibration residuals do not establish their premises. -/
namespace OntologySeparation.PathContextuality
noncomputable section
namespace Model
variable {Λ : Type} [Fintype Λ]

def pPlus (m : Model Λ) : ℝ := m.observed.prob () (true,true)

/-- The positive-success cell retains the diagonal mass that the negative cap
cannot absorb. No outcome determinism is assumed. -/
theorem positive_bound (m : Model Λ) (q d : ℝ) (hd : 0 ≤ d)
    (hq : m.ResponseCap q) (hD : m.Disturbance d) :
    (1-d-q)*m.pF ≤ m.pPlus := by
  classical
  obtain ⟨D,hD⟩ := hD
  have row (l : Λ) : (1-d-q)*(m.final l).prob () true ≤
      ∑ j, (m.probe l).mass (true,j)*(m.final j).prob () true := by
    have hn : (m.probe l).mass (false,l) ≤ q :=
      (Finset.single_le_sum (fun j _ => (m.probe l).nonneg (false,j))
        (Finset.mem_univ l)).trans (hq l)
    have he := hD l l
    simp at he
    have hp : 1-d-q ≤ (m.probe l).mass (true,l) := by
      nlinarith [mul_nonneg hd ((D l).nonneg l)]
    exact (mul_le_mul_of_nonneg_right hp ((m.final l).nonneg () true)).trans
      (Finset.single_le_sum (fun j _ => mul_nonneg ((m.probe l).nonneg (true,j))
        ((m.final j).nonneg () true)) (Finset.mem_univ l))
  calc
    (1-d-q)*m.pF = ∑ l, m.preparation.mass l*((1-d-q)*(m.final l).prob () true) := by
      simp only [pF, FiniteDistribution.mean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ m.pPlus := Finset.sum_le_sum fun l _ =>
      mul_le_mul_of_nonneg_left (row l) (m.preparation.nonneg l)

/-- The cap also bounds the entire negative marginal, not only its success cell. -/
theorem negative_marginal_bound (m : Model Λ) (q : ℝ) (hq : m.ResponseCap q) :
    (∑ f : Bool, m.observed.prob () (false,f)) ≤ q := by
  have he : (∑ f : Bool, m.observed.prob () (false,f)) =
      m.preparation.mean m.negative := by
    simp only [observed, FiniteDistribution.mean]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, (m.final j).normalized ()]
    simp
  rw [he]
  exact m.preparation.mean_le _ _ hq

/-- Ignoring the pointer, at most the disturbed mass can create new success. -/
theorem success_bound (m : Model Λ) (d : ℝ) (hd : 0 ≤ d)
    (hD : m.Disturbance d) : m.pMinus+m.pPlus ≤ m.pF+d*(1-m.pF) := by
  classical
  obtain ⟨D,hD⟩ := hD
  have row (l : Λ) :
      (∑ j, (m.probe l).mass (false,j)*(m.final j).prob () true) +
      (∑ j, (m.probe l).mass (true,j)*(m.final j).prob () true) ≤
      (1-d)*(m.final l).prob () true+d := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← add_mul, hD, add_mul]
    rw [Finset.sum_add_distrib]
    have hi : (∑ j, (1-d)*(if j=l then 1 else 0)*(m.final j).prob () true) =
        (1-d)*(m.final l).prob () true := by simp
    rw [hi]
    apply add_le_add le_rfl
    calc
      (∑ j, d*(D l).mass j*(m.final j).prob () true) =
          d*(D l).mean (fun j => (m.final j).prob () true) := by
        simp only [FiniteDistribution.mean, Finset.mul_sum, mul_assoc]
      _ ≤ d*1 := mul_le_mul_of_nonneg_left
        ((D l).mean_le _ _ (fun j => (m.final j).prob_le_one () true)) hd
      _ = d := mul_one d
  calc
    m.pMinus+m.pPlus = ∑ l, m.preparation.mass l*
        ((∑ j, (m.probe l).mass (false,j)*(m.final j).prob () true) +
         (∑ j, (m.probe l).mass (true,j)*(m.final j).prob () true)) := by
      simp only [pMinus, pPlus, observed, mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ l, m.preparation.mass l*((1-d)*(m.final l).prob () true+d) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (row l) (m.preparation.nonneg l)
    _ = m.pF+d*(1-m.pF) := by
      simp only [pF, FiniteDistribution.mean, mul_add, Finset.sum_add_distrib]
      simp_rw [mul_left_comm (m.preparation.mass _) (1-d), ← Finset.mul_sum]
      rw [← Finset.sum_mul, m.preparation.total]
      ring

/-- Conditional discrepancy propagation; the error budgets are hypotheses. -/
theorem robust_positive_bound (m : Model Λ) (q d epsB epsF b f : ℝ)
    (hd : 0 ≤ d) (hq : m.ResponseCap q) (hD : m.Disturbance d)
    (hb : |b-m.pPlus| ≤ epsB) (hf : |f-m.pF| ≤ epsF) :
    (1-d-q)*f-epsB-|1-d-q| *epsF ≤ b := by
  have h := m.positive_bound q d hd hq hD
  have hb' := (abs_le.mp hb).1
  have hf' : |(1-d-q)*(f-m.pF)| ≤ |1-d-q| *epsF := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg _)
  have hh := (abs_le.mp hf').2
  nlinarith
end Model

/-- Necessary inequalities for every finite model of the complete reference table. -/
theorem reference_necessary {Λ : Type} [Fintype Λ] (m : Model Λ) (q d : ℝ)
    (hd : 0 ≤ d) (hq : m.ResponseCap q) (hD : m.Disturbance d)
    (hf : m.pF = 49/625) (he : ObservationallyEquivalent m.observed quantumJoint) :
    337/625 ≤ q ∧ 1/50 ≤ d ∧
    1369/15625 ≤ q*(49/625)+d*(576/625) ∧
    (1-d-q)*(49/625) ≤ 144/15625 := by
  have hm : m.pMinus = 1369/15625 := by
    change m.observed.prob () (false,true) = _
    rw [he, quantum_realizes_table]
    rfl
  have hp : m.pPlus = 144/15625 := by
    change m.observed.prob () (true,true) = _
    rw [he, quantum_realizes_table]
    rfl
  have hn := m.negative_marginal_bound q hq
  have hs := m.success_bound d hd hD
  have ha := m.bound q d hd hq hD
  have hb := m.positive_bound q d hd hq hD
  simp only [Fintype.sum_bool] at hn
  rw [he () (false,true), he () (false,false),
    quantum_realizes_table () (false,true), quantum_realizes_table () (false,false)] at hn
  norm_num [exactTable] at hn
  rw [hf,hm,hp] at hs
  rw [hf,hm] at ha
  rw [hf,hp] at hb
  refine ⟨hn, ?_, ?_, hb⟩ <;> linarith

/-- F-to-S transition needed when S has negative response u. -/
def referenceFlow (u : ℝ) : ℝ := (1369/15625-(49/625)*u)/(576/625)

/-- Two-state attaining family, S=false and F=true. The parameter u is the
negative response at S; all four observed cells remain fixed. -/
def boundaryModel (u : ℝ) (hu0 : 337/625 ≤ u) (hu1 : u ≤ 1081/1225) : Model Bool where
  preparation := dropCapModel.preparation
  probe l := {
    mass o := if l then
      (if o.1 then (if o.2 then 51/100-referenceFlow u else 0)
       else (if o.2 then 49/100 else referenceFlow u))
      else (if o.1 then (if o.2 then 1-u-144/1225 else 144/1225)
       else (if o.2 then 0 else u))
    nonneg o := by
      cases l <;> rcases o with ⟨m,j⟩ <;> cases m <;> cases j <;>
        norm_num [referenceFlow] <;> linarith
    total := by
      cases l <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool] <;> ring }
  final := bitFinal

theorem boundary_statistics (u : ℝ) (hu0 : 337/625 ≤ u) (hu1 : u ≤ 1081/1225) :
    (boundaryModel u hu0 hu1).pF = 49/625 ∧
    ObservationallyEquivalent (boundaryModel u hu0 hu1).observed quantumJoint := by
  constructor
  · norm_num [Model.pF, FiniteDistribution.mean, boundaryModel, dropCapModel,
      bitFinal, coin, Fintype.sum_bool]
  · intro s o
    rw [quantum_realizes_table s o]
    rcases o with ⟨m,f⟩
    cases m <;> cases f <;>
      norm_num [Model.observed, boundaryModel, dropCapModel, bitFinal, coin,
        exactTable, Fintype.sum_bool, referenceFlow] <;> ring

theorem boundary_cap (u : ℝ) (hu0 : 337/625 ≤ u) (hu1 : u ≤ 1081/1225) :
    (boundaryModel u hu0 hu1).ResponseCap u := by
  intro l
  cases l <;> norm_num [Model.negative, boundaryModel, Fintype.sum_bool, referenceFlow] <;>
    linarith

private def moveKernel (l : Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteDistribution Bool where
  mass j := if j=l then 1-p else p
  nonneg j := by split_ifs <;> linarith
  total := by cases l <;> norm_num [Fintype.sum_bool]

/-- The attaining family's two flip rates are bounded by the chosen disturbance.
The extra disturbance is absorbed into the stochastic residual kernel. -/
theorem boundary_disturbance (u d : ℝ) (hu0 : 337/625 ≤ u) (hu1 : u ≤ 1081/1225)
    (hd : 0 < d) (hS : 1-u-144/1225 ≤ d) (hF : referenceFlow u ≤ d) :
    (boundaryModel u hu0 hu1).Disturbance d := by
  let flip : Bool → ℝ := fun l => if l then referenceFlow u else 1-u-144/1225
  have hf0 (l : Bool) : 0 ≤ flip l := by
    cases l <;> dsimp [flip, referenceFlow] <;> linarith
  have hf1 (l : Bool) : flip l ≤ d := by
    cases l <;> assumption
  refine ⟨fun l => moveKernel l (flip l/d) (div_nonneg (hf0 l) hd.le)
    ((div_le_one hd).mpr (hf1 l)), ?_⟩
  intro l j
  cases l <;> cases j <;>
    norm_num [boundaryModel, moveKernel, flip, referenceFlow] <;>
    field_simp [ne_of_gt hd] <;> ring

/-- Four linear inequalities describing the complete reference-data region.
For probability parameters, intersect this region with 0≤q,d≤1. -/
def ReferenceRegion (q d : ℝ) : Prop :=
  337/625 ≤ q ∧ 1/50 ≤ d ∧
  1369/15625 ≤ q*(49/625)+d*(576/625) ∧
  (1-d-q)*(49/625) ≤ 144/15625

/-- Every point of the reference region has a two-state model. Combined with
`reference_necessary`, this covers arbitrary finite cardinalities for this table;
it is not a general two-state reduction theorem. -/
theorem reference_region_sufficient (q d : ℝ) (h : ReferenceRegion q d) :
    ∃ m : Model Bool, m.ResponseCap q ∧ m.Disturbance d ∧
      m.pF = 49/625 ∧ ObservationallyEquivalent m.observed quantumJoint := by
  rcases h with ⟨hq,hd,ha,hb⟩
  have hd0 : 0 < d := by linarith
  by_cases hq1 : q ≤ 1081/1225
  · refine ⟨boundaryModel q hq hq1, boundary_cap _ _ _, ?_,
      (boundary_statistics _ _ _).1, (boundary_statistics _ _ _).2⟩
    apply boundary_disturbance q d hq hq1 hd0
    · nlinarith
    · dsimp [referenceFlow]
      linarith
  · have hlo : (337/625 : ℝ) ≤ 1081/1225 := by norm_num
    have hhi : (1081/1225 : ℝ) ≤ 1081/1225 := le_rfl
    refine ⟨boundaryModel (1081/1225) hlo hhi, ?_, ?_,
      (boundary_statistics _ _ _).1, (boundary_statistics _ _ _).2⟩
    · intro l
      exact (boundary_cap _ hlo hhi l).trans (by linarith)
    · apply boundary_disturbance _ d hlo hhi hd0
      · linarith
      · norm_num [referenceFlow]
        exact hd

/-- Exact two-state feasibility, with a necessity proof valid at every finite
cardinality. The displayed region is therefore the finite-model frontier. -/
theorem reference_compatible_iff (q d : ℝ) (hd : 0 ≤ d) :
    (∃ m : Model Bool, m.ResponseCap q ∧ m.Disturbance d ∧
      m.pF = 49/625 ∧ ObservationallyEquivalent m.observed quantumJoint) ↔
    ReferenceRegion q d := by
  constructor
  · rintro ⟨m,hq,hD,hf,he⟩
    exact reference_necessary m q d hd hq hD hf he
  · exact reference_region_sufficient q d

/-- Feasibility over any finite ontology, with an explicit two-state attainer
for every feasible point. No cardinality bound is assumed in the forward direction. -/
theorem reference_finite_compatible_iff (q d : ℝ) (hd : 0 ≤ d) :
    (∃ (Λ : Type) (inst : Fintype Λ), letI := inst;
      ∃ m : Model Λ, m.ResponseCap q ∧ m.Disturbance d ∧
        m.pF = 49/625 ∧ ObservationallyEquivalent m.observed quantumJoint) ↔
    ReferenceRegion q d := by
  constructor
  · rintro ⟨Λ, inst, m, hq, hD, hf, he⟩
    letI := inst
    exact reference_necessary m q d hd hq hD hf he
  · intro h
    exact ⟨Bool, inferInstance, reference_region_sufficient q d h⟩

/-- At fixed q=16/25, the full table forces a substantially larger d than
inverting the negative-success inequality alone. -/
theorem reference_disturbance_lower {Λ : Type} [Fintype Λ] (m : Model Λ) (d : ℝ)
    (hd : 0 ≤ d) (hq : m.ResponseCap (16/25)) (hD : m.Disturbance d)
    (hf : m.pF = 49/625) (he : ObservationallyEquivalent m.observed quantumJoint) :
    297/1225 ≤ d := by
  have h := (reference_necessary m (16/25) d hd hq hD hf he).2.2.2
  linarith

/-- Attainment of the complete-table minimum at the reference cap. -/
theorem reference_disturbance_attained :
    ∃ m : Model Bool, m.ResponseCap (16/25) ∧ m.Disturbance (297/1225) ∧
      m.pF = 49/625 ∧ ObservationallyEquivalent m.observed quantumJoint := by
  let m := boundaryModel (16/25) (by norm_num) (by norm_num)
  refine ⟨m, boundary_cap _ _ _, ?_, (boundary_statistics _ _ _).1,
    (boundary_statistics _ _ _).2⟩
  exact boundary_disturbance _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num [referenceFlow])

end
end OntologySeparation.PathContextuality
