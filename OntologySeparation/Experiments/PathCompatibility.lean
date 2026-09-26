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
    simp only [if_pos rfl, mul_one] at he
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
  simp only [he, quantum_realizes_table, Fintype.sum_bool] at hn
  norm_num [exactTable] at hn
  rw [hf,hm,hp] at hs
  rw [hf,hm] at ha
  rw [hf,hp] at hb
  refine ⟨hn, ?_, ?_, hb⟩ <;> linarith

end
end OntologySeparation.PathContextuality
