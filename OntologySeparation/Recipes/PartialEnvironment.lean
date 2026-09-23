import OntologySeparation.Experiments.PartialEnvironment

namespace OntologySeparation.PartialEnvironment
noncomputable section

/-- A uniform study with nonnegative pointwise probability allowances.
`overlapFloor` concerns the inaccessible branch record, not a fraction of qubits. -/
structure Study where
  overlapFloor : ℚ
  loss : ℚ
  slack : ℚ
  overlapNonneg : 0 ≤ overlapFloor
  overlapLeOne : overlapFloor ≤ 1
  lossNonneg : 0 ≤ loss
  slackNonneg : 0 ≤ slack
  fits : loss + slack < 12/25 * overlapFloor

def design (overlapFloor loss slack : ℚ)
    (overlapNonneg : 0 ≤ overlapFloor := by norm_num)
    (overlapLeOne : overlapFloor ≤ 1 := by norm_num)
    (lossNonneg : 0 ≤ loss := by norm_num)
    (slackNonneg : 0 ≤ slack := by norm_num)
    (fits : loss + slack < 12/25 * overlapFloor := by norm_num) : Study :=
  ⟨overlapFloor, loss, slack, overlapNonneg, overlapLeOne, lossNonneg, slackNonneg, fits⟩

def Study.worstModel (s : Study) : Leakage :=
  Leakage.ofOverlap s.overlapFloor (by exact_mod_cast s.overlapNonneg)
    (by exact_mod_cast s.overlapLeOne)

/-- The selected readout works throughout the class, without selecting it from
the hidden model. The scalar allowances still need external justification. -/
theorem Study.uniformly_resolves (s : Study) (m : Leakage)
    (hm : (s.overlapFloor : ℝ) ≤ m.overlap) :
    Resolves m test s.loss s.slack := by
  have h : ((s.loss + s.slack : ℚ) : ℝ) < ((12/25 * s.overlapFloor : ℚ) : ℝ) := by
    exact_mod_cast s.fits
  push_cast at h
  unfold Resolves
  rw [coherent_probability, collapsed_probability]
  linarith

def Study.capacity (s : Study) : Claim := .exact
  ((coherent s.worstModel).normalizedTraceDistance (collapsed s.worstModel))
  (12/25 * s.overlapFloor) (by rw [distance_exact]; simp [Study.worstModel, Leakage.ofOverlap])

def Study.coherentProbability (s : Study) : Claim := .exact
  (test.prob (coherent s.worstModel) true) (1/2 + 12/25 * s.overlapFloor)
  (by rw [coherent_probability]; simp [Study.worstModel, Leakage.ofOverlap])

def Study.collapsedProbability (s : Study) : Claim := .exact
  (test.prob (collapsed s.worstModel) true) (1/2)
  (by rw [collapsed_probability]; norm_num)

def Study.margin (s : Study) : Claim := .exact
  (test.prob (coherent s.worstModel) true - s.loss -
    (test.prob (collapsed s.worstModel) true + s.slack))
  (12/25 * s.overlapFloor - s.loss - s.slack)
  (by rw [coherent_probability, collapsed_probability]
      simp [Study.worstModel, Leakage.ofOverlap]; ring)

def Study.bound (s : Study) : Claim := .realizedBound
  (fun _ : FiniteQuantum.Test Accessible Accessible Bool => True)
  (fun t => t.prob (coherent s.worstModel) true - t.prob (collapsed s.worstModel) true)
  (12/25 * s.overlapFloor)
  (by intro t _; convert every_test_bound s.worstModel t using 1
      simp [Study.worstModel, Leakage.ofOverlap]) test trivial

end
end OntologySeparation.PartialEnvironment
