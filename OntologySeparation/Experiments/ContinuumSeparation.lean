import OntologySeparation.Experiments.ContinuumSpectral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A complete lossy readout and calibration separation at the probability level.
The dynamics-to-readout and quantitative approximation bridges are not asserted
by these elementary lemmas. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section

def plus (eta visibility theta : ℝ) : ℝ := eta*(1+visibility*Real.cos theta)/2

def minus (eta visibility theta : ℝ) : ℝ := eta*(1-visibility*Real.cos theta)/2

def failure (eta : ℝ) : ℝ := 1-eta

theorem readout_normalized (eta visibility theta : ℝ) :
    plus eta visibility theta + minus eta visibility theta + failure eta = 1 := by
  unfold plus minus failure
  ring

theorem readout_nonneg (eta visibility theta : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hv : 0 ≤ visibility) (hv1 : visibility ≤ 1) :
    0 ≤ plus eta visibility theta ∧ 0 ≤ minus eta visibility theta ∧ 0 ≤ failure eta := by
  have hc := Real.neg_one_le_cos theta
  have hc1 := Real.cos_le_one theta
  have hlo := mul_le_mul_of_nonneg_left hc hv
  have lo : -1 ≤ visibility*Real.cos theta := by nlinarith
  have hhi := mul_le_mul_of_nonneg_left hc1 hv
  have hi : visibility*Real.cos theta ≤ 1 := by nlinarith
  exact ⟨div_nonneg (mul_nonneg he (by linarith)) (by norm_num),
    div_nonneg (mul_nonneg he (by linarith)) (by norm_num), by dsimp [failure]; linarith⟩

theorem zero_visibility (eta theta : ℝ) : plus eta 0 theta = eta/2 := by
  simp [plus]

theorem full_loss (visibility theta : ℝ) :
    plus 0 visibility theta = 0 ∧ minus 0 visibility theta = 0 ∧ failure 0 = 1 := by
  simp [plus, minus, failure]

theorem reference_absorbs (eta visibility theta delta : ℝ) :
    plus eta visibility ((theta+delta)-delta) = plus eta visibility theta := by
  rw [add_sub_cancel_right]

theorem cosine_gap (eta visibility delta : ℝ) :
    plus eta visibility 0 - plus eta visibility delta =
      eta*visibility*(1-Real.cos delta)/2 := by
  simp only [plus, Real.cos_zero]
  ring

theorem strict_cosine_separation (eta visibility delta : ℝ)
    (he : 0 < eta) (hv : 0 < visibility) (hd : Real.cos delta < 1) :
    plus eta visibility delta < plus eta visibility 0 := by
  have hp : 0 < eta*visibility*(1-Real.cos delta)/2 :=
    div_pos (mul_pos (mul_pos he hv) (sub_pos.mpr hd)) (by norm_num)
  rw [← cosine_gap] at hp
  linarith

/-- An actual readout Lipschitz bound, not an assumed measurement premise. -/
theorem plus_phase_lipschitz (eta visibility x y : ℝ) (he : 0 ≤ eta) (hv : 0 ≤ visibility) :
    |plus eta visibility x - plus eta visibility y| ≤ eta*visibility/2*|x-y| := by
  have eq : plus eta visibility x - plus eta visibility y =
      eta*visibility/2*(Real.cos x-Real.cos y) := by unfold plus; ring
  rw [eq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ eta*visibility/2)]
  exact mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le x y) (by positivity)

/-- Robust disjointness of calibrated probability intervals. -/
theorem robust_coordinate_separation (p q p0 q0 rp rq : ℝ)
    (hp : |p-p0| ≤ rp) (hq : |q-q0| ≤ rq) (hgap : rp+rq < |p0-q0|) : p ≠ q := by
  intro h
  subst q
  have htri : |p0-q0| ≤ |p0-p|+|p-q0| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (p0-p) (p-q0)
  have hp' : |p0-p| ≤ rp := by simpa only [abs_sub_comm] using hp
  linarith

/-- Conditional test-error algebra. A TV/product theorem is a separate obligation. -/
theorem test_error_of_event_bound (rejectP rejectQ epsilon : ℝ)
    (h : |rejectQ-rejectP| ≤ epsilon) :
    1-epsilon ≤ rejectP+(1-rejectQ) := by
  have := (abs_le.mp h).2
  linarith

end
end OntologySeparation.ContinuumFinite
