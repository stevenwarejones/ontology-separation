import OntologySeparation.Experiments.ContinuumSeparation

/-! Scalar dispersion and finite-band vector estimates. Constants and band
hypotheses are explicit. The global 1/24 remainder and infinite tail-to-POVM
bridge in the mathematical guide remain separate obligations. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section

/-- Conservative mathlib remainder, valid on |x| ≤ 1; not the sharp 1/24 bound. -/
theorem cosine_remainder_local (x : ℝ) (hx : |x| ≤ 1) :
    |x^2/2-(1-Real.cos x)| ≤ |x|^4*(5/96) := by
  convert Real.cos_bound hx using 1 <;> congr 1 <;> ring

/-- Frequencies E/hbar for physical lattice spacing a. -/
def latticeFrequency (hbar mass spacing k : ℝ) : ℝ :=
  hbar / (mass * spacing^2) * (1-Real.cos (k*spacing))

def continuumFrequency (hbar mass k : ℝ) : ℝ := hbar*k^2/(2*mass)

theorem frequency_error_local (hbar mass spacing k : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 < mass) (ha : spacing ≠ 0) (hx : |k*spacing| ≤ 1) :
    |continuumFrequency hbar mass k - latticeFrequency hbar mass spacing k| ≤
      hbar/(mass*spacing^2) * (|k*spacing|^4*(5/96)) := by
  have factor : continuumFrequency hbar mass k - latticeFrequency hbar mass spacing k =
      hbar/(mass*spacing^2) * ((k*spacing)^2/2-(1-Real.cos (k*spacing))) := by
    unfold continuumFrequency latticeFrequency
    field_simp [ne_of_gt hm, ha]
    <;> ring
  rw [factor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ hbar/(mass*spacing^2))]
  exact mul_le_mul_of_nonneg_left (cosine_remainder_local _ hx) (by positivity)

theorem phase_difference (x y : ℝ) : ‖phase x-phase y‖ ≤ |x-y| := by
  have hp : phase y*phase (x-y) = phase x := by
    rw [← phase_add]
    congr 1
    ring
  have factor : phase x-phase y = phase y*(phase (x-y)-1) := by
    rw [mul_sub, hp, mul_one]
  rw [factor, norm_mul, phase_norm, one_mul]
  simpa only [phase, mul_comm Complex.I, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

/-- A finite-band state-norm estimate, with no dependence on dimension. -/
theorem finite_phase_error_sq {ι : Type} [Fintype ι] (c : ι → ℂ) (x y : ι → ℝ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hc : ∑ i, ‖c i‖^2 = 1)
    (hxy : ∀ i, |x i-y i| ≤ epsilon) :
    (∑ i, ‖phase (x i)*c i-phase (y i)*c i‖^2) ≤ epsilon^2 := by
  calc
    (∑ i, ‖phase (x i)*c i-phase (y i)*c i‖^2) ≤
        ∑ i, epsilon^2*‖c i‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_mul, norm_mul, mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) ((phase_difference _ _).trans (hxy i)) 2
    _ = epsilon^2 := by rw [← Finset.mul_sum, hc, mul_one]

end
end OntologySeparation.ContinuumFinite
