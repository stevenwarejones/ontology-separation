import OntologySeparation.Experiments.ContinuumSeparation

/-! Scalar dispersion and finite-band vector estimates. Constants and band
hypotheses are explicit. This module proves the global 1/24 remainder;
ContinuumTruncation, ContinuumBorn and ContinuumLimit supply the normalized
tail, measurement and strong-convergence bridge. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section

/-- Conservative mathlib remainder, valid on |x| ≤ 1; not the sharp 1/24 bound. -/
theorem cosine_remainder_local (x : ℝ) (hx : |x| ≤ 1) :
    |x^2/2-(1-Real.cos x)| ≤ |x|^4*(5/96) := by
  convert Real.cos_bound hx using 1 <;> congr 1 <;> ring

/-- A global one-sided fourth-order remainder. The sharp Taylor coefficient
1/24 is established independently of the conservative local mathlib estimate. -/
theorem cosine_remainder_global (x : ℝ) :
    0 ≤ x^2/2-(1-Real.cos x) ∧ x^2/2-(1-Real.cos x) ≤ x^4/24 := by
  have hl : ∀ y : ℝ, 0 ≤ y^2/2-(1-Real.cos y) := by
    intro y
    linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  have hd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => Real.sin z-z+z^3/6)
      (Real.cos y-1+y^2/2) y := by
    intro y
    convert ((Real.hasDerivAt_sin y).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 3).div_const 6) using 1 <;> simp only [id_eq] <;> ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun y => by change 0 ≤ Real.cos y-1+y^2/2; linarith [hl y])
  have hs : ∀ y : ℝ, 0 ≤ y → 0 ≤ Real.sin y-y+y^3/6 := by
    intro y hy
    simpa using hm hy
  have hd' : ∀ y : ℝ, HasDerivAt (fun z : ℝ => 1-z^2/2+z^4/24-Real.cos z)
      (Real.sin y-y+y^3/6) y := by
    intro y
    convert (((hasDerivAt_const y (1 : ℝ)).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 4).div_const 24)).sub (Real.hasDerivAt_cos y) using 1 <;> simp only [id_eq] <;> ring
  have hm' : MonotoneOn (fun z : ℝ => 1-z^2/2+z^4/24-Real.cos z) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (by fun_prop)
      (fun y _ => (hd' y).hasDerivWithinAt)
    intro y hy
    exact hs y (le_of_lt (by simpa using hy))
  have hu := hm' (by simp : (0 : ℝ) ∈ Set.Ici 0) (abs_nonneg x) (abs_nonneg x)
  simp only [Real.cos_zero,zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 4 ≠ 0),
    zero_div,sub_zero,add_zero,sub_self,Real.cos_abs,pow_abs] at hu
  rw [abs_of_nonneg (sq_nonneg x),abs_of_nonneg (by positivity : 0 ≤ x^4)] at hu
  exact ⟨hl x,by linarith⟩

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

/-- Global nonnegative dispersion defect with the empirical 1/24 constant. -/
theorem frequency_error_global (hbar mass spacing k : ℝ)
    (hh : 0 ≤ hbar) (hm : 0 < mass) (ha : spacing ≠ 0) :
    0 ≤ continuumFrequency hbar mass k-latticeFrequency hbar mass spacing k ∧
    continuumFrequency hbar mass k-latticeFrequency hbar mass spacing k ≤
      hbar*spacing^2*k^4/(24*mass) := by
  have factor : continuumFrequency hbar mass k-latticeFrequency hbar mass spacing k =
      hbar/(mass*spacing^2)*((k*spacing)^2/2-(1-Real.cos (k*spacing))) := by
    unfold continuumFrequency latticeFrequency
    field_simp [ne_of_gt hm,ha] <;> ring
  have hc := cosine_remainder_global (k*spacing)
  have hf : 0 ≤ hbar/(mass*spacing^2) := by positivity
  rw [factor]
  refine ⟨mul_nonneg hf hc.1, ?_⟩
  calc
    _ ≤ hbar/(mass*spacing^2)*((k*spacing)^4/24) := mul_le_mul_of_nonneg_left hc.2 hf
    _ = _ := by field_simp [ne_of_gt hm,ha] <;> ring

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
