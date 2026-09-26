import OntologySeparation.Experiments.ContinuumWitness

/-! One common kinetic multiplier cannot absorb distinct energy ratios.
This is an exact dynamical statement, not a statistical finite-menu certificate. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section

/-- Continuum modes one and two have a quadratic energy ratio. -/
theorem continuum_mode_ratio (r : Circle) :
    frequency r 1 > 0 ∧ frequency r 2 = 4*frequency r 1 ∧
    frequency r 2/frequency r 1 = 4 := by
  have hk : 0 < waveNumber r 1 := by
    simpa [waveNumber] using div_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos) r.length_pos
  have hf : 0 < frequency r 1 := by
    unfold frequency
    exact div_pos (mul_pos r.hbar_pos (sq_pos_of_pos hk)) (mul_pos (by norm_num) r.mass_pos)
  have h2 : waveNumber r 2 = 2*waveNumber r 1 := by norm_num [waveNumber]; ring
  have he : frequency r 2 = 4*frequency r 1 := by unfold frequency; rw [h2]; ring
  refine ⟨hf, he, ?_⟩
  rw [he]
  field_simp

/-- For N>4 the half-step angle is strictly between zero and pi/2. -/
theorem lattice_half_angle (N : ℕ) (hN : 4 < N) :
    0 < Real.pi/(N : ℝ) ∧ Real.pi/(N : ℝ) < Real.pi/2 ∧
    0 < Real.sin (Real.pi/(N : ℝ)) ∧ 0 < Real.cos (Real.pi/(N : ℝ)) ∧
    Real.cos (Real.pi/(N : ℝ))^2 < 1 := by
  have hn : (4 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < Real.pi/(N : ℝ) := div_pos Real.pi_pos (by linarith)
  have hhalf : Real.pi/(N : ℝ) < Real.pi/2 := by
    apply div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hp (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩
  refine ⟨hp,hhalf,hs,hc,?_⟩
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi/(N : ℝ))]

/-- The nearest-neighbor dispersion gives a different, derived ratio. -/
theorem lattice_mode_ratio (r : Circle) (N : ℕ) (hN : 4 < N) :
    let w := ringLatticeFrequency r (r.length/N)
    0 < w 1 ∧ w 2 = 4*Real.cos (Real.pi/(N : ℝ))^2*w 1 ∧
    w 2/w 1 = 4*Real.cos (Real.pi/(N : ℝ))^2 := by
  dsimp only
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL := r.length_pos.ne'
  have h1 : waveNumber r 1*(r.length/N) = 2*(Real.pi/(N : ℝ)) := by
    norm_num [waveNumber]
    field_simp
    <;> ring
  have h2 : waveNumber r 2*(r.length/N) = 2*(2*(Real.pi/(N : ℝ))) := by
    norm_num [waveNumber]
    field_simp
    <;> ring
  have hang := lattice_half_angle N hN
  have hcos : 0 < 1-Real.cos (2*(Real.pi/(N : ℝ))) := by
    rw [Real.cos_two_mul]
    nlinarith
  have hw : 0 < ringLatticeFrequency r (r.length/N) 1 := by
    unfold ringLatticeFrequency latticeFrequency
    rw [h1]
    exact div_pos (mul_pos r.hbar_pos hcos)
      (mul_pos r.mass_pos (sq_pos_of_pos (div_pos r.length_pos hn)))
  have he : ringLatticeFrequency r (r.length/N) 2 =
      4*Real.cos (Real.pi/(N : ℝ))^2*ringLatticeFrequency r (r.length/N) 1 := by
    unfold ringLatticeFrequency latticeFrequency
    rw [h1,h2,Real.cos_two_mul,Real.cos_two_mul]
    ring
  refine ⟨hw,he,?_⟩
  rw [he]
  exact mul_div_cancel_right₀ _ hw.ne'

/-- Positive shared multipliers cannot match both modes when N>4. Zero
multipliers are excluded because they erase all dynamical information. -/
theorem shared_scale_two_modes_impossible (r : Circle) (N : ℕ) (hN : 4 < N)
    (sc sa : ℝ) (hc : 0 < sc) (ha : 0 < sa) :
    ¬(sc*frequency r 1 = sa*ringLatticeFrequency r (r.length/N) 1 ∧
      sc*frequency r 2 = sa*ringLatticeFrequency r (r.length/N) 2) := by
  obtain ⟨hc1,hc2,_⟩ := continuum_mode_ratio r
  obtain ⟨ha1,ha2,_⟩ := lattice_mode_ratio r N hN
  have hangle := (lattice_half_angle N hN).2.2.2.2
  rintro ⟨h1,h2⟩
  rw [hc2,ha2] at h2
  have hp : 0 < sa*ringLatticeFrequency r (r.length/N) 1 := mul_pos ha ha1
  have hgap := mul_pos (sub_pos.mpr hangle) hp
  nlinarith

end
end OntologySeparation.ContinuumFinite
