import OntologySeparation.Experiments.ContinuumBorn
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! A concrete two-mode interferometric Born readout. The third outcome is
failure. Visibility and efficiency are classical randomization/loss of this
fixed interferometer, with the same calibration under both dynamics. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open scoped Matrix

abbrev TwoMode := EuclideanSpace ℂ (Fin 2)

def interferometerMatrix (q : ℝ) (o : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  if o = 0 then !![1/(Real.sqrt 2 : ℂ), phase q/(Real.sqrt 2 : ℂ); 0,0]
  else if o = 1 then !![1/(Real.sqrt 2 : ℂ), -phase q/(Real.sqrt 2 : ℂ); 0,0]
  else 0

def interferometerOperator (q : ℝ) (o : Fin 3) : TwoMode →L[ℂ] TwoMode :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (interferometerMatrix q o))

theorem interferometer_plus (q : ℝ) (u : TwoMode) :
    ‖interferometerOperator q 0 u‖^2 = ‖u 0+phase q*u 1‖^2/2 := by
  simp only [interferometerOperator,LinearMap.coe_toContinuousLinearMap',
    Matrix.toEuclideanLin_apply,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  change ‖(Real.sqrt 2 : ℂ)⁻¹*u 0+(phase q/(Real.sqrt 2 : ℂ))*u 1‖^2+‖(0 : ℂ)‖^2 = _
  rw [show (Real.sqrt 2 : ℂ)⁻¹*u 0+(phase q/(Real.sqrt 2 : ℂ))*u 1 =
    (u 0+phase q*u 1)/(Real.sqrt 2 : ℂ) by ring]
  norm_num [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]

theorem interferometer_minus (q : ℝ) (u : TwoMode) :
    ‖interferometerOperator q 1 u‖^2 = ‖u 0-phase q*u 1‖^2/2 := by
  simp only [interferometerOperator,LinearMap.coe_toContinuousLinearMap',
    Matrix.toEuclideanLin_apply,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  change ‖(Real.sqrt 2 : ℂ)⁻¹*u 0+(-phase q/(Real.sqrt 2 : ℂ))*u 1‖^2+‖(0 : ℂ)‖^2 = _
  rw [show (Real.sqrt 2 : ℂ)⁻¹*u 0+(-phase q/(Real.sqrt 2 : ℂ))*u 1 =
    (u 0-phase q*u 1)/(Real.sqrt 2 : ℂ) by ring]
  norm_num [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]

@[simp] theorem interferometer_failure (q : ℝ) (u : TwoMode) :
    ‖interferometerOperator q 2 u‖^2 = 0 := by
  simp [interferometerOperator,interferometerMatrix,Matrix.toEuclideanLin_apply]

/-- Completeness is proved from the actual beam-splitter matrix. -/
def interferometer (q : ℝ) : BornInstrument TwoMode (Fin 3) where
  operator := interferometerOperator q
  complete u := by
    rw [Fin.sum_univ_three,interferometer_plus,interferometer_minus,interferometer_failure,
      EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    have h := Complex.normSq_add (u 0) (phase q*u 1)
    have h' := Complex.normSq_sub (u 0) (phase q*u 1)
    simp only [Complex.normSq_eq_norm_sq,norm_mul,phase_norm,one_mul] at h h'
    linarith

def twoModeState (theta : ℝ) : TwoMode :=
  WithLp.toLp 2 ![1/(Real.sqrt 2 : ℂ),phase theta/(Real.sqrt 2 : ℂ)]

theorem twoModeState_normalized (theta : ℝ) : ‖twoModeState theta‖ = 1 := by
  have h : ‖twoModeState theta‖^2 = 1 := by
    norm_num [twoModeState,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,norm_div,div_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]
  nlinarith [norm_nonneg (twoModeState theta)]

theorem phase_re (theta : ℝ) : (phase theta).re = Real.cos theta := by
  simp [phase,Complex.exp_mul_I,← Complex.ofReal_cos]

theorem interferometer_probability (q theta : ℝ) :
    ((interferometer q).distribution (twoModeState theta) (twoModeState_normalized theta)).mass 0 =
      plus 1 1 (q+theta) := by
  change ‖interferometerOperator q 0 (twoModeState theta)‖^2 = _
  rw [interferometer_plus]
  have hsum : twoModeState theta 0+phase q*twoModeState theta 1 =
      (1+phase (q+theta))/(Real.sqrt 2 : ℂ) := by
    change 1/(Real.sqrt 2 : ℂ)+phase q*(phase theta/(Real.sqrt 2 : ℂ)) = _
    rw [phase_add]
    ring

  rw [hsum,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num)]
  have h := Complex.normSq_add (1 : ℂ) (phase (q+theta))
  simp only [Complex.normSq_eq_norm_sq,norm_one,phase_norm,one_pow,one_mul,
    Complex.conj_re,phase_re] at h
  unfold plus
  nlinarith

/-- Loss and symmetric visibility randomization of the Born readout. This is a
positive classical processing of the complete measurement, hence a POVM. -/
def noisyReadout (eta v q : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (u : TwoMode) (hu : ‖u‖ = 1) :
    FiniteDistribution (Fin 3) where
  mass o := if o = 0 then eta*((1+v)/2*‖interferometerOperator q 0 u‖^2+
      (1-v)/2*‖interferometerOperator q 1 u‖^2)
    else if o = 1 then eta*((1-v)/2*‖interferometerOperator q 0 u‖^2+
      (1+v)/2*‖interferometerOperator q 1 u‖^2) else 1-eta
  nonneg o := by
    fin_cases o <;> norm_num <;> first | positivity | linarith
  total := by
    have h := (interferometer q).complete u
    change (∑ o, ‖interferometerOperator q o u‖^2) = ‖u‖^2 at h
    rw [Fin.sum_univ_three,interferometer_failure,hu] at h
    simp only [Fin.sum_univ_three]
    norm_num
    nlinarith

/-- Both visible bins, and failure, are included in the calibrated formula. -/
theorem noisyReadout_table (eta v q theta : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let p := noisyReadout eta v q he0 he1 hv0 hv1 (twoModeState theta) (twoModeState_normalized theta)
    p.mass 0 = plus eta v (q+theta) ∧ p.mass 1 = minus eta v (q+theta) ∧ p.mass 2 = failure eta := by
  have hp := interferometer_probability q theta
  change ‖interferometerOperator q 0 (twoModeState theta)‖^2 = plus 1 1 (q+theta) at hp
  have ht := (interferometer q).complete (twoModeState theta)
  change (∑ o, ‖interferometerOperator q o (twoModeState theta)‖^2) = ‖twoModeState theta‖^2 at ht
  rw [Fin.sum_univ_three,interferometer_failure,twoModeState_normalized] at ht
  dsimp [noisyReadout,plus,minus,failure] at *
  norm_num at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · rfl

/-- The actual state produced by the two diagonal mode energies; the zero-mode
energy is zero. The reference q is shared between hypotheses. -/
def evolvedTwoMode (w t : ℝ) : TwoMode := twoModeState (-t*w)

/-- N=4, L=2π, m=hbar=1 gives a concrete nonzero dispersion gap. -/
def witnessGap : ℝ := (1/2)-4/Real.pi^2

theorem witnessGap_pos : 0 < witnessGap := by
  have hp : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hb : 8 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  unfold witnessGap
  apply sub_pos.mpr
  apply (div_lt_iff₀ hp).mpr
  nlinarith

/-- An explicit shared time/reference aligns the continuum and gives the N=4
lattice a π fringe shift. It is a fixed alternative, not a uniform fine-grid test. -/
theorem explicit_separating_born_experiment :
    let t := Real.pi/witnessGap
    let q := t/2
    ((interferometer q).distribution (evolvedTwoMode (1/2) t) (twoModeState_normalized _)).mass 0 = 1 ∧
    ((interferometer q).distribution (evolvedTwoMode (4/Real.pi^2) t) (twoModeState_normalized _)).mass 0 = 0 := by
  dsimp [evolvedTwoMode]
  rw [interferometer_probability,interferometer_probability]
  have hc : Real.pi/witnessGap/2 + -(Real.pi/witnessGap)*(1/2) = 0 := by ring
  have hl : Real.pi/witnessGap/2 + -(Real.pi/witnessGap)*(4/Real.pi^2) = Real.pi := by
    calc
      _ = (Real.pi/witnessGap)*witnessGap := by unfold witnessGap; ring
      _ = Real.pi := div_mul_cancel₀ _ (ne_of_gt witnessGap_pos)

  rw [hc,hl]
  simp [plus]

end
end OntologySeparation.ContinuumFinite
