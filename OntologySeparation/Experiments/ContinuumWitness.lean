import OntologySeparation.Experiments.ContinuumLimit
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
  simp [interferometerMatrix,Matrix.vecHead,Matrix.vecTail]
  rw [show (Real.sqrt 2 : ℂ)⁻¹*u 0+(phase q/(Real.sqrt 2 : ℂ))*u 1 =
    (u 0+phase q*u 1)/(Real.sqrt 2 : ℂ) by ring]
  norm_num [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]

theorem interferometer_minus (q : ℝ) (u : TwoMode) :
    ‖interferometerOperator q 1 u‖^2 = ‖u 0-phase q*u 1‖^2/2 := by
  simp only [interferometerOperator,LinearMap.coe_toContinuousLinearMap',
    Matrix.toEuclideanLin_apply,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp [interferometerMatrix,Matrix.vecHead,Matrix.vecTail]
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
    norm_num [Fin.ext_iff]
    linear_combination eta * h

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
  have hm : ‖interferometerOperator q 1 (twoModeState theta)‖^2 = 1-plus 1 1 (q+theta) := by
    rw [hp] at ht
    linarith
  dsimp [noisyReadout]
  rw [hp,hm]
  norm_num [plus,minus,failure,Fin.ext_iff]
  constructor <;> ring

/-- The actual state produced by the two diagonal mode energies; the zero-mode
energy is zero. The reference q is shared between hypotheses. -/
def evolvedTwoMode (w t : ℝ) : TwoMode := twoModeState (-t*w)

/-- The actual diagonal propagator on the two selected mode coefficients. -/
def twoModeEvolve (w₀ w₁ t : ℝ) (u : TwoMode) : TwoMode :=
  WithLp.toLp 2 ![phase (-t*w₀)*u 0,phase (-t*w₁)*u 1]

def relativePhase (w : ℤ → ℝ) (j₀ j₁ : ℤ) (t : ℝ) : ℝ := -t*(w j₁-w j₀)

def relativePhaseDifference (w v : ℤ → ℝ) (j₀ j₁ : ℤ) (t : ℝ) : ℝ :=
  relativePhase w j₀ j₁ t-relativePhase v j₀ j₁ t

theorem twoModeEvolve_relative (w₀ w₁ t : ℝ) :
    twoModeEvolve w₀ w₁ t (twoModeState 0) =
      phase (-t*w₀) • twoModeState (-t*(w₁-w₀)) := by
  ext i
  fin_cases i
  · simp [twoModeEvolve,twoModeState]
  · change phase (-t*w₁)*(phase 0/(Real.sqrt 2 : ℂ)) =
      phase (-t*w₀)*(phase (-t*(w₁-w₀))/(Real.sqrt 2 : ℂ))
    simp only [phase_zero,mul_one,← mul_div_assoc]
    rw [← phase_add]
    congr 2
    ring

theorem evolved_readout_probability (q w₀ w₁ t : ℝ) :
    ‖interferometerOperator q 0 (twoModeEvolve w₀ w₁ t (twoModeState 0))‖^2 =
      plus 1 1 (q-t*(w₁-w₀)) := by
  rw [twoModeEvolve_relative,map_smul,norm_smul,phase_norm,one_mul]
  convert interferometer_probability q (-t*(w₁-w₀)) using 1 <;> congr 1 <;> ring

/-- Symmetric modes have equal energies and give no relative-dispersion signal. -/
theorem symmetric_mode_negative_control (r : Circle) (a t : ℝ) (j : ℤ) :
    relativePhase (frequency r) (-j) j t = 0 ∧
    relativePhase (fun k => latticeFrequency r.hbar r.mass a (waveNumber r k)) (-j) j t = 0 := by
  have hk : waveNumber r (-j) = -waveNumber r j := by simp [waveNumber]; ring
  simp [relativePhase,frequency,hk,latticeFrequency,neg_mul,Real.cos_neg]

/-- Without an externally fixed phase reference the *whole* noisy Born table can
be matched. This is an exact operational non-identifiability example. -/
theorem free_reference_born_equivalence (eta v q theta phi : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (o : Fin 3) :
    (noisyReadout eta v q he0 he1 hv0 hv1 (twoModeState theta) (twoModeState_normalized theta)).mass o =
    (noisyReadout eta v (q+theta-phi) he0 he1 hv0 hv1 (twoModeState phi) (twoModeState_normalized phi)).mass o := by
  have h₁ := noisyReadout_table eta v q theta he0 he1 hv0 hv1
  have h₂ := noisyReadout_table eta v (q+theta-phi) phi he0 he1 hv0 hv1
  have heq : q+theta-phi+phi = q+theta := by ring
  dsimp only at h₁ h₂
  rw [heq] at h₂
  fin_cases o
  · exact h₁.1.trans h₂.1.symm
  · exact h₁.2.1.trans h₂.2.1.symm
  · exact h₁.2.2.trans h₂.2.2.symm

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

def witnessCircle : Circle where
  length := 2*Real.pi
  mass := 1
  hbar := 1
  length_pos := by positivity
  mass_pos := by norm_num
  hbar_pos := by norm_num

theorem witness_frequencies :
    frequency witnessCircle 0 = 0 ∧ frequency witnessCircle 1 = 1/2 ∧
    ringLatticeFrequency witnessCircle (witnessCircle.length/4) 0 = 0 ∧
    ringLatticeFrequency witnessCircle (witnessCircle.length/4) 1 = 4/Real.pi^2 := by
  have hk : waveNumber witnessCircle 1 = 1 := by
    simp [waveNumber,witnessCircle,Real.pi_ne_zero]
  have hz : waveNumber witnessCircle 0 = 0 := by simp [waveNumber]
  have ha : witnessCircle.length/4 = Real.pi/2 := by dsimp [witnessCircle]; ring
  simp only [frequency,ringLatticeFrequency,latticeFrequency,hk,hz,ha]
  norm_num [witnessCircle,Real.cos_pi_div_two]
  <;> ring

/-- Explicit fixed lattice separation now stated directly with the circle and
lattice frequencies derived from the cyclic kinetic operator. -/
theorem lattice_born_witness :
    let t := Real.pi/witnessGap
    let q := t/2
    ‖interferometerOperator q 0 (twoModeEvolve (frequency witnessCircle 0)
      (frequency witnessCircle 1) t (twoModeState 0))‖^2 = 1 ∧
    ‖interferometerOperator q 0 (twoModeEvolve
      (ringLatticeFrequency witnessCircle (witnessCircle.length/4) 0)
      (ringLatticeFrequency witnessCircle (witnessCircle.length/4) 1) t (twoModeState 0))‖^2 = 0 := by
  dsimp only
  rw [witness_frequencies.1,witness_frequencies.2.1,witness_frequencies.2.2.1,
    witness_frequencies.2.2.2,evolved_readout_probability,evolved_readout_probability]
  have h := explicit_separating_born_experiment
  dsimp only [evolvedTwoMode] at h
  rw [interferometer_probability,interferometer_probability] at h
  change plus 1 1 (Real.pi/witnessGap/2 + -(Real.pi/witnessGap)*(1/2)) = 1 ∧
    plus 1 1 (Real.pi/witnessGap/2 + -(Real.pi/witnessGap)*(4/Real.pi^2)) = 0 at h
  convert h using 1 <;> congr 1 <;> ring

@[simp] theorem twoModeEvolve_norm (w₀ w₁ t : ℝ) (u : TwoMode) :
    ‖twoModeEvolve w₀ w₁ t u‖ = ‖u‖ := by
  have h : ‖twoModeEvolve w₀ w₁ t u‖^2 = ‖u‖^2 := by
    simp [twoModeEvolve, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
      norm_mul, phase_norm]
  nlinarith [norm_nonneg u, norm_nonneg (twoModeEvolve w₀ w₁ t u)]

/-- The full noisy law after diagonal evolution, including loss. -/
theorem evolved_noisyReadout_table (eta v q w₀ w₁ t : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let u := twoModeEvolve w₀ w₁ t (twoModeState 0)
    let p := noisyReadout eta v q he0 he1 hv0 hv1 u
      (by simp [u, twoModeState_normalized])
    p.mass 0 = plus eta v (q-t*(w₁-w₀)) ∧
    p.mass 1 = minus eta v (q-t*(w₁-w₀)) ∧ p.mass 2 = failure eta := by
  have hp := evolved_readout_probability q w₀ w₁ t
  have ht := (interferometer q).complete (twoModeEvolve w₀ w₁ t (twoModeState 0))
  change (∑ o, ‖interferometerOperator q o _‖^2) = _ at ht
  rw [Fin.sum_univ_three, interferometer_failure, twoModeEvolve_norm,
    twoModeState_normalized] at ht
  have hm : ‖interferometerOperator q 1 (twoModeEvolve w₀ w₁ t (twoModeState 0))‖^2 =
      1-plus 1 1 (q-t*(w₁-w₀)) := by rw [hp] at ht; linarith
  dsimp [noisyReadout]
  rw [hp, hm]
  norm_num [Fin.ext_iff, plus, minus, failure]
  constructor <;> ring

/-- Both noisy tables of the fixed N=4 experiment, from the actual two-mode
propagators with the derived physical frequencies. -/
theorem lattice_noisy_witness (eta v : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let t := Real.pi/witnessGap
    let q := t/2
    let u := twoModeEvolve (frequency witnessCircle 0) (frequency witnessCircle 1) t (twoModeState 0)
    let z := twoModeEvolve (ringLatticeFrequency witnessCircle (witnessCircle.length/4) 0)
      (ringLatticeFrequency witnessCircle (witnessCircle.length/4) 1) t (twoModeState 0)
    let p := noisyReadout eta v q he0 he1 hv0 hv1 u (by simp [u, twoModeState_normalized])
    let r := noisyReadout eta v q he0 he1 hv0 hv1 z (by simp [z, twoModeState_normalized])
    p.mass 0 = eta*(1+v)/2 ∧ p.mass 1 = eta*(1-v)/2 ∧ p.mass 2 = 1-eta ∧
    r.mass 0 = eta*(1-v)/2 ∧ r.mass 1 = eta*(1+v)/2 ∧ r.mass 2 = 1-eta := by
  dsimp only
  have hc := evolved_noisyReadout_table eta v (Real.pi/witnessGap/2)
    (frequency witnessCircle 0) (frequency witnessCircle 1) (Real.pi/witnessGap) he0 he1 hv0 hv1
  have hl := evolved_noisyReadout_table eta v (Real.pi/witnessGap/2)
    (ringLatticeFrequency witnessCircle (witnessCircle.length/4) 0)
    (ringLatticeFrequency witnessCircle (witnessCircle.length/4) 1)
    (Real.pi/witnessGap) he0 he1 hv0 hv1
  have hphase : Real.pi/witnessGap/2 - Real.pi/witnessGap*(4/Real.pi^2-0) = Real.pi := by
    calc
      _ = (Real.pi/witnessGap)*witnessGap := by unfold witnessGap; ring
      _ = Real.pi := div_mul_cancel₀ _ (ne_of_gt witnessGap_pos)
  rw [witness_frequencies.1, witness_frequencies.2.1] at hc
  rw [witness_frequencies.2.2.1, witness_frequencies.2.2.2, hphase] at hl
  have hzero : Real.pi/witnessGap/2 - Real.pi/witnessGap*(1/2-0) = 0 := by ring
  rw [hzero] at hc
  simpa [plus, minus, failure, witness_frequencies.1, witness_frequencies.2.1,
    witness_frequencies.2.2.1, witness_frequencies.2.2.2] using
    And.intro hc.1 (And.intro hc.2.1 (And.intro hc.2.2 hl))

/-- Complete-outcome contrast and TV, including the equal failure probabilities. -/
theorem noisy_witness_tv (p r : FiniteDistribution (Fin 3)) (eta v : ℝ)
    (he : 0 ≤ eta) (hv : 0 ≤ v)
    (hp : p.mass 0 = eta*(1+v)/2 ∧ p.mass 1 = eta*(1-v)/2 ∧ p.mass 2 = 1-eta)
    (hr : r.mass 0 = eta*(1-v)/2 ∧ r.mass 1 = eta*(1+v)/2 ∧ r.mass 2 = 1-eta) :
    p.mass 0-r.mass 0 = eta*v ∧ p.mass 1-r.mass 1 = -(eta*v) ∧
    p.mass 2=r.mass 2 ∧ tv p r = eta*v := by
  have h0 : p.mass 0-r.mass 0 = eta*v := by rw [hp.1, hr.1]; ring
  have h1 : p.mass 1-r.mass 1 = -(eta*v) := by rw [hp.2.1, hr.2.1]; ring
  refine ⟨h0, h1, hp.2.2.trans hr.2.2.symm, ?_⟩
  simp [tv, l1, Fin.sum_univ_three, h0, h1, hp.2.2, hr.2.2,
    abs_of_nonneg (mul_nonneg he hv)]

/-- Phase calibration contributes a derived eta*v*radius/2 error per model. -/
theorem plus_phase_radius (eta v q theta delta radius : ℝ)
    (he : 0 ≤ eta) (hv : 0 ≤ v) (hd : |delta| ≤ radius) :
    |plus eta v (q+theta+delta)-plus eta v (q+theta)| ≤ eta*v/2*radius := by
  have h := plus_phase_lipschitz eta v (q+theta+delta) (q+theta) he hv
  have hc : q+theta+delta-(q+theta) = delta := by ring
  rw [hc] at h
  exact h.trans (mul_le_mul_of_nonneg_left hd (by positivity))

/-- Strict disjointness of the two witness probability intervals. -/
theorem noisy_witness_robust (eta v p r rp rr : ℝ) (he : 0 ≤ eta) (hv : 0 ≤ v)
    (hp : |p-eta*(1+v)/2| ≤ rp) (hr : |r-eta*(1-v)/2| ≤ rr)
    (hgap : rp+rr < eta*v) : p ≠ r := by
  apply robust_coordinate_separation p r (eta*(1+v)/2) (eta*(1-v)/2) rp rr hp hr
  have h : eta*(1+v)/2-eta*(1-v)/2 = eta*v := by ring
  simpa [h, abs_of_nonneg (mul_nonneg he hv)] using hgap

/-- At exact touching, the shared boundary belongs to both closed intervals. -/
theorem noisy_witness_touching (a b rp rr : ℝ) (h : a-b = rp+rr)
    (hp : 0 ≤ rp) (hr : 0 ≤ rr) :
    |(a-rp)-a| ≤ rp ∧ |(a-rp)-b| ≤ rr := by
  have h1 : a-rp-a = -rp := by ring
  have h2 : a-rp-b = rr := by linarith
  simp [h1, h2, abs_of_nonneg hp, abs_of_nonneg hr]

/-- A full-turn phase difference is a sufficient blind control for all outcomes.
It is deliberately not an iff for a single cosine setting. -/
theorem phase_wrap_noisy_tables (eta v q theta phi : ℝ) (k : ℤ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hphase : theta-phi = k*(2*Real.pi)) (o : Fin 3) :
    (noisyReadout eta v q he0 he1 hv0 hv1 (twoModeState theta) (twoModeState_normalized theta)).mass o =
    (noisyReadout eta v q he0 he1 hv0 hv1 (twoModeState phi) (twoModeState_normalized phi)).mass o := by
  have ht := noisyReadout_table eta v q theta he0 he1 hv0 hv1
  have hp := noisyReadout_table eta v q phi he0 he1 hv0 hv1
  have harg : q+theta = (q+phi)+k*(2*Real.pi) := by linarith
  have hc : Real.cos (q+theta) = Real.cos (q+phi) := by
    rw [harg, Real.cos_add_int_mul_two_pi]
  dsimp only at ht hp
  fin_cases o
  · rw [ht.1, hp.1]; simp [plus, hc]
  · rw [ht.2.1, hp.2.1]; simp [minus, hc]
  · exact ht.2.2.trans hp.2.2.symm

/-- Explicit signed blind times for the witness gap; k=0 includes time zero. -/
theorem witness_blind_phase (k : ℤ) :
    let t := k*(2*Real.pi)/witnessGap
    (-t*(4/Real.pi^2))-(-t*(1/2)) = k*(2*Real.pi) := by
  dsimp only
  calc
    _ = (k*(2*Real.pi)/witnessGap)*witnessGap := by unfold witnessGap; ring
    _ = _ := div_mul_cancel₀ _ (ne_of_gt witnessGap_pos)

/-- One positive energy can be absorbed in a positive kinetic-scale change. -/
theorem one_momentum_scale_match (Ec Ea : ℝ) (hc : 0 < Ec) (ha : 0 < Ea) :
    0 < Ec/Ea ∧ (Ec/Ea)*Ea = Ec :=
  ⟨div_pos hc ha, div_mul_cancel₀ _ ha.ne'⟩

/-- Exact condition for that scale change to lie in the symmetric calibration interval. -/
theorem one_momentum_scale_interval (Ec Ea radius : ℝ) (ha : 0 < Ea) :
    (1-radius ≤ Ec/Ea ∧ Ec/Ea ≤ 1+radius) ↔
      |Ec-Ea| ≤ radius*Ea := by
  rw [abs_le, le_div_iff₀ ha, div_le_iff₀ ha]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith

/-- Matching the rescaled gap matches every time and every common noisy readout. -/
theorem one_momentum_all_times (Ec Ea scale eta v q t : ℝ)
    (h : scale*Ea = Ec) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (o : Fin 3) :
    (noisyReadout eta v q he0 he1 hv0 hv1 (evolvedTwoMode Ec t) (twoModeState_normalized _)).mass o =
    (noisyReadout eta v q he0 he1 hv0 hv1 (evolvedTwoMode (scale*Ea) t)
      (twoModeState_normalized _)).mass o := by rw [h]

end
end OntologySeparation.ContinuumFinite
