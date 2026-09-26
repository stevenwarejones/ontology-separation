import OntologySeparation.Experiments.PhaseInterventionModels
import QIT.Core.Pure

/-! Exact counterexamples and nonempty quantum models for phase-intervention
claims. All numbers are ideal model values, not experimental observations. -/
namespace OntologySeparation.PhaseIntervention
noncomputable section
open scoped ComplexOrder MatrixOrder

/-- Select the second of two orthogonal modes. -/
def secondMode : Region Bool where
  projector := Matrix.diagonal (fun b => if b then 1 else 0)
  hermitian := by
    change _ = _
    ext i j
    cases i <;> cases j <;> norm_num [Matrix.diagonal, Matrix.conjTranspose_apply]
  idempotent := by
    ext i j
    cases i <;> cases j <;> norm_num [Matrix.diagonal, Matrix.mul_apply, Fintype.sum_bool]

/-- A normalized pure state with nonzero imaginary regional coherence. -/
def imaginarySource : QIT.PureVector Bool where
  amp b := if b then (4 / 5 : ℂ) * Complex.I else 3 / 5
  trace_rankOne_eq_one := by
    norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace, Fintype.sum_bool,
      Complex.star_def, map_ofNat]
    ring_nf
    norm_num

/-- Plus/minus interference readout, retaining both outcomes. -/
def plusReadout : QIT.POVM Bool Bool where
  effects b := (1 / 2 : ℂ) • QIT.rankOneMatrix
    (fun i : Bool => if b && i then -1 else 1)
  pos b := by
    apply Matrix.PosSemidef.smul (QIT.rankOneMatrix_pos _)
    norm_num [Complex.nonneg_iff]
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;> norm_num [Fintype.sum_bool, QIT.rankOneMatrix,
      Matrix.vecMulVec, Matrix.one_apply, Complex.star_def, map_ofNat]

theorem imaginary_coherence :
    coherence imaginarySource.state secondMode (plusReadout.effects false) =
      (6 / 25 : ℂ) * Complex.I := by
  norm_num [coherence, imaginarySource, QIT.PureVector.state, QIT.rankOneMatrix,
    Matrix.vecMulVec, secondMode, Region.complement, plusReadout,
    Matrix.mul_apply, Matrix.trace, Matrix.diagonal, Fintype.sum_bool, Complex.star_def, map_ofNat]
  ring

theorem two_phases_can_miss_coherence :
    (behavior imaginarySource.state secondMode plusReadout).prob .zero false =
      (behavior imaginarySource.state secondMode plusReadout).prob .half false ∧
    (behavior imaginarySource.state secondMode plusReadout).prob .quarter false -
      (behavior imaginarySource.state secondMode plusReadout).prob .threeQuarter false =
        -24 / 25 := by
  obtain ⟨hr, hi⟩ := quadrature_contrasts imaginarySource.state secondMode plusReadout false
  rw [imaginary_coherence] at hr hi
  norm_num at hr hi
  exact ⟨by linarith, by linarith⟩

/-- Even a coherent source has no contrast under a coordinate readout. -/
theorem insensitive_readout :
    PhaseBlind (behavior imaginarySource.state secondMode (QIT.POVM.coordinate Bool)) := by
  have hc (o : Bool) : coherence imaginarySource.state secondMode
      ((QIT.POVM.coordinate Bool).effects o) = 0 := by
    cases o <;> norm_num [coherence, imaginarySource, QIT.PureVector.state,
      QIT.rankOneMatrix, Matrix.vecMulVec, secondMode, Region.complement,
      QIT.POVM.coordinate, Matrix.mul_apply, Matrix.trace, Matrix.diagonal,
      Fintype.sum_bool, Complex.star_def, Matrix.single]
  intro s t o
  simp only [probability_formula, hc, mul_zero, Complex.zero_re, add_zero]

/-- The zero-contrast source is nevertheless changed by dephasing. -/
theorem insensitive_source_not_dephased :
    imaginarySource.state ≠ dephase imaginarySource.state secondMode := by
  intro h
  have he := congrArg (fun ρ : QIT.State Bool => ρ.matrix false true) h
  norm_num [imaginarySource, QIT.PureVector.state, QIT.rankOneMatrix,
    Matrix.vecMulVec, dephase, diagonalPart, secondMode, Region.complement,
    Matrix.mul_apply, Matrix.diagonal, Fintype.sum_bool, Complex.star_def, map_ofNat, Complex.ext_iff] at he

/-- Positive efficiency and contrast leave the phase-blind convex null. -/
theorem lossy_excludes_blind {G : Type} [Fintype G]
    (g : G → Behavior (phaseInterface (Fin 3))) (hg : ∀ k, PhaseBlind (g k)) :
    ¬ FiniteModels.Compatible g
      (lossy (4/5) (3/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) := by
  apply excludes_blind_mixture g hg _ .zero .half 0
  norm_num [lossy, fringe]

/-- With no detections, even unit visibility cannot give this operational test a gap. -/
theorem zero_efficiency_blind (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    PhaseBlind (lossy 0 v le_rfl (by norm_num) hv₀ hv₁) := by
  intro s t o
  simp [lossy]

/-- A continuously tunable physical state: maximally mixed plus the plus state. -/
def visibilityState (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) : QIT.State Bool where
  matrix := ((1-v : ℝ) : ℂ) • ((1/2 : ℂ) • 1) + (v : ℂ) • plusReadout.effects false
  pos := by
    apply Matrix.PosSemidef.add
    · apply Matrix.PosSemidef.smul
      · apply Matrix.PosSemidef.smul Matrix.PosSemidef.one
        norm_num [Complex.nonneg_iff]
      · exact_mod_cast sub_nonneg.mpr hv₁
    · apply Matrix.PosSemidef.smul (plusReadout.pos false)
      exact_mod_cast hv₀
  trace_eq_one := by
    norm_num [plusReadout, Matrix.trace, Fintype.sum_bool, QIT.rankOneMatrix,
      Matrix.vecMulVec]
    ring

/-- A complete inefficient interference measurement: plus, minus, no detection. -/
def inefficientReadout (η : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) : QIT.POVM (Fin 3) Bool where
  effects o := if o.val = 0 then (η : ℂ) • plusReadout.effects false
    else if o.val = 1 then (η : ℂ) • plusReadout.effects true
    else ((1-η : ℝ) : ℂ) • 1
  pos o := by
    split_ifs
    · exact (plusReadout.pos false).smul (by exact_mod_cast hη₀)
    · exact (plusReadout.pos true).smul (by exact_mod_cast hη₀)
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr hη₁)
  sum_eq_one := by
    rw [Fin.sum_univ_three]
    change (η : ℂ) • plusReadout.effects false + (η : ℂ) • plusReadout.effects true +
      ((1-η : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) = 1
    have hs : plusReadout.effects false + plusReadout.effects true = 1 := by
      simpa only [Fintype.sum_bool, add_comm] using plusReadout.sum_eq_one
    rw [← smul_add, hs, ← add_smul]
    norm_num

/-- The sharp lossy probability family is realized by a fixed state, regional
phase unitary and complete POVM. It is not only a normalized phenomenological table. -/
theorem quantum_realizes_lossy (η v : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    ObservationallyEquivalent
      (behavior (visibilityState v hv₀ hv₁) secondMode (inefficientReadout η hη₀ hη₁))
      (lossy η v hη₀ hη₁ hv₀ hv₁) := by
  intro s o
  rw [probability_formula]
  fin_cases o <;> cases s <;>
    norm_num [baseline, coherence, diagonalPart, visibilityState, secondMode,
      Region.complement, inefficientReadout, plusReadout, QIT.rankOneMatrix,
      Matrix.vecMulVec, Matrix.mul_apply, Matrix.diagonal, Matrix.trace,
      Fintype.sum_bool, lossy, fringe, factor, Complex.mul_re, Complex.mul_im] <;> ring

/-- Selected-bin probability stays fixed; the other detected bin and failures
change with setting. Conditioning on detection alone invents a selected-bin fringe. -/
def selectionCounterexample : Behavior (phaseInterface (Fin 3)) where
  prob s o := if o.val = 0 then 1/4 else if o.val = 1 then
    (match s with | .zero => 1/4 | _ => 3/4) else (match s with | .zero => 1/2 | _ => 0)
  nonneg s o := by cases s <;> split_ifs <;> norm_num
  normalized s := by
    change (∑ o : Fin 3, _) = _
    rw [Fin.sum_univ_three]
    cases s <;> norm_num

theorem postselection_changes_contrast :
    (∀ s, selectionCounterexample.prob s 0 = 1/4) ∧
    selectionCounterexample.prob .zero 0 /
      (selectionCounterexample.prob .zero 0 + selectionCounterexample.prob .zero 1) -
    selectionCounterexample.prob .half 0 /
      (selectionCounterexample.prob .half 0 + selectionCounterexample.prob .half 1) = 1/4 := by
  norm_num [selectionCounterexample]

end
end OntologySeparation.PhaseIntervention
