import OntologySeparation.Adapters.FiniteQuantum
import OntologySeparation.Core.FiniteModels
import Mathlib.Tactic

/-! Four controlled phase settings on a finite quantum system. The state, regional
projector and complete readout are fixed across settings. Born probabilities,
quadrature contrasts and dephased invariance follow from these physical objects;
no measured fringe or experimental calibration is a premise of the algebra. -/
namespace OntologySeparation.PhaseIntervention
noncomputable section
open scoped ComplexOrder MatrixOrder
open FiniteModels

inductive Phase | zero | quarter | half | threeQuarter
  deriving DecidableEq, Fintype

def factor : Phase → ℂ
  | .zero => 1
  | .quarter => Complex.I
  | .half => -1
  | .threeQuarter => -Complex.I

@[simp] theorem factor_unit (s : Phase) : star (factor s) * factor s = 1 := by
  cases s <;> simp [factor]

variable {H O : Type} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]

/-- A genuine orthogonal projection, in any finite dimension. -/
structure Region (H : Type) [Fintype H] [DecidableEq H] where
  projector : Matrix H H ℂ
  hermitian : projector.IsHermitian
  idempotent : projector * projector = projector

def Region.complement (R : Region H) : Matrix H H ℂ := 1 - R.projector

def Region.phaseMap (R : Region H) (s : Phase) : Matrix H H ℂ :=
  R.complement + factor s • R.projector

theorem Region.phaseMap_isometry (R : Region H) (s : Phase) :
    (R.phaseMap s).conjTranspose * R.phaseMap s = 1 := by
  simp only [Region.phaseMap, Region.complement, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    R.hermitian.eq, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, R.idempotent]
  match_scalars <;> cases s <;> norm_num [factor]

/-- Phase manipulation followed by the same complete detector POVM. Outcomes may
include no detection, other bins and any recorded failure categories. -/
def behavior (ρ : QIT.State H) (R : Region H) (M : QIT.POVM O H) :
    Behavior { Setting := Phase, Outcome := O } :=
  FiniteQuantum.behavior ρ (fun s =>
    FiniteQuantum.measureAfterIsometry M (R.phaseMap s) (R.phaseMap_isometry s))

def diagonalPart (ρ : Matrix H H ℂ) (R : Region H) : Matrix H H ℂ :=
  R.complement * ρ * R.complement + R.projector * ρ * R.projector

/-- Dephasing is a normalized positive quantum state, not just a fitted constant. -/
def dephase (ρ : QIT.State H) (R : Region H) : QIT.State H where
  matrix := diagonalPart ρ.matrix R
  pos := by
    have hQ : R.complement.IsHermitian := Matrix.isHermitian_one.sub R.hermitian
    simpa only [diagonalPart, hQ.eq, R.hermitian.eq] using
      (ρ.pos.mul_mul_conjTranspose_same R.complement).add
        (ρ.pos.mul_mul_conjTranspose_same R.projector)
  trace_eq_one := by
    have hid : R.complement * R.complement + R.projector * R.projector = 1 := by
      simp only [Region.complement, sub_mul, mul_sub, one_mul, mul_one, R.idempotent]
      abel
    simp only [diagonalPart, Matrix.trace_add]
    rw [Matrix.trace_mul_cycle R.complement ρ.matrix R.complement,
      Matrix.trace_mul_cycle R.projector ρ.matrix R.projector]
    rw [← Matrix.trace_add, ← add_mul, hid, one_mul, ρ.trace_eq_one]

def baseline (ρ : QIT.State H) (R : Region H) (E : Matrix H H ℂ) : ℝ :=
  ((diagonalPart ρ.matrix R * E).trace).re

def coherence (ρ : QIT.State H) (R : Region H) (E : Matrix H H ℂ) : ℂ :=
  (R.projector * ρ.matrix * R.complement * E).trace

private theorem conjugate_cross (ρ : QIT.State H) (R : Region H)
    (E : Matrix H H ℂ) (hE : E.IsHermitian) :
    (R.complement * ρ.matrix * R.projector * E).trace =
      star (coherence ρ R E) := by
  have hQ : R.complement.IsHermitian := Matrix.isHermitian_one.sub R.hermitian
  rw [coherence, ← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, hE.eq, hQ.eq, R.hermitian.eq,
    ρ.pos.isHermitian.eq]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- Expansion of the actual state transformation, before applying the Born rule. -/
theorem phase_expansion (ρ : QIT.State H) (R : Region H) (s : Phase) :
    R.phaseMap s * ρ.matrix * (R.phaseMap s).conjTranspose =
      diagonalPart ρ.matrix R +
        factor s • (R.projector * ρ.matrix * R.complement) +
        star (factor s) • (R.complement * ρ.matrix * R.projector) := by
  have hQ : R.complement.IsHermitian := Matrix.isHermitian_one.sub R.hermitian
  simp only [Region.phaseMap, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    hQ.eq, R.hermitian.eq, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, factor_unit, one_smul, diagonalPart]
  abel

/-- Born-rule derivation for arbitrary finite states, regions and complete readouts. -/
theorem probability_formula (ρ : QIT.State H) (R : Region H)
    (M : QIT.POVM O H) (s : Phase) (o : O) :
    (behavior ρ R M).prob s o = baseline ρ R (M.effects o) +
      2 * (factor s * coherence ρ R (M.effects o)).re := by
  change (FiniteQuantum.measureAfterIsometry M (R.phaseMap s)
    (R.phaseMap_isometry s)).prob ρ o = _
  rw [FiniteQuantum.measureAfterIsometry_prob_eq_lift, QIT.POVM.prob_eq_trace_re]
  change ((R.phaseMap s * ρ.matrix * (R.phaseMap s).conjTranspose * M.effects o).trace).re = _
  rw [phase_expansion]
  simp only [add_mul, smul_mul_assoc, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, Complex.add_re]
  rw [conjugate_cross ρ R _ (M.pos o).isHermitian]
  simp only [baseline, coherence, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Opposite phase settings isolate both real and imaginary parts with fixed signs. -/
theorem quadrature_contrasts (ρ : QIT.State H) (R : Region H)
    (M : QIT.POVM O H) (o : O) :
    (behavior ρ R M).prob .zero o - (behavior ρ R M).prob .half o =
      4 * (coherence ρ R (M.effects o)).re ∧
    (behavior ρ R M).prob .quarter o - (behavior ρ R M).prob .threeQuarter o =
      -4 * (coherence ρ R (M.effects o)).im := by
  simp only [probability_formula, factor, one_mul, neg_mul, Complex.neg_re,
    Complex.I_mul_re]
  constructor <;> ring

/-- The measured cross term vanishes exactly when both tested quadratures do.
This does not say that the whole state's off-diagonal block vanishes. -/
theorem zero_contrasts_iff (ρ : QIT.State H) (R : Region H)
    (M : QIT.POVM O H) (o : O) :
    ((behavior ρ R M).prob .zero o = (behavior ρ R M).prob .half o ∧
      (behavior ρ R M).prob .quarter o = (behavior ρ R M).prob .threeQuarter o) ↔
      coherence ρ R (M.effects o) = 0 := by
  obtain ⟨hr, hi⟩ := quadrature_contrasts ρ R M o
  constructor
  · rintro ⟨h₁, h₂⟩
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
  · intro h
    rw [h] at hr hi
    simp only [Complex.zero_re, Complex.zero_im, mul_zero] at hr hi
    constructor <;> linarith

/-- Equal randomization of opposite settings removes the cross block exactly. -/
theorem opposite_average (ρ : QIT.State H) (R : Region H)
    (M : QIT.POVM O H) (o : O) :
    ((behavior ρ R M).prob .zero o + (behavior ρ R M).prob .half o) / 2 =
      (M.prob (dephase ρ R) o : ℝ) := by
  rw [QIT.POVM.prob_eq_trace_re]
  change _ = baseline ρ R (M.effects o)
  simp only [probability_formula, factor, one_mul, neg_mul, Complex.neg_re]
  ring

/-- A state dephased between the selected region and its complement is invariant
under every declared phase intervention. -/
theorem dephased_invariant (ρ : QIT.State H) (R : Region H) (s : Phase) :
    QIT.POVM.isometryLiftState (dephase ρ R) (R.phaseMap s)
      (R.phaseMap_isometry s) = dephase ρ R := by
  apply QIT.State.ext
  change R.phaseMap s * (dephase ρ R).matrix * (R.phaseMap s).conjTranspose = _
  have hleft : R.projector * R.complement = 0 := by
    simp [Region.complement, mul_sub, R.idempotent]
  have hright : R.complement * R.projector = 0 := by
    simp [Region.complement, sub_mul, R.idempotent]
  have hc : R.projector * (dephase ρ R).matrix * R.complement = 0 := by
    change R.projector * (R.complement * ρ.matrix * R.complement +
      R.projector * ρ.matrix * R.projector) * R.complement = 0
    simp only [mul_add, ← Matrix.mul_assoc, hleft, zero_mul, zero_add]
    simp only [Matrix.mul_assoc, hleft, mul_zero]
  have hd : diagonalPart (dephase ρ R).matrix R = (dephase ρ R).matrix := by
    have hQ : R.complement * R.complement = R.complement := by
      simp only [Region.complement, sub_mul, mul_sub, one_mul, mul_one, R.idempotent]
      abel
    change R.complement * (R.complement * ρ.matrix * R.complement +
      R.projector * ρ.matrix * R.projector) * R.complement +
      R.projector * (R.complement * ρ.matrix * R.complement +
      R.projector * ρ.matrix * R.projector) * R.projector = _
    simp only [mul_add, ← Matrix.mul_assoc, hQ, R.idempotent,
      hleft, hright, zero_mul, zero_add, add_zero]
    simp only [Matrix.mul_assoc, hQ, R.idempotent]
    simp only [dephase, diagonalPart, Matrix.mul_assoc]
  have hc' : R.complement * (dephase ρ R).matrix * R.projector = 0 := by
    have hQ : R.complement.IsHermitian := Matrix.isHermitian_one.sub R.hermitian
    have h := congrArg Matrix.conjTranspose hc
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero,
      hQ.eq, R.hermitian.eq,
      (dephase ρ R).pos.isHermitian.eq, Matrix.mul_assoc] using h
  rw [phase_expansion (dephase ρ R) R s, hc, hc', smul_zero, add_zero, smul_zero,
    add_zero, hd]

theorem dephased_probability (ρ : QIT.State H) (R : Region H)
    (M : QIT.POVM O H) (s : Phase) (o : O) :
    (behavior (dephase ρ R) R M).prob s o = (M.prob (dephase ρ R) o : ℝ) := by
  change (FiniteQuantum.measureAfterIsometry M (R.phaseMap s)
    (R.phaseMap_isometry s)).prob (dephase ρ R) o = _
  rw [FiniteQuantum.measureAfterIsometry_prob_eq_lift, dephased_invariant]

end
end OntologySeparation.PhaseIntervention
