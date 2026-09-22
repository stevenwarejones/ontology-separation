import OntologySeparation.Experiments.RecordEnvironment
import OntologySeparation.Adapters.QuantumDiscrimination

namespace OntologySeparation.RecordEnvironment
noncomputable section
open scoped ComplexOrder MatrixOrder
open QuantumDiscrimination

/-- The two accessible states coincide: every laboratory intervention has
exactly chance-level equal-prior decision error. -/
theorem laboratory_error {B : Type} [Fintype B] [DecidableEq B]
    (t : FiniteQuantum.Test Laboratory B Bool) :
    error coherent.marginalA collapsed.marginalA t = 1 / 2 := by
  rw [← same_laboratory_state]
  exact same_state_error _ t

/-- A lower bound for every finite full-register channel and binary measurement. -/
theorem full_error_bound {B : Type} [Fintype B] [DecidableEq B]
    (t : FiniteQuantum.Test Registers B Bool) :
    minimumError coherent collapsed ≤ error coherent collapsed t :=
  every_test coherent collapsed t

def fullOptimal := optimalTest coherent collapsed

theorem full_optimum_attained : error coherent collapsed fullOptimal =
    minimumError coherent collapsed := attained coherent collapsed

theorem full_beats_laboratory : error coherent collapsed fullOptimal < 1 / 2 := by
  rw [full_optimum_attained]
  exact strict_improvement coherent collapsed global_states_differ

/-- The return-to-source projector and its complement form a complete binary
measurement. The failure outcome is retained; no postselection is used. -/
def returnReadout : QIT.POVM Bool Registers where
  effects b := if b then coherent.matrix else 1 - coherent.matrix
  pos b := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hi : coherent.matrix * coherent.matrix = coherent.matrix :=
        source.state_matrix_mul_self
      have hh : Matrix.conjTranspose coherent.matrix = coherent.matrix :=
        coherent.pos.isHermitian
      have he : Matrix.conjTranspose (1 - coherent.matrix) *
          (1 - coherent.matrix) = 1 - coherent.matrix := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh,
          sub_mul, mul_sub, one_mul, mul_one, hi]
        abel
      rw [← he]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    · simpa using coherent.pos
  sum_eq_one := by simp [Fintype.sum_bool]

def returnTest := FiniteQuantum.measure returnReadout

theorem return_coherent : returnTest.prob coherent true = 1 := by
  rw [returnTest, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  change (coherent.matrix * coherent.matrix).trace.re = 1
  rw [show coherent.matrix * coherent.matrix = coherent.matrix from
    source.state_matrix_mul_self, coherent.trace_eq_one]
  rfl

theorem return_collapsed : returnTest.prob collapsed true = 337 / 625 := by
  rw [returnTest, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  change (collapsed.matrix * coherent.matrix).trace.re = _
  norm_num [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    collapsed_entry, coherent, source, QIT.PureVector.state,
    QIT.rankOneMatrix, Matrix.vecMulVec, Complex.div_re, Complex.div_im]

/-- A specified witness distinct from the abstract spectral optimum. -/
def returnSeparator : ExperimentAccess.Separator
    (FiniteQuantum.Named.predict (C := Registers) (O := Bool))
    (RegisterAccess.Allowed (FiniteQuantum.Named.footprint names)
      (FiniteQuantum.Named.bothPolicy names)) coherent collapsed where
  protocol := .jointTest returnTest
  accessible := FiniteQuantum.Named.both_allowed names _
  setting := ()
  outcome := true
  gap := 288 / 625
  positive := by norm_num
  difference := by
    change returnTest.prob coherent true - returnTest.prob collapsed true = _
    rw [return_coherent, return_collapsed]
    norm_num

def returnSeparationClaim : Claim := .separation _ _ _ _ returnSeparator

def returnCoherentClaim : Claim := .exact (returnTest.prob coherent true) 1 (by simpa using return_coherent)

def returnCollapsedClaim : Claim := .exact (returnTest.prob collapsed true) (337/625)
  (by convert return_collapsed using 1 <;> norm_num)
def returnGapClaim : Claim := .exact
  (returnTest.prob coherent true - returnTest.prob collapsed true) (288/625)
  (by rw [return_coherent, return_collapsed]; norm_num)
end
end OntologySeparation.RecordEnvironment
