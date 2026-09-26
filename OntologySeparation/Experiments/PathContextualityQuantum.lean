import OntologySeparation.Experiments.PathContextuality
import OntologySeparation.Adapters.FiniteQuantum
import QIT.Core.Pure

/-! Exact finite-strength two-path instrument. All outcomes are retained.
This is a rational instance of the established finite-pointer construction. -/
namespace OntologySeparation.PathContextuality
noncomputable section
open scoped ComplexOrder MatrixOrder

/-- Path basis false=Q, true=P. Negative pointer is false. -/
def kraus (m : Bool) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun i => if m = i then 4/5 else 3/5)
def pathZ : Matrix Bool Bool ℂ := Matrix.diagonal (fun i => if i then -1 else 1)
def pathP : Matrix Bool Bool ℂ := Matrix.diagonal (fun i => if i then 1 else 0)

theorem kraus_complete : ∑ m, (kraus m).conjTranspose * kraus m = 1 := by
  ext i j
  cases i <;> cases j <;>
    norm_num [kraus, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Matrix.one_apply]

/-- Measurement operational equivalence: noisy sharp path readout. -/
theorem effect_equivalence : (kraus false).conjTranspose * kraus false =
    (7/25 : ℂ) • (1-pathP) + (9/25 : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  ext i j
  cases i <;> cases j <;>
    norm_num [kraus, pathP, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Matrix.one_apply]

/-- Full channel identity for every complex input matrix, not merely the
postselection marginal or four fitted probabilities. -/
theorem channel_equivalence (X : Matrix Bool Bool ℂ) :
    (∑ m, kraus m * X * (kraus m).conjTranspose) =
      (49/50 : ℂ) • X + (1/50 : ℂ) • (pathZ * X * pathZ.conjTranspose) := by
  ext i j
  cases i <;> cases j <;>
    norm_num [kraus, pathZ, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool] <;> ring

def source : QIT.PureVector Bool where
  amp i := if i then 3/5 else 4/5
  trace_rankOne_eq_one := by
    norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace, Fintype.sum_bool]

def finalReadout : QIT.POVM Bool Bool where
  effects f := QIT.rankOneMatrix (fun i : Bool =>
    if f then (if i then -3/5 else 4/5) else (if i then 4/5 else 3/5))
  pos f := QIT.rankOneMatrix_pos _
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;>
      norm_num [Fintype.sum_bool, QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.one_apply]

/-- Pull back the complete final measurement through each Kraus branch. -/
def jointReadout : QIT.POVM (Bool × Bool) Bool where
  effects o := (kraus o.1).conjTranspose * finalReadout.effects o.2 * kraus o.1
  pos o := by
    simpa using (finalReadout.pos o.2).conjTranspose_mul_mul_same (kraus o.1)
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;>
      norm_num [Fintype.sum_prod_type, Fintype.sum_bool, kraus, finalReadout,
        QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.diagonal, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply]

def quantumJoint : Behavior jointInterface :=
  FiniteQuantum.behavior source.state (fun _ => FiniteQuantum.measure jointReadout)

def exactTable : Behavior jointInterface where
  prob _ o := if o.2 then (if o.1 then 144/15625 else 1369/15625) else 7056/15625
  nonneg _ o := by rcases o with ⟨m,f⟩; cases m <;> cases f <;> norm_num
  normalized _ := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem quantum_realizes_table : ObservationallyEquivalent quantumJoint exactTable := by
  intro s o
  rcases o with ⟨m,f⟩
  change (FiniteQuantum.measure jointReadout).prob source.state (m,f) = _
  rw [FiniteQuantum.measure_prob]
  rw [QIT.POVM.prob_eq_trace_re]
  cases m <;> cases f <;>
    norm_num [jointReadout, source, QIT.PureVector.state, finalReadout, kraus,
      QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.diagonal, Matrix.trace,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool, exactTable]

theorem bypass_probability : (finalReadout.prob source.state true : ℝ) = 49/625 := by
  rw [QIT.POVM.prob_eq_trace_re]
  norm_num [source, QIT.PureVector.state, finalReadout, QIT.rankOneMatrix,
    Matrix.vecMulVec, Matrix.trace, Matrix.mul_apply, Fintype.sum_bool]

theorem exact_gap : exactTable.prob () (false,true) -
    ((16/25 : ℝ)*(49/625)+(1/50)*(1-49/625)) = 297/15625 := by
  norm_num [exactTable]

/-- No finite stochastic ontic model with these representations matches both
bypass and joint data. No definite-path premise is needed for this exclusion. -/
theorem quantum_exclusion {Λ : Type} [Fintype Λ] (m : Model Λ)
    (hq : m.ResponseCap (16/25)) (hd : m.Disturbance (1/50))
    (hf : m.pF = 49/625) : ¬ ObservationallyEquivalent m.observed quantumJoint := by
  intro h
  have hm : m.pMinus = 1369/15625 := by
    rw [Model.pMinus, h () (false,true), quantum_realizes_table () (false,true)]
    rfl
  have hb := m.bound (16/25) (1/50) (by norm_num) hq hd
  rw [hm, hf] at hb
  norm_num at hb
end
end OntologySeparation.PathContextuality
