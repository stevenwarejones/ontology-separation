import OntologySeparation.Experiments.PathContextuality
import OntologySeparation.Adapters.FiniteQuantum
import QIT.Core.Pure

/-! Exact finite-strength two-path instrument. All outcomes are retained.
This is a rational instance of the established finite-pointer construction. -/
namespace OntologySeparation.PathContextuality
noncomputable section
open scoped ComplexOrder MatrixOrder

/-- Strength shared by the quantum effect identity and its ontic bridge. -/
def referencePm : ℝ := 7/25
/-- Identity-mixture weight shared by the channel identity and its ontic bridge. -/
def referenceD : ℝ := 1/50

/-- Path basis false=Q, true=P. Negative pointer is false. -/
def kraus (m : Bool) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun i => if m = i then 4/5 else 3/5)
def pathZ : Matrix Bool Bool ℂ := Matrix.diagonal (fun i => if i then -1 else 1)
def pathP : Matrix Bool Bool ℂ := Matrix.diagonal (fun i => if i then 1 else 0)

theorem kraus_complete : ∑ m, (kraus m).conjTranspose * kraus m = 1 := by
  ext i j
  cases i <;> cases j <;>
    norm_num [Complex.star_def, map_ofNat, kraus, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Matrix.one_apply]

/-- Measurement operational equivalence: noisy sharp path readout. -/
theorem effect_equivalence : (kraus false).conjTranspose * kraus false =
    (referencePm : ℂ) • (1-pathP) +
      (((1-referencePm)/2 : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  ext i j
  cases i <;> cases j <;>
    norm_num [Complex.star_def, map_ofNat, referencePm, kraus, pathP, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Matrix.one_apply]

/-- Full channel identity for every complex input matrix, not merely the
postselection marginal or four fitted probabilities. -/
theorem channel_equivalence (X : Matrix Bool Bool ℂ) :
    (∑ m, kraus m * X * (kraus m).conjTranspose) =
      ((1-referenceD : ℝ) : ℂ) • X +
      (referenceD : ℂ) • (pathZ * X * pathZ.conjTranspose) := by
  ext i j
  cases i <;> cases j <;>
    norm_num [Complex.star_def, map_ofNat, referenceD, kraus, pathZ, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool] <;> ring

/-- Ontic representation of `effect_equivalence`: measurement noncontextuality
and convex mixing supply `hM`; the operator equality alone does not supply it. -/
theorem reference_cap {Λ : Type} [Fintype Λ] (m : Model Λ)
    (e : Λ → ℝ) (he : ∀ l, e l ≤ 1)
    (hM : ∀ l, m.negative l = (1-referencePm)/2 + referencePm*e l) :
    m.ResponseCap (16/25) := by
  have h := m.cap_of_measurement_equivalence referencePm
    (by norm_num [referencePm]) e he hM
  norm_num [referencePm] at h
  exact h

def source : QIT.PureVector Bool where
  amp i := if i then 3/5 else 4/5
  trace_rankOne_eq_one := by
    norm_num [Complex.star_def, map_ofNat, QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace, Fintype.sum_bool]

def finalReadout : QIT.POVM Bool Bool where
  effects f := QIT.rankOneMatrix (fun i : Bool =>
    if f then (if i then -3/5 else 4/5) else (if i then 4/5 else 3/5))
  pos f := QIT.rankOneMatrix_pos _
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;>
      norm_num [Complex.star_def, map_ofNat, Fintype.sum_bool, QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.one_apply]

/-- Pull back the complete final measurement through each Kraus branch. -/
def jointReadout : QIT.POVM (Bool × Bool) Bool where
  effects o := (kraus o.1).conjTranspose * finalReadout.effects o.2 * kraus o.1
  pos o := by
    simpa using (finalReadout.pos o.2).conjTranspose_mul_mul_same (kraus o.1)
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;>
      norm_num [Complex.star_def, map_ofNat, Fintype.sum_prod_type, Fintype.sum_bool, kraus, finalReadout,
        QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.diagonal, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply]

def quantumJoint : Behavior jointInterface :=
  FiniteQuantum.behavior source.state (fun _ => FiniteQuantum.measure jointReadout)

def exactTable : Behavior jointInterface where
  prob _ o := if o.2 then (if o.1 then 144/15625 else 1369/15625) else 7056/15625
  nonneg _ o := by rcases o with ⟨m,f⟩; cases m <;> cases f <;> norm_num
  normalized _ := by
    change (∑ o : Bool × Bool, (if o.2 then
      (if o.1 then 144/15625 else 1369/15625) else 7056/15625 : ℝ)) = 1
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem quantum_realizes_table : ObservationallyEquivalent quantumJoint exactTable := by
  intro s o
  rcases o with ⟨m,f⟩
  change (FiniteQuantum.measure jointReadout).prob source.state (m,f) = _
  rw [FiniteQuantum.measure_prob]
  rw [QIT.POVM.prob_eq_trace_re]
  cases m <;> cases f <;>
    norm_num [Complex.star_def, map_ofNat, jointReadout, source, QIT.PureVector.state, finalReadout, kraus,
      QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.diagonal, Matrix.trace,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool, exactTable]

theorem bypass_probability : (finalReadout.prob source.state true : ℝ) = 49/625 := by
  rw [QIT.POVM.prob_eq_trace_re]
  norm_num [Complex.star_def, map_ofNat, source, QIT.PureVector.state, finalReadout, QIT.rankOneMatrix,
    Matrix.vecMulVec, Matrix.trace, Matrix.mul_apply, Fintype.sum_bool]

theorem exact_gap : exactTable.prob () (false,true) -
    ((16/25 : ℝ)*(49/625)+(1/50)*(1-49/625)) = 297/15625 := by
  norm_num [Complex.star_def, map_ofNat, exactTable]

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
/-- Explicit operational-to-ontic bridge for the reference instrument. `hM`
represents `effect_equivalence`; `hD` represents `channel_equivalence`, whose
identity-mixture coefficient is `referenceD`. These are additional ontological
premises, not consequences of matrix equalities. Shared preparation and final
response are built into `Model`. -/
theorem quantum_exclusion_of_representations {Λ : Type} [Fintype Λ] (m : Model Λ)
    (e : Λ → ℝ) (he : ∀ l, e l ≤ 1)
    (hM : ∀ l, m.negative l = (1-referencePm)/2 + referencePm*e l)
    (hD : m.Disturbance referenceD) (hf : m.pF = 49/625) :
    ¬ ObservationallyEquivalent m.observed quantumJoint :=
  quantum_exclusion m (reference_cap m e he hM) hD hf

end
end OntologySeparation.PathContextuality
