import OntologySeparation.Experiments.EnvironmentDiscrimination
import Mathlib.Tactic

/-! Partial environment access with a physical, continuously parameterized
source. `Accessible` is the laboratory logical record and one environment
fragment; the second fragment is always traced out. This benchmark is a
known two-branch quantum-erasure model, not a novelty claim. -/
namespace OntologySeparation.PartialEnvironment
noncomputable section
open scoped ComplexOrder MatrixOrder

abbrev Accessible := Bool × Bool
abbrev Total := Accessible × Bool

/-- Overlap and orthogonal component of the inaccessible branch record.
The normalization equation is a physical constraint, not a fitted score. -/
structure Leakage where
  overlap : ℝ
  orthogonal : ℝ
  nonneg : 0 ≤ overlap
  normalized : overlap ^ 2 + orthogonal ^ 2 = 1

/-- Every physical overlap has an explicit normalized hidden record. -/
def Leakage.ofOverlap (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : Leakage where
  overlap := r
  orthogonal := Real.sqrt (1 - r^2)
  nonneg := h0
  normalized := by rw [Real.sq_sqrt (by nlinarith)]; ring

def source (m : Leakage) : QIT.PureVector Total where
  amp i := if i.1.1 = i.1.2 then
    if i.1.1 then (4 / 5 : ℂ) * (if i.2 then m.orthogonal else m.overlap)
    else if i.2 then 0 else 3 / 5
    else 0
  trace_rankOne_eq_one := by
    have hn : (m.overlap : ℂ)^2 + (m.orthogonal : ℂ)^2 = 1 := by
      exact_mod_cast m.normalized
    norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
      Fintype.sum_prod_type, Fintype.sum_bool, Complex.star_def, map_ofNat]
    linear_combination (16 / 25 : ℂ) * hn

def coherent (m : Leakage) : QIT.State Accessible := (source m).state.marginalA

/-- A specified unread coordinate measurement on the accessible registers.
This leaves precisely the same populations and removes branch coherence. -/
def collapsed (m : Leakage) : QIT.State Accessible :=
  (QIT.Channel.measure (QIT.POVM.coordinate Accessible)).applyState (coherent m)

theorem coherent_entry (m : Leakage) (i j : Accessible) :
    (coherent m).matrix i j =
      if i.1 = i.2 ∧ j.1 = j.2 then
        if i.1 = j.1 then (if i.1 then 16/25 else 9/25)
        else (12/25 : ℂ) * m.overlap
      else 0 := by
  have hn : (m.overlap : ℂ)^2 + (m.orthogonal : ℂ)^2 = 1 := by
    exact_mod_cast m.normalized
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  change (∑ e : Bool, (source m).state.matrix ((a,b),e) ((c,d),e)) = _
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [source, QIT.PureVector.state, QIT.rankOneMatrix,
      Matrix.vecMulVec, Fintype.sum_bool, Complex.star_def, map_ofNat] <;>
    first | (solve | ring) | linear_combination (16 / 25 : ℂ) * hn

theorem collapsed_entry (m : Leakage) (i j : Accessible) :
    (collapsed m).matrix i j = if i = j then (coherent m).matrix i i else 0 := by
  change ((QIT.Channel.measure (QIT.POVM.coordinate Accessible)).map
    (coherent m).matrix) i j = _
  rw [QIT.Channel.measure_map_state_diagonal]
  simp [QIT.POVM.coordinate, Matrix.trace_mul_single, Matrix.diagonal]

/-- The normalized plus/minus projectors on the two populated branches. -/
def branchProjector (minus : Bool) : Matrix Accessible Accessible ℂ :=
  (1 / 2 : ℂ) • QIT.rankOneMatrix
    (fun i => if i.1 = i.2 then if minus && i.1 then -1 else 1 else 0)

theorem projector_pos (minus : Bool) : (branchProjector minus).PosSemidef := by
  apply Matrix.PosSemidef.smul (QIT.rankOneMatrix_pos _)
  norm_num [Complex.nonneg_iff]

theorem projector_trace (minus : Bool) : (branchProjector minus).trace = 1 := by
  cases minus <;> norm_num [branchProjector, QIT.rankOneMatrix,
    Matrix.vecMulVec, Matrix.trace, Fintype.sum_prod_type, Fintype.sum_bool]

theorem projector_idempotent : branchProjector false * branchProjector false =
    branchProjector false := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [branchProjector, QIT.rankOneMatrix, Matrix.vecMulVec,
      Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]

def readout : QIT.POVM Bool Accessible where
  effects b := if b then branchProjector false else 1 - branchProjector false
  pos b := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hh := (projector_pos false).isHermitian.eq
      have he : Matrix.conjTranspose (1 - branchProjector false) * (1 - branchProjector false) =
          1 - branchProjector false := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh,
          sub_mul, mul_sub, one_mul, mul_one, projector_idempotent]
        abel
      rw [← he]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    · simpa using projector_pos false
  sum_eq_one := by simp

def test := FiniteQuantum.measure readout

theorem coherent_probability (m : Leakage) :
    test.prob (coherent m) true = 1/2 + 12/25 * m.overlap := by
  rw [test, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  norm_num [readout, Matrix.trace, Matrix.mul_apply, coherent_entry,
    branchProjector, QIT.rankOneMatrix, Matrix.vecMulVec,
    Fintype.sum_prod_type, Fintype.sum_bool, Complex.mul_re]
  ring

theorem collapsed_probability (m : Leakage) : test.prob (collapsed m) true = 1/2 := by
  rw [test, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  norm_num [readout, Matrix.trace, Matrix.mul_apply, collapsed_entry, coherent_entry,
    branchProjector, QIT.rankOneMatrix, Matrix.vecMulVec,
    Fintype.sum_prod_type, Fintype.sum_bool]

theorem difference_matrix (m : Leakage) :
    (coherent m).matrix - (collapsed m).matrix =
      ((12/25 * m.overlap : ℝ) : ℂ) •
        (branchProjector false - branchProjector true) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [Matrix.sub_apply, collapsed_entry, coherent_entry,
      branchProjector, QIT.rankOneMatrix, Matrix.vecMulVec]

theorem distance_upper (m : Leakage) :
    (coherent m).normalizedTraceDistance (collapsed m) ≤ 12/25 * m.overlap := by
  have hp (b : Bool) : QIT.traceNorm (branchProjector b) = 1 := by
    rw [QIT.traceNorm_posSemidef_eq_trace_re _ (projector_pos b), projector_trace]
    rfl
  have ht := QIT.traceNorm_add_le (branchProjector false) (-branchProjector true)
  rw [QIT.traceNorm_neg, hp, hp] at ht
  change 1/2 * QIT.traceNorm ((coherent m).matrix - (collapsed m).matrix) ≤ _
  rw [difference_matrix, QIT.traceNorm_real_smul_eq (mul_nonneg (by norm_num) m.nonneg)]
  rw [← sub_eq_add_neg] at ht
  nlinarith [m.nonneg]

/-- Sharp accessible distinguishability: upper bound over all quantum tests,
attained by the explicit complete readout above. -/
theorem distance_exact (m : Leakage) :
    (coherent m).normalizedTraceDistance (collapsed m) = 12/25 * m.overlap := by
  apply le_antisymm (distance_upper m)
  have h := QuantumDiscrimination.probability_gap_le (coherent m) (collapsed m) test
  rw [coherent_probability, collapsed_probability] at h
  linarith

theorem every_test_bound (m : Leakage) {B : Type} [Fintype B] [DecidableEq B]
    (t : FiniteQuantum.Test Accessible B Bool) :
    t.prob (coherent m) true - t.prob (collapsed m) true ≤ 12/25 * m.overlap := by
  have h := QuantumDiscrimination.probability_gap_le (coherent m) (collapsed m) t
  rw [distance_exact] at h
  exact h

/-- Pointwise probability allowance criterion. `loss` lowers the coherent
prediction and `slack` raises the collapsed prediction for this binary event.
These are supplied physical bounds, not inferred calibration estimates. -/
def Resolves (m : Leakage) {B : Type} [Fintype B] [DecidableEq B]
    (t : FiniteQuantum.Test Accessible B Bool) (loss slack : ℝ) : Prop :=
  t.prob (collapsed m) true + slack < t.prob (coherent m) true - loss

/-- Exact threshold for the stated allowance criterion, including the boundary.
The converse covers any finite CPTP preprocessing and complete binary POVM
on the accessible fragment. The inaccessible fragment is absent from its type. -/
theorem resolves_iff (m : Leakage) (loss slack : ℝ) :
    (∃ t : FiniteQuantum.Test Accessible Accessible Bool, Resolves m t loss slack) ↔
      loss + slack < 12/25 * m.overlap := by
  constructor
  · rintro ⟨t, ht⟩
    have hb := every_test_bound m t
    unfold Resolves at ht
    linarith
  · intro h
    refine ⟨test, ?_⟩
    unfold Resolves
    rw [coherent_probability, collapsed_probability]
    linarith

theorem no_test_resolves (m : Leakage) (loss slack : ℝ)
    (h : 12/25 * m.overlap ≤ loss + slack)
    {B : Type} [Fintype B] [DecidableEq B]
    (t : FiniteQuantum.Test Accessible B Bool) : ¬ Resolves m t loss slack := by
  have hb := every_test_bound m t
  unfold Resolves
  linarith

theorem optimal_error (m : Leakage) :
    QuantumDiscrimination.minimumError (coherent m) (collapsed m) =
      1/2 - 6/25 * m.overlap := by
  rw [QuantumDiscrimination.minimumError, distance_exact]
  ring

/-- Losing the accessible fragment too hides all branch coherence. -/
theorem no_fragment_state (m : Leakage) :
    (coherent m).marginalA = (collapsed m).marginalA := by
  apply QIT.State.ext
  ext a b
  change (∑ e : Bool, (coherent m).matrix (a,e) (b,e)) =
    ∑ e : Bool, (collapsed m).matrix (a,e) (b,e)
  cases a <;> cases b <;>
    norm_num [collapsed_entry, coherent_entry, Fintype.sum_bool]

theorem no_fragment_test (m : Leakage) {B O : Type} [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O] (t : FiniteQuantum.Test Bool B O) (o : O) :
    t.prob (coherent m).marginalA o = t.prob (collapsed m).marginalA o := by
  rw [no_fragment_state]

/-- The same experiment must work for every hidden record in the class.
This quantifier order prevents choosing a different test after learning which
model generated the observation. -/
theorem uniform_threshold (r loss slack : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (∃ t : FiniteQuantum.Test Accessible Accessible Bool,
      ∀ m : Leakage, r ≤ m.overlap → Resolves m t loss slack) ↔
      loss + slack < 12/25 * r := by
  constructor
  · rintro ⟨t, ht⟩
    have hw := ht (Leakage.ofOverlap r h0 h1) le_rfl
    have hb := every_test_bound (Leakage.ofOverlap r h0 h1) t
    unfold Resolves at hw
    change _ ≤ 12/25 * r at hb
    linarith
  · intro h
    refine ⟨test, ?_⟩
    intro m hm
    unfold Resolves
    rw [coherent_probability, collapsed_probability]
    linarith

/-- A failed uniform guarantee has a physical worst-case record, not merely a
loose upper-bound proof. The failure is of the stated margin criterion. -/
theorem worst_case (r loss slack : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (h : 12/25 * r ≤ loss + slack)
    {B : Type} [Fintype B] [DecidableEq B]
    (t : FiniteQuantum.Test Accessible B Bool) :
    ∃ m : Leakage, r ≤ m.overlap ∧ ¬ Resolves m t loss slack :=
  ⟨Leakage.ofOverlap r h0 h1, le_rfl,
    no_test_resolves (Leakage.ofOverlap r h0 h1) loss slack h t⟩

end
end OntologySeparation.PartialEnvironment
