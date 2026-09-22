import OntologySeparation.Adapters.FiniteQuantum
import OntologySeparation.Core.Claim
import OntologySeparation.Core.Comparison
import QIT.Core.Pure
import Mathlib.Tactic.NormNum

/-! An explicit operational separation: a coherent copied record and its
unread-measurement dephasing agree on all local tests, but a joint reversal
measurement separates them. This is not a universal collapse/decoherence test. -/
namespace OntologySeparation.RecordAccess
noncomputable section
open scoped ComplexOrder MatrixOrder
abbrev Registers := Bool × Bool

/-- System first, inaccessible record/environment second. -/
def source : QIT.PureVector Registers where
  amp i := if i.1 = i.2 then (if i.1 then 4 / 5 else 3 / 5) else 0
  trace_rankOne_eq_one := by
    apply Complex.ext <;> norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
      Fintype.sum_prod_type, Fintype.sum_bool, Complex.div_re, Complex.div_im]

def coherent : QIT.State Registers := source.state

/-- A specified irreversible dephasing channel, not an interpretation label. -/
def dephased : QIT.State Registers :=
  (QIT.Channel.measure (QIT.POVM.coordinate Registers)).applyState coherent

/-- Closed matrix expression derived from the channel, for transparent calculation. -/
theorem dephased_entry (i j : Registers) :
    dephased.matrix i j = if i = j then coherent.matrix i i else 0 := by
  change ((QIT.Channel.measure (QIT.POVM.coordinate Registers)).map coherent.matrix) i j = _
  rw [QIT.Channel.measure_map_state_diagonal]
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [QIT.POVM.coordinate, Matrix.diagonal, Matrix.trace, Matrix.mul_apply,
      Matrix.single, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Discarding the record removes exactly the off-diagonal coherence of this source. -/
theorem same_local_state : coherent.marginalA = dephased.marginalA := by
  apply QIT.State.ext
  ext a b
  change (∑ e : Bool, coherent.matrix (a,e) (b,e)) =
    ∑ e : Bool, dephased.matrix (a,e) (b,e)
  simp_rw [dephased_entry]
  cases a <;> cases b <;> norm_num [coherent, source, QIT.PureVector.state,
    QIT.rankOneMatrix, Matrix.vecMulVec, Fintype.sum_bool]

/-- All local experiments, not only the computational-basis example. -/
theorem all_local_tests {B O : Type} [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O] (t : FiniteQuantum.Test Bool B O) (o : O) :
    t.prob coherent.marginalA o = t.prob dephased.marginalA o :=
  FiniteQuantum.local_test_eq coherent dephased same_local_state t o

/-- Undo the record-copy CNOT, then rotate the original source to |0>.
The rational source avoids a hidden floating-point or square-root approximation. -/
def recovery : Matrix Registers Registers ℂ := fun o i =>
  if o.2 = xor i.1 i.2 then
    (if o.1 = i.1 then 3 / 5 else if o.1 then -(4 / 5) else 4 / 5)
  else 0

theorem recovery_isometry : Matrix.conjTranspose recovery * recovery = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    apply Complex.ext <;>
    norm_num [recovery, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply, Complex.div_re, Complex.div_im]

/-- A complete four-outcome measurement, including all failure outcomes. -/
def recoveryReadout : QIT.POVM Registers Registers :=
  (QIT.POVM.coordinate Registers).compressByIsometry recovery recovery_isometry

def recoveryTest : FiniteQuantum.Test Registers Registers Registers :=
  FiniteQuantum.measure recoveryReadout

theorem coherent_recovery : recoveryTest.prob coherent (false,false) = 1 := by
  rw [recoveryTest, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  norm_num [recoveryReadout, QIT.POVM.compressByIsometry, QIT.POVM.coordinate,
    coherent, source, QIT.PureVector.state, QIT.rankOneMatrix, Matrix.vecMulVec,
    recovery, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
    Fintype.sum_prod_type, Fintype.sum_bool, Complex.div_re, Complex.div_im]

theorem dephased_recovery : recoveryTest.prob dephased (false,false) = 337 / 625 := by
  rw [recoveryTest, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  norm_num [dephased_entry, Matrix.trace, Matrix.diag, recoveryReadout, QIT.POVM.compressByIsometry, QIT.POVM.coordinate,
    coherent, source, QIT.PureVector.state, QIT.rankOneMatrix, Matrix.vecMulVec,
    recovery, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
    Fintype.sum_prod_type, Fintype.sum_bool, Complex.div_re, Complex.div_im]

inductive Law where | coherent | dephased

def Law.state : Law → QIT.State Registers
  | .coherent => RecordAccess.coherent
  | .dephased => RecordAccess.dephased

/-- Access is encoded by the constructor; a joint test cannot be labeled local. -/
inductive Protocol where
  | localTest (test : FiniteQuantum.Test Bool Registers Registers)
  | jointTest (test : FiniteQuantum.Test Registers Registers Registers)

def Protocol.localOnly : Protocol → Prop
  | .localTest _ => True
  | .jointTest _ => False

def predict (law : Law) : Protocol → Behavior { Setting := Unit, Outcome := Registers }
  | .localTest t => FiniteQuantum.behavior law.state.marginalA (fun _ => t)
  | .jointTest t => FiniteQuantum.behavior law.state (fun _ => t)

theorem locally_equivalent :
    ExperimentAccess.Equivalent predict Protocol.localOnly .coherent .dephased := by
  intro p hp s o
  cases p with
  | localTest t => exact all_local_tests t o
  | jointTest t => exact False.elim hp

/-- Explicit newly available intervention, with a checked gap 288/625. -/
def separator : ExperimentAccess.Separator predict (fun _ => True) .coherent .dephased where
  protocol := .jointTest recoveryTest
  accessible := trivial
  setting := ()
  outcome := (false,false)
  gap := 288 / 625
  positive := by norm_num
  difference := by
    change recoveryTest.prob coherent (false,false) - recoveryTest.prob dephased (false,false) = _
    rw [coherent_recovery, dephased_recovery]
    norm_num

theorem joint_not_equivalent :
    ¬ ExperimentAccess.Equivalent predict (fun _ => True) .coherent .dephased :=
  separator.not_equivalent

/-- Same model pair and prediction semantics, reported over local-only access. -/
def localComparison :
    Comparison.Result predict Protocol.localOnly .coherent .dephased :=
  .agreement ⟨locally_equivalent⟩

/-- Enlarged access admits the checked recovery separator. -/
def jointComparison :
    Comparison.Result predict (fun _ => True) .coherent .dephased :=
  .separation separator

def localComparisonClaim : Claim := localComparison.claim
def jointComparisonClaim : Claim := jointComparison.claim

def coherentClaim : Claim := .exact (recoveryTest.prob coherent (false,false)) 1
  (by simpa using coherent_recovery)
def dephasedClaim : Claim := .exact (recoveryTest.prob dephased (false,false)) (337/625)
  (by convert dephased_recovery using 1 <;> norm_num)
end
end OntologySeparation.RecordAccess
