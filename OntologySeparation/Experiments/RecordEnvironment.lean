import OntologySeparation.Experiments.RecordAccess
import OntologySeparation.Adapters.NamedFiniteQuantum

/-! A laboratory (system, friend record) and a distinct environment register.
The two laws differ by an explicit unread coordinate measurement after copying.
This is a specified dynamical alternative, not a classification of interpretations. -/
namespace OntologySeparation.RecordEnvironment
noncomputable section
open scoped ComplexOrder MatrixOrder
abbrev Laboratory := Bool × Bool
abbrev Registers := Laboratory × Bool

/-- Tensor order is ((system, friend record), environment). -/
def source : QIT.PureVector Registers where
  amp i := if i.1.1 = i.1.2 ∧ i.1.1 = i.2 then
    (if i.1.1 then 4 / 5 else 3 / 5) else 0
  trace_rankOne_eq_one := by
    apply Complex.ext <;> norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
      Fintype.sum_prod_type, Fintype.sum_bool, Complex.div_re, Complex.div_im]

def coherent : QIT.State Registers := source.state

/-- An irreversible unread measurement; no hidden record of its outcome is
available to subsequent tests in this model. -/
def collapsed : QIT.State Registers :=
  (QIT.Channel.measure (QIT.POVM.coordinate Registers)).applyState coherent

theorem collapsed_entry (i j : Registers) :
    collapsed.matrix i j = if i = j then coherent.matrix i i else 0 := by
  change ((QIT.Channel.measure (QIT.POVM.coordinate Registers)).map coherent.matrix) i j = _
  rw [QIT.Channel.measure_map_state_diagonal]
  simp [QIT.POVM.coordinate, Matrix.trace_mul_single, Matrix.diagonal]

/-- Copy the friend record into an initially clean environment qubit. -/
def copyEnvironment : Matrix Registers Laboratory ℂ := fun o i =>
  if o.1 = i ∧ o.2 = i.2 then 1 else 0

theorem copyEnvironment_isometry :
    Matrix.conjTranspose copyEnvironment * copyEnvironment = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [copyEnvironment, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply]

/-- The three-register source comes from the existing checked record preparation
by an isometry. The tensor convention is proved, not inferred from names. -/
theorem preparation_is_copy : coherent =
    QIT.POVM.isometryLiftState RecordAccess.coherent copyEnvironment
      copyEnvironment_isometry := by
  apply QIT.State.ext
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,d⟩,f⟩
  cases a <;> cases b <;> cases e <;> cases c <;> cases d <;> cases f <;>
    norm_num [QIT.POVM.isometryLiftState_matrix, copyEnvironment,
      coherent, source, RecordAccess.coherent, RecordAccess.source,
      QIT.PureVector.state, QIT.rankOneMatrix, Matrix.vecMulVec,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-- Losing the environment already dephases the laboratory, even though both
its system and friend record remain controllable. -/
theorem laboratory_state : coherent.marginalA = RecordAccess.dephased := by
  apply QIT.State.ext
  ext ⟨a,b⟩ ⟨c,d⟩
  change (∑ e : Bool, coherent.matrix ((a,b),e) ((c,d),e)) = _
  rw [RecordAccess.dephased_entry]
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [coherent, source, RecordAccess.coherent, RecordAccess.source,
      QIT.PureVector.state, QIT.rankOneMatrix, Matrix.vecMulVec, Fintype.sum_bool]

theorem same_laboratory_state : coherent.marginalA = collapsed.marginalA := by
  apply QIT.State.ext
  ext ⟨a,b⟩ ⟨c,d⟩
  change (∑ e : Bool, coherent.matrix ((a,b),e) ((c,d),e)) =
    ∑ e : Bool, collapsed.matrix ((a,b),e) ((c,d),e)
  simp_rw [collapsed_entry]
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [coherent, source, QIT.PureVector.state, QIT.rankOneMatrix,
      Matrix.vecMulVec, Fintype.sum_bool]

inductive Region where | laboratory | environment
  deriving DecidableEq, Fintype

def names : FiniteQuantum.Named.Names Region :=
  ⟨.laboratory, .environment, by decide⟩

/-- Arbitrary finite local channels and readouts; not a menu of recovery circuits. -/
theorem every_laboratory_test {B O : Type} [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O] (t : FiniteQuantum.Test Laboratory B O) (o : O) :
    t.prob coherent.marginalA o = t.prob collapsed.marginalA o :=
  FiniteQuantum.local_test_eq coherent collapsed same_laboratory_state t o

/-- Access is checked against the test's tensor type, not a display label. -/
theorem laboratory_equivalent :
    ExperimentAccess.Equivalent
      (FiniteQuantum.Named.predict (C := Registers) (O := Bool))
      (RegisterAccess.Allowed (FiniteQuantum.Named.footprint names)
        (FiniteQuantum.Named.leftPolicy names)) coherent collapsed :=
  FiniteQuantum.Named.left_equivalent names coherent collapsed same_laboratory_state

def laboratoryClaim : Claim := .agreement _ _ _ _ laboratory_equivalent

/-- The laws are globally different, despite their identical laboratory state. -/
theorem global_states_differ : coherent ≠ collapsed := by
  intro h
  have he := congrArg (fun s : QIT.State Registers =>
    s.matrix ((false,false),false) ((true,true),true)) h
  dsimp only at he
  rw [collapsed_entry] at he
  norm_num [coherent, source, QIT.PureVector.state, QIT.rankOneMatrix,
    Matrix.vecMulVec] at he
end
end OntologySeparation.RecordEnvironment
