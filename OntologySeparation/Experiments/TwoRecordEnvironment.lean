import OntologySeparation.Experiments.EnvironmentDiscrimination

/-! Two explicit perfect environment copies.

The state contains the laboratory (system + friend record) and two independent
environment qubits that both copy the same branch bit.  Tracing out either one
perfect record copy is enough to remove all branch coherence from the remaining
laboratory + accessible-copy subsystem.

This is the first nontrivial multi-record quantum base case for the
access-sensitive consensus/monogamy program. -/

namespace OntologySeparation.TwoRecordEnvironment
noncomputable section
open scoped ComplexOrder MatrixOrder

abbrev Laboratory := RecordEnvironment.Laboratory
abbrev Accessible := Laboratory × Bool
abbrev Registers := Accessible × Bool

/-- Tensor order is (((system, friend), environment₁), environment₂). -/
def source : QIT.PureVector Registers where
  amp i :=
    if i.1.1.1 = i.1.1.2 ∧ i.1.1.1 = i.1.2 ∧ i.1.1.1 = i.2 then
      (if i.1.1.1 then 4 / 5 else 3 / 5)
    else 0
  trace_rankOne_eq_one := by
    apply Complex.ext <;>
      norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
        Fintype.sum_prod_type, Fintype.sum_bool,
        Complex.div_re, Complex.div_im]

def coherent : QIT.State Registers := source.state

def collapsed : QIT.State Registers :=
  (QIT.Channel.measure (QIT.POVM.coordinate Registers)).applyState coherent

theorem collapsed_entry (i j : Registers) :
    collapsed.matrix i j = if i = j then coherent.matrix i i else 0 := by
  change ((QIT.Channel.measure (QIT.POVM.coordinate Registers)).map coherent.matrix) i j = _
  rw [QIT.Channel.measure_map_state_diagonal]
  simp [QIT.POVM.coordinate, Matrix.trace_mul_single, Matrix.diagonal]

/-- If environment₂ is inaccessible, the entire accessible subsystem
(laboratory + environment₁) is already dephased. -/
theorem one_copy_missing_state :
    coherent.marginalA = collapsed.marginalA := by
  apply QIT.State.ext
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,d⟩,f⟩
  change
    (∑ g : Bool, coherent.matrix (((a,b),e),g) (((c,d),f),g)) =
    ∑ g : Bool, collapsed.matrix (((a,b),e),g) (((c,d),f),g)
  simp_rw [collapsed_entry]
  cases a <;> cases b <;> cases e <;>
    cases c <;> cases d <;> cases f <;>
    norm_num [coherent, source, QIT.PureVector.state, QIT.rankOneMatrix,
      Matrix.vecMulVec, Fintype.sum_bool]

/-- Hence no finite CPTP evolution and POVM on laboratory + one copied record can
distinguish the coherent and collapsed laws. -/
theorem every_one_copy_test {B O : Type}
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (t : FiniteQuantum.Test Accessible B O) (o : O) :
    t.prob coherent.marginalA o = t.prob collapsed.marginalA o := by
  rw [one_copy_missing_state]

/-- The full coherent state is globally distinct from the collapsed state. -/
theorem global_states_differ : coherent ≠ collapsed := by
  intro h
  have he := congrArg (fun s : QIT.State Registers =>
    s.matrix (((false,false),false),false) (((true,true),true),true)) h
  dsimp only at he
  rw [collapsed_entry] at he
  norm_num [coherent, source, QIT.PureVector.state, QIT.rankOneMatrix,
    Matrix.vecMulVec] at he

/-- Therefore full-register access has some finite quantum test that performs
strictly better than chance at discriminating the two laws. -/
theorem full_access_strictly_distinguishes :
    QuantumDiscrimination.minimumError coherent collapsed < 1 / 2 := by
  exact QuantumDiscrimination.minimumError_lt_half coherent collapsed global_states_differ

end
end OntologySeparation.TwoRecordEnvironment
