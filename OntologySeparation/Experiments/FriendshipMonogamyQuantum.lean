import OntologySeparation.Experiments.FriendshipMonogamy
import OntologySeparation.Experiments.RecordEnvironment

/-!
# Explicit two-copy quantum record model

This file begins the Hilbert-space upgrade of the effective overlap theorem in
`FriendshipMonogamy`.

The state contains four physical qubits:

* system;
* friend record;
* redundant environment record A;
* redundant environment record B.

Both environment records are perfect copies of the same friend event.  Observer A
is allowed the laboratory plus copy A while copy B is inaccessible; observer B has
the mirror access pattern.  Tracing out either inaccessible perfect copy removes
the branch coherence exactly.

The result is deliberately stronger and more physical than the product-of-overlaps
bookkeeping theorem: the reduced states are calculated from one explicit pure
state, and the consequence applies to arbitrary finite quantum tests on each
observer's accessible subsystem.
-/

namespace OntologySeparation.FriendshipMonogamyQuantum
noncomputable section
open scoped ComplexOrder MatrixOrder

abbrev Laboratory := RecordEnvironment.Laboratory
abbrev AccessibleRegion := Laboratory × Bool
abbrev Registers := AccessibleRegion × Bool

/-- Branching state with two perfect redundant copies of the friend record.
Tensor order is (((system, friend), recordA), recordB). -/
def source : QIT.PureVector Registers where
  amp i :=
    if i.1.1.1 = i.1.1.2 ∧ i.1.1.1 = i.1.2 ∧ i.1.1.1 = i.2 then
      (if i.1.1.1 then 4 / 5 else 3 / 5)
    else 0
  trace_rankOne_eq_one := by
    apply Complex.ext <;>
      norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
        Fintype.sum_prod_type, Fintype.sum_bool, Complex.div_re, Complex.div_im]

def coherent : QIT.State Registers := source.state

/-- Observer A keeps the laboratory and record A and loses record B.  The lost
perfect copy dephases the entire retained branch label. -/
theorem observerA_state :
    coherent.marginalAB = RecordEnvironment.collapsed := by
  apply QIT.State.ext
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,d⟩,f⟩
  change
    (∑ g : Bool,
      coherent.matrix (((a,b),e),g) (((c,d),f),g)) =
      RecordEnvironment.collapsed.matrix ((a,b),e) ((c,d),f)
  rw [RecordEnvironment.collapsed_entry]
  cases a <;> cases b <;> cases e <;>
    cases c <;> cases d <;> cases f <;>
      norm_num [coherent, source, RecordEnvironment.coherent,
        RecordEnvironment.source, QIT.PureVector.state, QIT.rankOneMatrix,
        Matrix.vecMulVec, Fintype.sum_bool]

/-- Observer B keeps the laboratory and record B and loses record A.  By the
same physical calculation, the inaccessible perfect copy dephases B's retained
state as well. -/
theorem observerB_state :
    coherent.marginalAC = RecordEnvironment.collapsed := by
  apply QIT.State.ext
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨c,d⟩,f⟩
  change
    (∑ g : Bool,
      coherent.matrix (((a,b),g),e) (((c,d),g),f)) =
      RecordEnvironment.collapsed.matrix ((a,b),e) ((c,d),f)
  rw [RecordEnvironment.collapsed_entry]
  cases a <;> cases b <;> cases e <;>
    cases c <;> cases d <;> cases f <;>
      norm_num [coherent, source, RecordEnvironment.coherent,
        RecordEnvironment.source, QIT.PureVector.state, QIT.rankOneMatrix,
        Matrix.vecMulVec, Fintype.sum_bool]

/-- The two disjoint one-copy access regions are simultaneously dephased. -/
theorem disjoint_single_copy_views :
    coherent.marginalAB = RecordEnvironment.collapsed ∧
      coherent.marginalAC = RecordEnvironment.collapsed :=
  ⟨observerA_state, observerB_state⟩

/-- This is not a claim about one chosen recovery circuit: every finite channel
and readout acting only on observer A's accessible region sees exactly the
dephased state. -/
theorem every_observerA_test
    {B O : Type} [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (t : FiniteQuantum.Test AccessibleRegion B O) (o : O) :
    t.prob coherent.marginalAB o = t.prob RecordEnvironment.collapsed o := by
  rw [observerA_state]

/-- Mirror universal statement for observer B. -/
theorem every_observerB_test
    {B O : Type} [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (t : FiniteQuantum.Test AccessibleRegion B O) (o : O) :
    t.prob coherent.marginalAC o = t.prob RecordEnvironment.collapsed o := by
  rw [observerB_state]

/-- In this explicit two-copy state, giving each superobserver one disjoint
redundant record does not give either observer access to branch coherence: the
other perfect record is enough to destroy all off-diagonal terms in the retained
density matrix. -/
theorem two_copy_access_obstruction :
    (∀ {B O : Type} [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
      (t : FiniteQuantum.Test AccessibleRegion B O) (o : O),
        t.prob coherent.marginalAB o = t.prob RecordEnvironment.collapsed o) ∧
    (∀ {B O : Type} [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
      (t : FiniteQuantum.Test AccessibleRegion B O) (o : O),
        t.prob coherent.marginalAC o = t.prob RecordEnvironment.collapsed o) := by
  constructor
  · intro B O _ _ _ _ t o
    exact every_observerA_test t o
  · intro B O _ _ _ _ t o
    exact every_observerB_test t o

end
end OntologySeparation.FriendshipMonogamyQuantum
