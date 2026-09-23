import OntologySeparation.Experiments.EnvironmentDiscrimination

/-! Explicit quantum access-separation benchmark.

The existing RecordEnvironment construction contains a laboratory register
(system + friend record) and a copied environment record.  This file proves that
coherent and collapsed laws are indistinguishable on either disjoint subsystem
alone, while the already-checked joint return measurement distinguishes them.

This is the Hilbert-space replacement for the effective "zero overlap kills the
fringe" bookkeeping used in FriendshipMonogamy. -/

namespace OntologySeparation.QuantumAccessMonogamy
noncomputable section

open RecordEnvironment

/-- Losing the laboratory and retaining only the environment also erases the
coherent/collapsed distinction. -/
theorem same_environment_state :
    RecordEnvironment.coherent.marginalB =
      RecordEnvironment.collapsed.marginalB := by
  apply QIT.State.ext
  ext e f
  change
    (∑ l : RecordEnvironment.Laboratory,
      RecordEnvironment.coherent.matrix (l,e) (l,f)) =
    ∑ l : RecordEnvironment.Laboratory,
      RecordEnvironment.collapsed.matrix (l,e) (l,f)
  simp_rw [RecordEnvironment.collapsed_entry]
  cases e <;> cases f <;>
    norm_num [RecordEnvironment.coherent, RecordEnvironment.source,
      QIT.PureVector.state, QIT.rankOneMatrix, Matrix.vecMulVec,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-- Every finite channel + POVM confined to the environment alone agrees. -/
theorem every_environment_test {B O : Type}
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (t : FiniteQuantum.Test Bool B O) (o : O) :
    t.prob RecordEnvironment.coherent.marginalB o =
      t.prob RecordEnvironment.collapsed.marginalB o := by
  rw [same_environment_state]

/-- Every finite laboratory-only test agrees; restated here so the two disjoint
local regions appear in one theorem namespace. -/
theorem every_laboratory_test {B O : Type}
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (t : FiniteQuantum.Test RecordEnvironment.Laboratory B O) (o : O) :
    t.prob RecordEnvironment.coherent.marginalA o =
      t.prob RecordEnvironment.collapsed.marginalA o :=
  RecordEnvironment.every_laboratory_test t o

/-- Joint coherent control recovers an operational distinction with exact gap. -/
theorem joint_return_gap :
    RecordEnvironment.returnTest.prob RecordEnvironment.coherent true -
      RecordEnvironment.returnTest.prob RecordEnvironment.collapsed true =
      (288 : ℝ) / 625 := by
  rw [RecordEnvironment.return_coherent, RecordEnvironment.return_collapsed]
  norm_num

/-- The same pair of laws is locally indistinguishable on each disjoint factor
but distinguishable on the joint tensor product. -/
theorem disjoint_local_blind_joint_separates :
    RecordEnvironment.coherent.marginalA =
        RecordEnvironment.collapsed.marginalA ∧
      RecordEnvironment.coherent.marginalB =
        RecordEnvironment.collapsed.marginalB ∧
      RecordEnvironment.returnTest.prob RecordEnvironment.coherent true ≠
        RecordEnvironment.returnTest.prob RecordEnvironment.collapsed true := by
  refine ⟨RecordEnvironment.same_laboratory_state, same_environment_state, ?_⟩
  intro h
  have hg := joint_return_gap
  rw [h] at hg
  norm_num at hg

end
end OntologySeparation.QuantumAccessMonogamy
