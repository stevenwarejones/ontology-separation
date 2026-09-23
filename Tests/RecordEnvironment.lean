import OntologySeparation.Experiments.RecordEnvironment

namespace OntologySeparation.Tests
open RecordEnvironment

example : coherent.marginalA = RecordAccess.dephased := laboratory_state
example : coherent ≠ collapsed := global_states_differ

-- A full-register channel/readout cannot be relabeled as a laboratory test.
example (t : FiniteQuantum.Test Registers Registers Bool) : True := by
  fail_if_success
    have bad : FiniteQuantum.Named.Protocol Laboratory Bool Registers Bool :=
      .localTest t
  trivial

example (t : FiniteQuantum.Test Registers Registers Bool) :
    ¬ RegisterAccess.Allowed (FiniteQuantum.Named.footprint names)
      (FiniteQuantum.Named.leftPolicy names) (.jointTest t) := by
  rw [FiniteQuantum.Named.left_allowed_iff]
  exact not_false
end OntologySeparation.Tests
