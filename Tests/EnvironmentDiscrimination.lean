import OntologySeparation.Experiments.EnvironmentDiscrimination

namespace OntologySeparation.Tests
open RecordEnvironment QuantumDiscrimination

example : returnTest.prob coherent true - returnTest.prob collapsed true = 288 / 625 := by
  rw [return_coherent, return_collapsed]
  norm_num

-- A specified recovery witness is not automatically the optimal measurement.
-- Likewise a globally separating test is not permitted in the laboratory class.
example : ¬ RegisterAccess.Allowed (FiniteQuantum.Named.footprint names)
    (FiniteQuantum.Named.leftPolicy names)
    (FiniteQuantum.Named.Protocol.jointTest returnTest) := by
  rw [FiniteQuantum.Named.left_allowed_iff]
  exact not_false

example : minimumError coherent coherent = 0 + 1 / 2 := by
  simp [minimumError]

example : error coherent collapsed fullOptimal < 1 / 2 := full_beats_laboratory
end OntologySeparation.Tests
