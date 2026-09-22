import OntologySeparation.Experiments.RecordAccess

open OntologySeparation
open OntologySeparation.FiniteQuantum
open OntologySeparation.RecordAccess

noncomputable section

/-- The existing recovery experiment is exactly the new public one-step
isometry-plus-POVM constructor, not a second implementation. -/
example :
    measureAfterIsometry (QIT.POVM.coordinate Registers) recovery recovery_isometry =
      recoveryTest := rfl

example :
    (measureAfterIsometry (QIT.POVM.coordinate Registers) recovery recovery_isometry).prob
        coherent (false, false) = 1 := by
  simpa using coherent_recovery

example :
    (measureAfterIsometry (QIT.POVM.coordinate Registers) recovery recovery_isometry).prob
        dephased (false, false) = 337 / 625 := by
  simpa using dephased_recovery

end
