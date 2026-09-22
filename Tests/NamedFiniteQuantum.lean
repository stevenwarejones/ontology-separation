import OntologySeparation.Adapters.NamedFiniteQuantum
import OntologySeparation.Experiments.RecordAccess

open OntologySeparation
open OntologySeparation.RecordAccess

noncomputable section

def genericNames : FiniteQuantum.Named.Names Register where
  left := .system
  right := .record
  distinct := by decide

def localCoordinate :
    FiniteQuantum.Test Bool Bool Bool :=
  FiniteQuantum.measure (QIT.POVM.coordinate Bool)

example :
    RegisterAccess.Allowed
      (FiniteQuantum.Named.footprint genericNames)
      (FiniteQuantum.Named.leftPolicy genericNames)
      (FiniteQuantum.Named.Protocol.localTest (B := Bool) localCoordinate) := by
  rw [FiniteQuantum.Named.left_allowed_iff]
  trivial

example :
    ¬ RegisterAccess.Allowed
      (FiniteQuantum.Named.footprint genericNames)
      (FiniteQuantum.Named.leftPolicy genericNames)
      (FiniteQuantum.Named.Protocol.jointTest (A := Bool) (B := Bool) recoveryTest) := by
  rw [FiniteQuantum.Named.left_allowed_iff]
  simp [FiniteQuantum.Named.Protocol.localOnly]

example :
    RegisterAccess.Allowed
      (FiniteQuantum.Named.footprint genericNames)
      (FiniteQuantum.Named.bothPolicy genericNames)
      (FiniteQuantum.Named.Protocol.jointTest (A := Bool) (B := Bool) recoveryTest) :=
  FiniteQuantum.Named.both_allowed _ _

example :
    ExperimentAccess.Equivalent FiniteQuantum.Named.predict
      (RegisterAccess.Allowed
        (FiniteQuantum.Named.footprint genericNames)
        (FiniteQuantum.Named.leftPolicy genericNames))
      coherent dephased :=
  FiniteQuantum.Named.left_equivalent genericNames coherent dephased same_local_state

end
