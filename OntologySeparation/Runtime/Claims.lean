import Lean

/-! Enumerated theorem references for the executable. Catalog/Evidence resolves
EVERY constructor to a Lean proof and verifies declaration-name consistency. -/
namespace OntologySeparation.Catalog

inductive ClaimId where
  | bellLocal | bellQuantum | bellPR | lfBound | lfQuantum | lfControl | echo | leak | phase
  deriving Repr, BEq, DecidableEq

def ClaimId.declaration : ClaimId → String
  | .bellLocal => "QIT.Bell.CHSH.value_le_two_of_isLocal"
  | .bellQuantum => "OntologySeparation.Catalog.bellQuantumEvidence"
  | .bellPR => "OntologySeparation.Catalog.bellPREvidence"
  | .lfBound => "OntologySeparation.Catalog.lfBoundEvidence"
  | .lfQuantum => "OntologySeparation.Catalog.lfQuantumEvidence"
  | .lfControl => "OntologySeparation.LF.exists_bell_violation_within_LF"
  | .echo => "OntologySeparation.Memory.echo_probability"
  | .leak => "OntologySeparation.Memory.leakedEcho_probability"
  | .phase => "OntologySeparation.Memory.phaseEcho_probability"

end OntologySeparation.Catalog
