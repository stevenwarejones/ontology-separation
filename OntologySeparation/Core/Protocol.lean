import Lean

/-! Human-readable protocol descriptions and explicit capability checking.
A protocol description is not itself a proof that a physical implementation exists. -/
namespace OntologySeparation

/-- Extensible capability identifiers avoid a closed list of possible physical laws. -/
abbrev Capability := String

structure Operation where
  action : String
  systems : List String
  requires : List Capability := []
  deriving Repr, Lean.ToJson, Lean.FromJson

structure ProtocolDescription where
  systems : List String
  preparation : String
  operations : List Operation
  settings : List String
  outcomes : List String
  observable : String
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Return missing capabilities. An unavailable action is not assigned probability zero. -/
def missingCapabilities (available : List Capability) (p : ProtocolDescription) : List Capability :=
  ((p.operations.flatMap (·.requires)).filter fun c => !available.contains c).eraseDups

end OntologySeparation
