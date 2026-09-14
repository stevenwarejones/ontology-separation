import OntologySeparation.Catalog.Scenarios
import OntologySeparation.Runtime.Claims
import OntologySeparation.Runtime.Memory
import OntologySeparation.Core.Assumptions

/-! A small demonstration registry. Extension of the mathematical API never requires
editing this registry: it is a curated client of the generic Core interfaces. -/
namespace OntologySeparation.Catalog

structure ModelInfo where
  id : String
  title : String
  kind : String
  scope : String
  deriving Repr, Lean.ToJson, Lean.FromJson

def models : List ModelInfo := [
  ⟨"bell_local", "Bell-local", "assumption class", "Finite local response mixtures"⟩,
  ⟨"local_friendliness", "Local Friendliness", "assumption class",
    "Three-setting conditional no-signaling friend models"⟩,
  ⟨"no_signaling", "No-signaling", "assumption class", "Bipartite marginal independence"⟩,
  ⟨"real_singlet", "Quantum singlet", "concrete model family", "Real projective two-qubit measurements"⟩,
  ⟨"unitary_memory", "Unitary memory", "concrete toy dynamics", "Two-qubit records; p=0"⟩,
  ⟨"dephased_memory", "Dephased memory", "concrete toy dynamics", "Two-qubit records; p=1"⟩,
  ⟨"partial_memory", "Partial dephasing", "concrete toy dynamics", "Two-qubit records; p=1/2"⟩
]

/-- Status distinguishes checked results from unimplemented physics. -/
inductive Status where
  | verifiedBound
  | verifiedWitness
  | verifiedToyPrediction
  | unresolved
  | outsideScope
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure Cell where
  scenario : String
  model : String
  status : Status
  result : String
  declaration : Option String
  assumptions : List String
  limitation : String
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- The constructor requires a registered claim ID; Evidence resolves every ID to a proof. -/
def checked (s : Scenario) (m : ModelInfo) (status : Status)
    (result : String) (claim : ClaimId) (assumptions : List String) : Cell :=
  ⟨s.id, m.id, status, result, some claim.declaration, assumptions, s.obligations⟩

def unresolved (s : Scenario) (m : ModelInfo) : Cell :=
  ⟨s.id, m.id, .unresolved, "No prediction established", none, [], s.obligations⟩

def outside (s : Scenario) (m : ModelInfo) : Cell :=
  ⟨s.id, m.id, .outsideScope, "This adapter does not interpret this protocol", none,
    [], m.scope ++ "; " ++ s.obligations⟩

/-- The example universe list is finite; the core theory and interpreter APIs are open. -/
def memoryModel (id : String) : Option Memory.Parameters :=
  if id == "unitary_memory" then some Memory.unitary
  else if id == "dephased_memory" then some Memory.collapse
  else if id == "partial_memory" then some Memory.halfDephasing
  else none

/-- Evaluate toy circuits using the Lean matrix interpreter. No prediction lookup table. -/
def memoryCell (s : Scenario) (m : ModelInfo) (model : Memory.Parameters) : Cell :=
  if s.family == .echo then
    checked s m .verifiedToyPrediction (toString (Memory.probability model Memory.echo))
      ClaimId.echo ["Initial |+0>", "Record dephasing strength p=" ++ toString model.strength]
  else if s.family == .leak then
    checked s m .verifiedToyPrediction (toString (Memory.probability model Memory.leakedEcho))
      ClaimId.leak ["Initial |+0>", "Complete inaccessible memory leakage before reversal"]
  else if s.family == .phase then
    checked s m .verifiedToyPrediction (toString (Memory.probability model Memory.phaseEcho))
      ClaimId.phase ["Initial |+0>", "Signal phase flip", "p=" ++ toString model.strength]
  else outside s m

/-- Curated backend selection. New families should get an interpreter, not invented cells. -/
def evaluate (s : Scenario) (m : ModelInfo) : Cell :=
  if s.family == .research then unresolved s m
  else if let some model := memoryModel m.id then memoryCell s m model
  else if s.family == .bell && m.id == "bell_local" then
    checked s m .verifiedBound "S <= 2" ClaimId.bellLocal
      ["Local response mixture", "Setting-independent mixture weights"]
  else if s.family == .bell && m.id == "no_signaling" then
    checked s m .verifiedWitness "PR witness S = 4" ClaimId.bellPR ["No-signaling behavior class"]
  else if s.family == .bell && m.id == "real_singlet" then
    checked s m .verifiedWitness "S = 1502/625 > 2" ClaimId.bellQuantum
      ["Normalized singlet", "Specified rational projective measurement bases"]
  else if s.family == .lf && m.id == "local_friendliness" then
    checked s m .verifiedBound "G <= 6" ClaimId.lfBound
      ["Conditional no-signaling", "Actual friend records", "Setting-independent prior"]
  else if s.family == .lf && m.id == "real_singlet" then
    checked s m .verifiedWitness "G = 1214656/180625 > 6" ClaimId.lfQuantum
      ["Normalized singlet", "Ideal coherent friend reversal", "Specified bases"]
  else if s.family == .lfControl && m.id == "local_friendliness" then
    checked s m .verifiedWitness "Inner CHSH = 4 while genuine LF bound holds" ClaimId.lfControl
      ["Fixed friend records", "Conditional PR inner box"]
  else outside s m

def matrix : List Cell := scenarios.flatMap fun s => models.map (evaluate s)

/-- Profile syntax is exported separately; no model is assigned a profile without a proof. -/
def report : Lean.Json := Lean.Json.mkObj [
  ("schema_version", Lean.toJson (1 : Nat)),
  ("scenarios", Lean.toJson scenarios),
  ("models", Lean.toJson models),
  ("cells", Lean.toJson matrix),
  ("binary_profiles", Lean.toJson binaryProfiles),
  ("profile_notice", Lean.toJson
    "Sixteen expressible profiles; physical realizability requires an explicit vocabulary and witness.")
]

end OntologySeparation.Catalog
