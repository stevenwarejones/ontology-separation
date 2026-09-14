import OntologySeparation.Catalog.Extensions
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
  | verifiedConditional
  | requiresExtension
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

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

/-- A missing law is stated concretely, with a separately checked candidate experiment.
The generic extension theorem is conditional on adding an independent sector. -/
def needsExtension (s : Scenario) (m : ModelInfo) : Cell :=
  let reason := if let some e := extensionFor s then
    "Additional law needed: " ++ e.requiredLaw
  else if s.family == .echo || s.family == .leak || s.family == .phase then
    "Needs preparation, record channel, reversal channel, and readout laws"
  else "Needs a bipartite measurement interface and its relation to this model's dynamics"
  ⟨s.id, m.id, .requiresExtension, reason, none,
    ["No unique prediction follows from the model's currently defined sector"],
    m.scope ++ "; " ++ s.obligations⟩

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
  else needsExtension s m

/-- Curated backend selection. New families should get an interpreter, not invented cells. -/
def evaluate (s : Scenario) (m : ModelInfo) : Cell :=
  if s.id == "P03" && m.id == "no_signaling" then
    checked s m .verifiedConditional "IF LF + NS contamination: G <= 6+4 epsilon (sharp)" .nsFraction
      ["ADDITIONAL LAW: mixture of an LF sector and a normalized no-signaling sector",
       "0 <= epsilon <= 1; epsilon >= (G-6)/4",
       "Sharpness: Shared.LF_NS_contamination_attained; not a communication-cost theorem"]
  else if s.family == .research then
    if let some e := extensionFor s then
      checked s m .verifiedConditional ("IF added law: " ++ e.result) (extensionClaim s)
        ["ADDITIONAL LAW, not entailed by " ++ m.title, e.requiredLaw, e.scope]
    else needsExtension s m
  else if let some model := memoryModel m.id then
    if s.family == .bell || s.family == .lfControl then
      checked s m .verifiedConditional
        ("With dephased-singlet preparation: S = " ++ toString ((1502 - 1152 * model.strength) / 625))
        .noisyBell ["ADDED bipartite singlet preparation", "Z dephasing weight p=" ++ toString model.strength,
          "Use the specified Bell projective bases; same two non-friend settings for B03"]
    else if s.family == .lf then
      checked s m .verifiedConditional
        ("With dephased-singlet preparation: G = " ++ toString ((1214656 - 476928 * model.strength) / 180625))
        .noisyLF ["ADDED bipartite singlet preparation and ideal friend reversal",
          "Z dephasing weight p=" ++ toString model.strength, "Use the specified LF bases"]
    else memoryCell s m model
  else if s.family == .echo then
    checked s m .verifiedConditional "With memory-channel law: P(+) = 1-p/2" .echo
      ["ADDED two-qubit |+0> preparation and record/reverse/readout model", "0 <= p <= 1; column does not fix p"]
  else if s.family == .leak then
    checked s m .verifiedConditional "With complete inaccessible leakage: P(+) = 1/2" .leak
      ["ADDED two-qubit memory model and complete record leakage before reversal"]
  else if s.family == .phase then
    checked s m .verifiedConditional "With phase-echo channel law: P(+) = p/2" .phase
      ["ADDED coherent control and memory channel", "0 <= p <= 1; column does not fix p"]
  else if s.family == .bell && m.id == "bell_local" then
    checked s m .verifiedBound "S <= 2" ClaimId.bellLocal
      ["Local response mixture", "Setting-independent mixture weights"]
  else if s.family == .bell && m.id == "no_signaling" then
    checked s m .verifiedWitness "PR witness S = 4" ClaimId.bellPR ["No-signaling behavior class"]
  else if s.family == .bell && m.id == "real_singlet" then
    checked s m .verifiedWitness "S = 1502/625 > 2" ClaimId.bellQuantum
      ["Normalized singlet", "Specified rational projective measurement bases"]
  else if s.family == .bell && m.id == "local_friendliness" then
    checked s m .verifiedWitness "Inner-setting CHSH = 4" .innerPR
      ["LF conditional PR component", "Restrict to the two non-friend settings"]
  else if s.family == .lf && m.id == "bell_local" then
    checked s m .verifiedBound "G <= 6" .localThree
      ["Three-setting finite deterministic local response mixtures", "Setting-independent weights"]
  else if s.family == .lf && m.id == "no_signaling" then
    checked s m .verifiedBound "G <= 10 (attained)" .nsLF
      ["Three-setting normalized no-signaling probabilities", "Explicit extremal box attains 10"]
  else if s.family == .lf && m.id == "local_friendliness" then
    checked s m .verifiedBound "G <= 6" ClaimId.lfBound
      ["Conditional no-signaling", "Actual friend records", "Setting-independent prior"]
  else if s.family == .lf && m.id == "real_singlet" then
    checked s m .verifiedWitness "G = 1214656/180625 > 6" ClaimId.lfQuantum
      ["Normalized singlet", "Ideal coherent friend reversal", "Specified bases"]
  else if s.family == .lfControl && m.id == "bell_local" then
    checked s m .verifiedBound "Inner CHSH <= 2" .bellLocal
      ["Two non-friend settings use the Bell local interface", "Setting restriction preserves local response mixtures"]
  else if s.family == .lfControl && m.id == "no_signaling" then
    checked s m .verifiedWitness "Inner CHSH = 4" .innerPR
      ["LF PR component is no-signaling (Shared.lf_noSignaling)", "Same non-friend setting restriction"]
  else if s.family == .lfControl && m.id == "real_singlet" then
    checked s m .verifiedWitness "Inner CHSH = 1502/625 > 2" .bellQuantum
      ["Assign the Bell singlet bases to the two non-friend settings", "No assertion that this witness is LF-compatible"]
  else if s.family == .lfControl && m.id == "local_friendliness" then
    checked s m .verifiedWitness "Inner CHSH = 4 while genuine LF bound holds" ClaimId.lfControl
      ["Fixed friend records", "Conditional PR inner box"]
  else needsExtension s m

def matrix : List Cell := scenarios.flatMap fun s => models.map (evaluate s)

/-- Profile syntax is exported separately; no model is assigned a profile without a proof. -/
def report : Lean.Json := Lean.Json.mkObj [
  ("schema_version", Lean.toJson (2 : Nat)),
  ("scenarios", Lean.toJson scenarios),
  ("models", Lean.toJson models),
  ("cells", Lean.toJson matrix),
  ("extensions", Lean.toJson extensions),
  ("independent_extension_theorem", Lean.toJson ClaimId.freeExtension.declaration),
  ("binary_profiles", Lean.toJson binaryProfiles),
  ("profile_notice", Lean.toJson
    "Sixteen expressible profiles; physical realizability requires an explicit vocabulary and witness.")
]

end OntologySeparation.Catalog
