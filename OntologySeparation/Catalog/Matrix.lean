import OntologySeparation.Catalog.Extensions
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

/-- Model parameters have one source; metadata and dispatch both use this list. -/
def memoryModels : List (String × Memory.Model) := [
  ("unitary_memory", ⟨0, by norm_num, by norm_num⟩),
  ("dephased_memory", ⟨1, by norm_num, by norm_num⟩),
  ("partial_memory", ⟨1/2, by norm_num, by norm_num⟩)]
def memoryModel (id : String) : Option Memory.Model :=
  (memoryModels.find? fun entry => entry.1 == id).map Prod.snd

def models : List ModelInfo := [
  ⟨"bell_local", "Bell-local", "assumption class", "Finite local response mixtures"⟩,
  ⟨"local_friendliness", "Local Friendliness", "assumption class",
    "Three-setting conditional no-signaling friend models"⟩,
  ⟨"no_signaling", "No-signaling", "assumption class", "Bipartite marginal independence"⟩,
  ⟨"real_singlet", "Quantum singlet", "concrete model family", "Real projective two-qubit measurements"⟩
] ++ memoryModels.map (fun (id, m) =>
  ⟨id, "Memory dephasing p=" ++ toString m.strength, "concrete toy dynamics",
    "Two-qubit record channel p=" ++ toString m.strength⟩)

/-- Additional laws are explicitly separate from the evidence kind. -/
inductive Applicability where
  | native | additional
  deriving Repr, BEq, DecidableEq

/-- Every reported result is a proof-bearing claim. Descriptions are context only. -/
structure Cell where
  scenario : String
  model : String
  applicability : Applicability
  claim : Option Claim
  assumptions : List String
  limitation : String
  supporting : List Claim

noncomputable section

def checked (s : Scenario) (m : ModelInfo) (claim : Claim)
    (assumptions : List String) (applicability : Applicability := .native) (supporting : List Claim := []) : Cell :=
  ⟨s.id, m.id, applicability, some claim, assumptions, s.obligations, supporting⟩
def needsExtension (s : Scenario) (m : ModelInfo) : Cell :=
  ⟨s.id, m.id, .additional, none, ["No interpretation supplied for this model and protocol"],
    m.scope ++ "; " ++ s.obligations, []⟩


def memoryCell (s : Scenario) (m : ModelInfo) (model : Memory.Model) : Cell :=
  let assumptions := ["Initial |+0>; rational two-qubit memory dynamics", "Record dephasing p=" ++ toString model.strength]
  if s.family == .echo then checked s m (memoryClaim model Memory.echo) assumptions
  else if s.family == .leak then checked s m (memoryClaim model Memory.leakedEcho)
    (assumptions ++ ["Complete inaccessible leakage before reversal"])
  else if s.family == .phase then checked s m (memoryClaim model Memory.phaseEcho)
    (assumptions ++ ["Signal phase flip before reversal"])
  else needsExtension s m

/-- Only the interpretation dispatch is curated. Values and evidence kinds come from proofs. -/
def evaluate (s : Scenario) (m : ModelInfo) : Cell :=
  if s.id == "P03" && m.id == "no_signaling" then
    checked s m nsFractionClaim
      ["ADDITIONAL LAW: LF + normalized no-signaling mixture", "0 ≤ epsilon ≤ 1; not a communication-cost theorem"] .additional (researchSupporting s.id)
  else if s.family == .research then
    if let some e := extensionFor s then
      checked s m e.claim ["ADDITIONAL LAW, not entailed by " ++ m.title, e.requiredLaw, e.scope] .additional (researchSupporting s.id)
    else needsExtension s m
  else if let some model := memoryModel m.id then
    if s.family == .bell || s.family == .lfControl then
      checked s m (noisyBellClaim model)
        ["ADDITIONAL LAW: bipartite singlet preparation and specified Bell bases", "Z dephasing p=" ++ toString model.strength] .additional
    else if s.family == .lf then
      checked s m (noisyLFClaim model)
        ["ADDITIONAL LAW: singlet preparation, specified LF bases and ideal friend reversal", "Z dephasing p=" ++ toString model.strength] .additional
    else memoryCell s m model
  else if s.family == .echo then
    checked s m echoClaim ["ADDITIONAL LAW: two-qubit record/reverse/readout channel; column does not fix p"] .additional
  else if s.family == .leak then
    checked s m leakClaim ["ADDITIONAL LAW: two-qubit memory and complete inaccessible leakage"] .additional
  else if s.family == .phase then
    checked s m phaseClaim ["ADDITIONAL LAW: coherent phase control and memory channel; column does not fix p"] .additional
  else if s.family == .bell && m.id == "bell_local" then
    checked s m bellLocalClaim ["Finite local response mixtures with setting-independent weights"]
  else if s.family == .bell && m.id == "no_signaling" then
    checked s m bellPRClaim ["Normalized two-setting no-signaling behaviors"]
  else if s.family == .bell && m.id == "real_singlet" then
    checked s m bellQuantumClaim ["Normalized singlet and specified rational measurement bases"] .native [bellExclusionClaim]
  else if s.family == .bell && m.id == "local_friendliness" then
    checked s m lfControlClaim ["LF component with actual records; two non-friend settings"]
  else if s.family == .lf && m.id == "bell_local" then
    checked s m localThreeClaim ["Three-setting local mixtures with setting-independent weights"]
  else if s.family == .lf && m.id == "no_signaling" then
    checked s m nsLFClaim ["Three-setting no-signaling behaviors"] .native [nsAttainmentClaim]
  else if s.family == .lf && m.id == "local_friendliness" then
    checked s m lfBoundClaim ["Conditional no-signaling, actual friend records, setting-independent prior"]
  else if s.family == .lf && m.id == "real_singlet" then
    checked s m lfQuantumClaim ["Normalized singlet; ideal friend reversal; specified bases"] .native [lfExclusionClaim]
  else if s.family == .lfControl && m.id == "bell_local" then
    checked s m bellLocalClaim ["Bell-local interface for the two non-friend settings"]
  else if s.family == .lfControl && m.id == "no_signaling" then
    checked s m innerPRClaim ["No-signaling LF component restricted to non-friend settings"]
  else if s.family == .lfControl && m.id == "real_singlet" then
    checked s m bellQuantumClaim ["Bell singlet bases assigned to the non-friend settings; no LF membership claim"]
  else if s.family == .lfControl && m.id == "local_friendliness" then
    checked s m lfControlClaim ["Fixed friend records and a conditional PR inner box"]
  else needsExtension s m

def matrix : List Cell := scenarios.flatMap fun s => models.map (evaluate s)
end
end OntologySeparation.Catalog
