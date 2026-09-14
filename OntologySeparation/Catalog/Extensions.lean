import OntologySeparation.Catalog.Scenarios
import OntologySeparation.Runtime.Claims
import OntologySeparation.Runtime.Research

/-! Explicit additional-law experiments. These are not automatic predictions of
any existing universe column. Every claim resolves to a kernel-checked theorem. -/
namespace OntologySeparation.Catalog

structure ExtensionInfo where
  scenario : String
  title : String
  requiredLaw : String
  result : String
  contrast : String
  declaration : String
  scope : String
  deriving Repr, Lean.ToJson, Lean.FromJson

def extension (s : String) (title law result contrast : String) (claim : ClaimId)
    (scope : String) : ExtensionInfo :=
  ⟨s, title, law, result, contrast, claim.declaration, scope⟩

def extensions : List ExtensionInfo := [
  extension "P01" "Three-record gluing test"
    "A single setting-independent joint distribution over three binary records"
    "Expected number of disagreeing edges <= 2"
    "Three separately anticorrelated, fair contexts give 3 and have no joint extension"
    .triangle "Abstract contextual probability model; not a demonstrated quantum or friend implementation.",
  extension "P03" "LF contamination budget"
    "Mixture of an LF behavior and an arbitrary normalized behavior; outside fraction epsilon"
    "G <= 6 + 8 epsilon; epsilon >= (G-6)/8"
    "If the bad sector is also no-signaling: G <= 6+4 epsilon, attained; epsilon >= (G-6)/4. See Shared.LF_NS_fraction_required and Shared.LF_NS_contamination_attained."
    .contamination "Conservative arbitrary-behavior bound. Fraction of non-LF runs is not communication, signaling strength, or a causal influence metric.",
  extension "P05" "Access to a parity-encoded record"
    "Two independent fair classical bits; decoder sees only one share"
    ("Every randomized one-share decoder succeeds with " ++ toString (Research.oneBitRecovery (fun _ => 0)))
    ("Joint access and parity decoder succeeds with " ++ toString (Research.jointRecovery xor))
    .recovery "Operational access changes. Passive invertible relabeling leaves predictions unchanged; no quantum subsystem-recovery claim.",
  extension "P06" "Pauli-order interference"
    "Normalized real target; coherently superpose XZ and ZX; dephase order control with strength p"
    "Minus-port probability = 1-p/2"
    "p=0: 1; p=1/2: 3/4; p=1: 1/2"
    .order "Gate-specific calibration. A known-gate fixed-order circuit can imitate this statistic; not a causal-nonseparability or friend-order witness.",
  extension "P07" "Controlled-phase product-state test"
    "Pure real two-qubit amplitudes; coherent CZ applied to |++>"
    "Normalized output has determinant -1/2 and is not a product amplitude"
    "Every pure real product amplitude has determinant zero"
    .mediator "Pure-state calculation; requires purity and state reconstruction. No gravity model, coupling scale, mixed-state separability theorem, or generic classical-mediator exclusion.",
  extension "P08" "Classical query-budget recovery"
    "Two fair bits; at most one classical bit query; arbitrary randomized response and query choice"
    "Success = 1/2 for every such decoder"
    "Two classical queries allow success 1"
    .query "A small exact algorithm-class obstruction, not an asymptotic complexity result or a bound on coherent quantum queries.",
  extension "P10" "Public agreement composition"
    "A single joint distribution over three public binary records A,B,C"
    "P(A != C) <= P(A != B) + P(B != C)"
    "Zero adjacent disagreement forces zero end-to-end disagreement"
    .agreement "Does not compose inaccessible observer-relative records; the common joint distribution is an explicit premise."
]

/-- Every former placeholder has a concrete checked subproblem. -/
def extensionFor (s : Scenario) : Option ExtensionInfo :=
  extensions.find? fun e => e.scenario == s.id

end OntologySeparation.Catalog

namespace OntologySeparation.Catalog

def extensionClaim (s : Scenario) : ClaimId :=
  if s.id == "P01" then .triangle
  else if s.id == "P03" then .contamination
  else if s.id == "P05" then .recovery
  else if s.id == "P06" then .order
  else if s.id == "P07" then .mediator
  else if s.id == "P08" then .query
  else .agreement

end OntologySeparation.Catalog
