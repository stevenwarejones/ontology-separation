import OntologySeparation.Catalog.Scenarios
import OntologySeparation.Catalog.Evidence
import OntologySeparation.Runtime.Research

/-! Explicit additional-law experiments. These are not automatic predictions of
any existing universe column. Every claim resolves to a kernel-checked theorem. -/
namespace OntologySeparation.Catalog

structure ExtensionInfo where
  scenario : String
  title : String
  requiredLaw : String
  supporting : List Claim
  claim : Claim
  scope : String

def extension (s : String) (title law : String) (claim : Claim)
    (scope : String) : ExtensionInfo :=
  ⟨s, title, law, researchSupporting s, claim, scope⟩

noncomputable def extensions : List ExtensionInfo := [
  extension "P01" "Three-record gluing test"
    "A single setting-independent joint distribution over three binary records"
    triangleClaim "Abstract contextual probability model; not a demonstrated quantum or friend implementation.",
  extension "P03" "LF contamination budget"
    "Mixture of an LF behavior and an arbitrary normalized behavior; outside fraction epsilon"
    contaminationClaim "Conservative arbitrary-behavior bound. Fraction of non-LF runs is not communication, signaling strength, or a causal influence metric.",
  extension "P05" "Access to a parity-encoded record"
    "Two independent fair classical bits; decoder sees only one share"
    recoveryClaim "Operational access changes. Passive invertible relabeling leaves predictions unchanged; no quantum subsystem-recovery claim.",
  extension "P06" "Pauli-order interference"
    "Normalized real target; coherently superpose XZ and ZX; dephase order control with strength p"
    orderClaim "Gate-specific calibration. A known-gate fixed-order circuit can imitate this statistic; not a causal-nonseparability or friend-order witness.",
  extension "P07" "Controlled-phase product-state test"
    "Pure real two-qubit amplitudes; coherent CZ applied to |++>"
    mediatorClaim "Pure-state calculation; requires purity and state reconstruction. No gravity model, coupling scale, mixed-state separability theorem, or generic classical-mediator exclusion.",
  extension "P08" "Classical query-budget recovery"
    "Two fair bits; at most one classical bit query; arbitrary randomized response and query choice"
    queryClaim "A small exact algorithm-class obstruction, not an asymptotic complexity result or a bound on coherent quantum queries.",
  extension "P10" "Public agreement composition"
    "A single joint distribution over three public binary records A,B,C"
    agreementClaim "Does not compose inaccessible observer-relative records; the common joint distribution is an explicit premise."
]

/-- Every former placeholder has a concrete checked subproblem. -/
noncomputable def extensionFor (s : Scenario) : Option ExtensionInfo :=
  extensions.find? fun e => e.scenario == s.id

end OntologySeparation.Catalog
