import OntologySeparation.Models.DephasedSinglet
import OntologySeparation.Experiments.Research
import OntologySeparation.Adapters.Shared
import OntologySeparation.Core.Exclusion
import OntologySeparation.Experiments.Bell
import OntologySeparation.Experiments.LocalFriendliness
import OntologySeparation.Models.Memory
import OntologySeparation.Runtime.Claims

/-! Reportable claims carry Lean proofs. The UI text is explanatory; each named
`declaration` below is an actual theorem whose statement can be inspected in Lean. -/
namespace OntologySeparation.Catalog

structure VerifiedClaim where
  declaration : String
  proposition : Prop
  proof : proposition

theorem bellQuantumEvidence :
    Bell.score Bell.singletBehavior = 1502/625 ∧ ¬ Bell.localTheory Bell.singletBehavior :=
  ⟨Bell.singlet_score, Bell.quantumSeparation.excludes⟩

theorem bellPREvidence :
    QIT.Bell.CHSH.value QIT.Bell.CHSH.prBox = 4 ∧
      ¬ Bell.localTheory Bell.prWitness.behavior :=
  ⟨QIT.Bell.CHSH.value_prBox, Bell.local_vs_noSignaling.excludes⟩

theorem lfBoundEvidence (p : Behavior LF.interface) (h : LF.theory p) :
    RealQuantum.genuineLF p ≤ 6 := LF.genuineBound.valid p h

theorem lfQuantumEvidence :
    RealQuantum.genuineLF RealQuantum.lfBehavior = 1214656/180625 ∧
      ¬ LF.theory RealQuantum.lfBehavior :=
  ⟨RealQuantum.lfBehavior_value, LF.quantumSeparation.excludes⟩

def bellLocalClaim : VerifiedClaim :=
  ⟨"QIT.Bell.CHSH.value_le_two_of_isLocal", _, QIT.Bell.CHSH.value_le_two_of_isLocal⟩
def bellQuantumClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Catalog.bellQuantumEvidence", _, bellQuantumEvidence⟩
def bellPRClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Catalog.bellPREvidence", _, bellPREvidence⟩
def lfBoundClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Catalog.lfBoundEvidence", _, lfBoundEvidence⟩
def lfQuantumClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Catalog.lfQuantumEvidence", _, lfQuantumEvidence⟩
def lfControlClaim : VerifiedClaim :=
  ⟨"OntologySeparation.LF.exists_bell_violation_within_LF", _, LF.exists_bell_violation_within_LF⟩
def echoClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Memory.echo_probability", _, Memory.echo_probability⟩
def leakClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Memory.leakedEcho_probability", _, Memory.leakedEcho_probability⟩
def phaseClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Memory.phaseEcho_probability", _, Memory.phaseEcho_probability⟩

def triangleClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.no_pairwise_gluing", _, Research.no_pairwise_gluing⟩
def recoveryClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.restricted_recovery", _, Research.restricted_recovery⟩
def jointRecoveryClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.joint_recovery", _, Research.joint_recovery⟩
def relabelClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.passive_relabel", _, Research.passive_relabel⟩
def queryClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.random_query_bound", _, Research.random_query_bound⟩
def orderClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.noisy_order_probability", _, Research.noisy_order_probability⟩
def mediatorClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.phase_state_not_complex_product", _, Research.phase_state_not_complex_product⟩
def agreementClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Research.public_error_bound", _, Research.public_error_bound⟩
def contaminationClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Shared.LF_contamination_required", _, Shared.LF_contamination_required⟩
def localThreeClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Shared.local_three_LF_bound", _, @Shared.local_three_LF_bound⟩
def innerPRClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Shared.lf_inner_PR", _, Shared.lf_inner_PR⟩
def singletNSClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Shared.singlet_noSignaling", _, @Shared.singlet_noSignaling⟩
def freeExtensionClaim : VerifiedClaim :=
  ⟨"OntologySeparation.independent_sector_underdetermined", _, @independent_sector_underdetermined.{0,0}⟩
def exclusionClaim : VerifiedClaim :=
  ⟨"OntologySeparation.ProfileBridge.excludes", _, @ProfileBridge.excludes.{0,0}⟩

def nsLFClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Shared.LF_ns_sharp", _, Shared.LF_ns_sharp⟩

def noisyBellClaim : VerifiedClaim :=
  ⟨"OntologySeparation.DephasedSinglet.bell_score", _, DephasedSinglet.bell_score⟩
def noisyLFClaim : VerifiedClaim :=
  ⟨"OntologySeparation.DephasedSinglet.LF_score", _, DephasedSinglet.LF_score⟩

def nsFractionClaim : VerifiedClaim :=
  ⟨"OntologySeparation.Shared.LF_NS_fraction_required", _, Shared.LF_NS_fraction_required⟩

/-- Exhaustive proof resolver: adding an executable claim requires a new proof case. -/
def resolve : ClaimId → VerifiedClaim
  | .bellLocal => bellLocalClaim
  | .bellQuantum => bellQuantumClaim
  | .bellPR => bellPRClaim
  | .lfBound => lfBoundClaim
  | .lfQuantum => lfQuantumClaim
  | .lfControl => lfControlClaim
  | .echo => echoClaim
  | .leak => leakClaim
  | .phase => phaseClaim

  | .nsFraction => nsFractionClaim
  | .noisyBell => noisyBellClaim
  | .noisyLF => noisyLFClaim
  | .nsLF => nsLFClaim
  | .triangle => triangleClaim
  | .recovery => recoveryClaim
  | .jointRecovery => jointRecoveryClaim
  | .relabel => relabelClaim
  | .query => queryClaim
  | .order => orderClaim
  | .mediator => mediatorClaim
  | .agreement => agreementClaim
  | .contamination => contaminationClaim
  | .localThree => localThreeClaim
  | .innerPR => innerPRClaim
  | .singletNS => singletNSClaim
  | .freeExtension => freeExtensionClaim
  | .exclusion => exclusionClaim

/-- The executable's theorem reference is exactly the resolved proof's reference. -/
theorem claim_reference_consistent (id : ClaimId) :
    (resolve id).declaration = id.declaration := by
  cases id <;> rfl

end OntologySeparation.Catalog
