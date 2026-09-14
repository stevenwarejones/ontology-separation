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

/-- The executable's theorem reference is exactly the resolved proof's reference. -/
theorem claim_reference_consistent (id : ClaimId) :
    (resolve id).declaration = id.declaration := by
  cases id <;> rfl

end OntologySeparation.Catalog
