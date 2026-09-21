import OntologySeparation.Operational.Bell
import OntologySeparation.Operational.FriendRecords
import OntologySeparation.Core.ProfileRules
namespace OntologySeparation.OperationalProfiles
def BellSupported (p : AssumptionProfile) : Prop :=
  p.Extends OperationalBell.screeningOffProfile ∨ p.Extends OperationalBell.jointProfile
instance (p : AssumptionProfile) : Decidable (BellSupported p) := inferInstanceAs (Decidable (_ ∨ _))
theorem bell_bound {Λ : Type} [Fintype Λ] (p : AssumptionProfile)
    (supported : BellSupported p) (m : OperationalBell.Model Λ)
    (assumptions : p.Satisfied OperationalBell.vocabulary m) : Bell.score m.behavior ≤ 2 := by
  rcases supported with h | h
  · exact (OperationalBell.certified.under p h).valid m assumptions
  · exact (OperationalBell.jointCertified.under p h).valid m assumptions
theorem lf_bound {Λ : Type} [Fintype Λ] (p : AssumptionProfile)
    (supported : p.Extends FriendRecords.profile) (m : FriendRecords.Model Λ)
    (assumptions : p.Satisfied FriendRecords.vocabulary m) : RealQuantum.genuineLF m.behavior ≤ 6 :=
  (FriendRecords.certified.under p supported).valid m assumptions
theorem bell_supported_count : (binaryProfiles.filter fun p => decide (BellSupported p)).length = 9 := by decide
theorem lf_supported_count : (binaryProfiles.filter fun p => decide (p.Extends FriendRecords.profile)).length = 2 := by decide
/-- Coverage, not realizability or experimental exclusion. -/
def rows : Lean.Json := Lean.toJson (binaryProfiles.map fun p => Lean.Json.mkObj [
  ("profile", Lean.toJson p), ("bell_bound", Lean.toJson (decide (BellSupported p))),
  ("lf_bound", Lean.toJson (decide (p.Extends FriendRecords.profile)))])
end OntologySeparation.OperationalProfiles
