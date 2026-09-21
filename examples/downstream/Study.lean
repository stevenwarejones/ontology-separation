import OntologySeparation.Operational.ClassicalWorld
import OntologySeparation.Core.Claim

/-! Extend the general framework with a Bell law package. Unlike qubit recipes,
this proves a bound for a class of hidden-state models, not one probability. -/
namespace MyLaboratory
open OntologySeparation
noncomputable section

def admissible (m : OperationalBell.Model Unit) : Prop :=
  OperationalBell.screeningOffProfile.Satisfied OperationalBell.vocabulary m

def bellBound : Claim := .realizedBound admissible (fun m => Bell.score m.behavior) 2
  (fun m h => OperationalBell.certified.valid m h)
  ClassicalWorld.constantWorld.operational ClassicalWorld.realizedBound.satisfies

-- Exclusion uses the same class definition and the actual calculated singlet behavior.
def singletExcluded : Claim := .exclusion
  (profileTheory (OperationalBell.vocabulary (Λ := Unit))
    OperationalBell.screeningOffProfile OperationalBell.Model.behavior)
  Bell.singletBehavior OperationalBell.singlet_excludes
end
end MyLaboratory
