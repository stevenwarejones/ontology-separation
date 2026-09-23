import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Experiments.PartialLeakage

/-! A structured-adversary benchmark for memory-change awareness.

Baumann and Brukner (Quantum 8, 1481, 2024) show that in an extended Wigner-friend
scenario the effective change of the friend's memory can depend on a distant
observer's setting, and that awareness of this change conflicts with no-signaling.

This file isolates the final operational logic as a deletion-minimal core.  It
does NOT yet derive the remote dependence from a quantum circuit; that bridge is
the next target. -/

namespace OntologySeparation.MemoryAwareness
noncomputable section

open AdversarySearch
open Recipes

/-- Two remote settings determine an objective memory-change rate and the rate
reported by a hypothetical awareness register. -/
structure Model where
  flip : Bool → Rate
  awareness : Bool → Rate

inductive Law where
  | remoteDependentChange
  | faithfulAwareness
  | noSignalingAwareness
  deriving DecidableEq, Repr

def Holds : Law → Model → Prop
  | .remoteDependentChange, m => m.flip false ≠ m.flip true
  | .faithfulAwareness, m => ∀ y, m.awareness y = m.flip y
  | .noSignalingAwareness, m => m.awareness false = m.awareness true

def Target (_ : Model) : Prop := True

def core : Finset Law :=
  {.remoteDependentChange, .faithfulAwareness, .noSignalingAwareness}

theorem core_inconsistent (m : Model)
    (hd : Holds .remoteDependentChange m)
    (hf : Holds .faithfulAwareness m)
    (hns : Holds .noSignalingAwareness m) : False := by
  apply hd
  rw [← hf false, ← hf true]
  exact hns

def noDependenceAdversary : Model where
  flip := fun _ => Rate.of 0
  awareness := fun _ => Rate.of 0

theorem noDependence_faithful :
    Holds .faithfulAwareness noDependenceAdversary := by
  intro y
  rfl

theorem noDependence_nosignaling :
    Holds .noSignalingAwareness noDependenceAdversary := rfl

def unawareAdversary : Model where
  flip := fun y => if y then Rate.of 1 else Rate.of 0
  awareness := fun _ => Rate.of 0

theorem unaware_dependent :
    Holds .remoteDependentChange unawareAdversary := by
  norm_num [Holds, unawareAdversary, Rate.of]

theorem unaware_nosignaling :
    Holds .noSignalingAwareness unawareAdversary := rfl

def signalingAwarenessAdversary : Model where
  flip := fun y => if y then Rate.of 1 else Rate.of 0
  awareness := fun y => if y then Rate.of 1 else Rate.of 0

theorem signalingAwareness_dependent :
    Holds .remoteDependentChange signalingAwarenessAdversary := by
  norm_num [Holds, signalingAwarenessAdversary, Rate.of]

theorem signalingAwareness_faithful :
    Holds .faithfulAwareness signalingAwarenessAdversary := by
  intro y
  rfl

/-- The final operational no-signaling conflict is deletion-minimal: remove any
one of remote dependence, faithful awareness, or no-signaling and a model exists. -/
def certificate : MinimalCore Holds Target core where
  excludes := by
    intro m hm _
    exact core_inconsistent m
      (hm .remoteDependentChange (by simp [core]))
      (hm .faithfulAwareness (by simp [core]))
      (hm .noSignalingAwareness (by simp [core]))
  deletionAdversary := by
    intro law hlaw
    cases law with
    | remoteDependentChange =>
        refine ⟨noDependenceAdversary, ?_, trivial⟩
        intro kept hkept
        have hk : kept = Law.faithfulAwareness ∨ kept = Law.noSignalingAwareness := by
          simp [core] at hkept
          exact hkept
        rcases hk with rfl | rfl
        · exact noDependence_faithful
        · exact noDependence_nosignaling
    | faithfulAwareness =>
        refine ⟨unawareAdversary, ?_, trivial⟩
        intro kept hkept
        have hk : kept = Law.remoteDependentChange ∨ kept = Law.noSignalingAwareness := by
          simp [core] at hkept
          exact hkept
        rcases hk with rfl | rfl
        · exact unaware_dependent
        · exact unaware_nosignaling
    | noSignalingAwareness =>
        refine ⟨signalingAwarenessAdversary, ?_, trivial⟩
        intro kept hkept
        have hk : kept = Law.remoteDependentChange ∨ kept = Law.faithfulAwareness := by
          simp [core] at hkept
          exact hkept
        rcases hk with rfl | rfl
        · exact signalingAwareness_dependent
        · exact signalingAwareness_faithful

theorem memory_awareness_core_minimal :
    (∀ m, Satisfies Holds core m → ¬ Target m) ∧
    (∃ m, Satisfies Holds (core.erase .remoteDependentChange) m ∧ Target m) ∧
    (∃ m, Satisfies Holds (core.erase .faithfulAwareness) m ∧ Target m) ∧
    (∃ m, Satisfies Holds (core.erase .noSignalingAwareness) m ∧ Target m) := by
  refine ⟨certificate.excludes, ?_, ?_, ?_⟩
  · exact certificate.deletionAdversary .remoteDependentChange (by simp [core])
  · exact certificate.deletionAdversary .faithfulAwareness (by simp [core])
  · exact certificate.deletionAdversary .noSignalingAwareness (by simp [core])

end
end OntologySeparation.MemoryAwareness
