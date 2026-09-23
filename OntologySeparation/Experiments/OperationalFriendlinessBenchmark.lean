import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Experiments.Bell

/-! A score-level adversary benchmark for the logical hinge used by
Operational/Noncontextual Friendliness.

This is deliberately narrower than the full extended-Wigner-friend construction:
absoluteEvents is represented by a Fine/CHSH-compatible global event table and
operationalAgency by equality between that latent table and the visible table.
The point is to test the structured-adversary workflow on a known theorem shape,
not to claim a new no-go theorem. -/
namespace OntologySeparation.OperationalFriendlinessBenchmark
noncomputable section
open AdversarySearch

inductive Law where
  | absoluteEvents
  | operationalAgency
  deriving DecidableEq, Repr

structure Model where
  visible : Behavior Bell.interface
  latent : Behavior Bell.interface

def Holds : Law → Model → Prop
  | .absoluteEvents, m => Bell.localTheory m.latent
  | .operationalAgency, m => m.visible = m.latent

def Target (m : Model) : Prop := m.visible = Bell.singletBehavior

def core : Finset Law := {.absoluteEvents, .operationalAgency}

def constantStrategy :
    QIT.Bell.DeterministicStrategy (Fin 2) (Fin 2) Bool Bool :=
  (fun _ => false, fun _ => false)

def constantBehavior : Behavior Bell.interface :=
  Bell.fromQIT (QIT.Bell.deterministicBehavior constantStrategy)

theorem constant_local : Bell.localTheory constantBehavior :=
  ⟨QIT.Bell.deterministicBehavior constantStrategy,
    QIT.Bell.deterministic_isLocal constantStrategy, rfl⟩

def dropAbsolute : Model where
  visible := Bell.singletBehavior
  latent := Bell.singletBehavior

def dropAgency : Model where
  visible := Bell.singletBehavior
  latent := constantBehavior

theorem dropAbsolute_not_absolute :
    ¬ Holds .absoluteEvents dropAbsolute := by
  change ¬ Bell.localTheory Bell.singletBehavior
  exact Bell.quantumSeparation.excludes

theorem dropAgency_not_agency :
    ¬ Holds .operationalAgency dropAgency := by
  intro h
  change Bell.singletBehavior = constantBehavior at h
  have hs : Bell.score Bell.singletBehavior = Bell.score constantBehavior :=
    congrArg Bell.score h
  have hc := Bell.localBound.valid constantBehavior constant_local
  change Bell.score constantBehavior ≤ 2 at hc
  rw [← hs, Bell.singlet_score] at hc
  norm_num at hc

/-- The two benchmark premises form a deletion-minimal core for excluding the
chosen exact quantum behavior in this reduced representation. -/
def certificate : MinimalCore Holds Target core where
  excludes := by
    intro m hm ht
    have hAbsMem : Law.absoluteEvents ∈ core := by simp [core]
    have hAgencyMem : Law.operationalAgency ∈ core := by simp [core]
    have ha := hm .absoluteEvents hAbsMem
    have hg := hm .operationalAgency hAgencyMem
    change Bell.localTheory m.latent at ha
    change m.visible = m.latent at hg
    change m.visible = Bell.singletBehavior at ht
    rw [← hg, ht] at ha
    exact Bell.quantumSeparation.excludes ha
  deletionAdversary := by
    intro law hlaw
    cases law with
    | absoluteEvents =>
        refine ⟨dropAbsolute, ?_, ?_⟩
        · intro kept hkept
          cases kept with
          | absoluteEvents => simp [core] at hkept
          | operationalAgency =>
              change Bell.singletBehavior = Bell.singletBehavior
              rfl
        · change Bell.singletBehavior = Bell.singletBehavior
          rfl
    | operationalAgency =>
        refine ⟨dropAgency, ?_, ?_⟩
        · intro kept hkept
          cases kept with
          | absoluteEvents =>
              change Bell.localTheory constantBehavior
              exact constant_local
          | operationalAgency => simp [core] at hkept
        · change Bell.singletBehavior = Bell.singletBehavior
          rfl

theorem exact_core :
    (∀ m, Satisfies Holds core m → ¬ Target m) ∧
    (∀ law, law ∈ core →
      ∃ m, Satisfies Holds (core.erase law) m ∧ Target m) :=
  ⟨certificate.excludes, certificate.deletionAdversary⟩

end
end OntologySeparation.OperationalFriendlinessBenchmark
