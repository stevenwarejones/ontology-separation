import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Experiments.Bell

/-! A score-level adversary benchmark for the logical hinge used by
Operational/Noncontextual Friendliness.

This is deliberately narrower than the full extended-Wigner-friend construction:
absoluteEvents is represented by a Fine/CHSH-compatible global event table and
operationalAgency by equality between that latent table and the public table.
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
  public : Behavior Bell.interface
  latent : Behavior Bell.interface

def Holds : Law → Model → Prop
  | .absoluteEvents, m => Bell.localTheory m.latent
  | .operationalAgency, m => m.public = m.latent

def Target (m : Model) : Prop := m.public = Bell.singletBehavior

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
  public := Bell.singletBehavior
  latent := Bell.singletBehavior

def dropAgency : Model where
  public := Bell.singletBehavior
  latent := constantBehavior

theorem dropAbsolute_not_absolute :
    ¬ Holds .absoluteEvents dropAbsolute := by
  simpa [Holds, dropAbsolute] using Bell.quantumSeparation.excludes

theorem dropAgency_not_agency :
    ¬ Holds .operationalAgency dropAgency := by
  intro h
  have hs : Bell.score Bell.singletBehavior = Bell.score constantBehavior :=
    congrArg Bell.score h
  rw [Bell.singlet_score] at hs
  have hc := Bell.localBound.valid constantBehavior constant_local
  rw [← hs] at hc
  norm_num at hc

/-- The two benchmark premises form a deletion-minimal core for excluding the
chosen exact quantum behavior in this reduced representation. -/
def certificate : MinimalCore Holds Target core where
  excludes := by
    intro m hm ht
    have ha := hm .absoluteEvents (by simp [core])
    have hg := hm .operationalAgency (by simp [core])
    unfold Holds at ha hg
    unfold Target at ht
    rw [← hg, ht] at ha
    exact Bell.quantumSeparation.excludes ha
  deletionAdversary := by
    intro law hlaw
    cases law with
    | absoluteEvents =>
        refine ⟨dropAbsolute, ?_, rfl⟩
        intro kept hkept
        have hk : kept = Law.operationalAgency := by
          simpa [core] using hkept
        subst kept
        rfl
    | operationalAgency =>
        refine ⟨dropAgency, ?_, rfl⟩
        intro kept hkept
        have hk : kept = Law.absoluteEvents := by
          simpa [core] using hkept
        subst kept
        exact constant_local

theorem exact_core :
    (∀ m, Satisfies Holds core m → ¬ Target m) ∧
    (∀ law, law ∈ core →
      ∃ m, Satisfies Holds (core.erase law) m ∧ Target m) :=
  ⟨certificate.excludes, certificate.deletionAdversary⟩

end
end OntologySeparation.OperationalFriendlinessBenchmark
