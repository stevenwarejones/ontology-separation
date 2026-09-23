import Mathlib.Data.Finset.Basic

/-! A small proof-bearing language for structured adversary searches.

A no-go core is scientifically stronger than a universal exclusion alone when every
named premise is challenged by an explicit deletion adversary. The search procedure
that proposes candidate cores may be external; this file only certifies the returned
core and its countermodels. -/
namespace OntologySeparation.AdversarySearch

variable {Law Model : Type} [DecidableEq Law]

/-- A model satisfies every law selected by a finite assumption core. -/
def Satisfies (holds : Law → Model → Prop) (core : Finset Law) (m : Model) : Prop :=
  ∀ law ∈ core, holds law m

theorem satisfies_mono (holds : Law → Model → Prop) {weak strong : Finset Law}
    (hsub : weak ⊆ strong) {m : Model} (hm : Satisfies holds strong m) :
    Satisfies holds weak m := by
  intro law hlaw
  exact hm law (hsub hlaw)

/-- A checked exclusion together with one countermodel for deleting each premise.

The deletion adversaries establish premise-by-premise necessity only inside the stated
model language; they do not prove philosophical necessity outside that language. -/
structure MinimalCore (holds : Law → Model → Prop) (target : Model → Prop)
    (core : Finset Law) where
  excludes : ∀ m, Satisfies holds core m → ¬ target m
  deletionAdversary :
    ∀ law, law ∈ core →
      ∃ m, Satisfies holds (core.erase law) m ∧ target m

namespace MinimalCore

variable {holds : Law → Model → Prop} {target : Model → Prop} {core : Finset Law}

/-- Every member of a certified core has an explicit target-realizing adversary when
that one law is removed. -/
theorem deletion_necessary (c : MinimalCore holds target core) {law : Law}
    (hlaw : law ∈ core) :
    ∃ m, Satisfies holds (core.erase law) m ∧ target m :=
  c.deletionAdversary law hlaw

/-- No proper one-law deletion can inherit the certified exclusion. -/
theorem erase_not_excluding (c : MinimalCore holds target core) {law : Law}
    (hlaw : law ∈ core) :
    ¬ (∀ m, Satisfies holds (core.erase law) m → ¬ target m) := by
  intro h
  obtain ⟨m, hm, ht⟩ := c.deletionAdversary law hlaw
  exact h m hm ht

end MinimalCore

/-- Classification used by research reports before any novelty claim is made. -/
inductive NoveltyStatus where
  | reproduction
  | extension
  | candidateNewCore
  deriving Repr, BEq, DecidableEq

end OntologySeparation.AdversarySearch
