import OntologySeparation.Core.AdversarySearch

namespace OntologySeparation.Tests.AdversarySearch
open OntologySeparation.AdversarySearch

inductive DemoLaw where
  | leftFalse
  | rightFalse
  deriving DecidableEq

def holds : DemoLaw → (Bool × Bool) → Prop
  | .leftFalse, m => m.1 = false
  | .rightFalse, m => m.2 = false

def target (m : Bool × Bool) : Prop := m.1 = true ∨ m.2 = true

def core : Finset DemoLaw := {.leftFalse, .rightFalse}

def certificate : MinimalCore holds target core where
  excludes := by
    intro m hm ht
    have hleftMem : DemoLaw.leftFalse ∈ core := by simp [core]
    have hrightMem : DemoLaw.rightFalse ∈ core := by simp [core]
    have hl : m.1 = false := hm .leftFalse hleftMem
    have hr : m.2 = false := hm .rightFalse hrightMem
    rcases ht with ht | ht
    · simp [hl] at ht
    · simp [hr] at ht
  deletionAdversary := by
    intro law hlaw
    cases law with
    | leftFalse =>
        refine ⟨(true, false), ?_, Or.inl rfl⟩
        intro kept hkept
        cases kept with
        | leftFalse => simp [core] at hkept
        | rightFalse => rfl
    | rightFalse =>
        refine ⟨(false, true), ?_, Or.inr rfl⟩
        intro kept hkept
        cases kept with
        | leftFalse => rfl
        | rightFalse => simp [core] at hkept

example :
    ¬ (∀ m, Satisfies holds (core.erase DemoLaw.leftFalse) m → ¬ target m) :=
  certificate.erase_not_excluding (by simp [core])

end OntologySeparation.Tests.AdversarySearch
