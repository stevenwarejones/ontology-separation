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
    have hl := hm .leftFalse (by simp [core])
    have hr := hm .rightFalse (by simp [core])
    rcases ht with ht | ht
    · exact (by simpa [holds] using hl) ht
    · exact (by simpa [holds] using hr) ht
  deletionAdversary := by
    intro law hlaw
    cases law with
    | leftFalse =>
        refine ⟨(true, false), ?_, Or.inl rfl⟩
        intro kept hkept
        simp [core] at hkept
        simpa [holds] using hkept
    | rightFalse =>
        refine ⟨(false, true), ?_, Or.inr rfl⟩
        intro kept hkept
        simp [core] at hkept
        simpa [holds] using hkept

example :
    ¬ (∀ m, Satisfies holds (core.erase DemoLaw.leftFalse) m → ¬ target m) :=
  certificate.erase_not_excluding (by simp [core])

end OntologySeparation.Tests.AdversarySearch
