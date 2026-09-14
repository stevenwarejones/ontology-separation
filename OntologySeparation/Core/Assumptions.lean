import Lean

/-! Explicit physical-law profiles. Rejecting a law means its negation, whereas
leaving it unspecified adds no condition. No philosophical label fixes a predicate. -/
namespace OntologySeparation

inductive Stance where
  | require
  | reject
  | unspecified
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

/-- Operational vocabulary selected by the model author. `measurementIndependent`
is the statistical condition sometimes motivated by free experimental choice. -/
structure Vocabulary (Model : Type) where
  realism : Model → Prop
  globalTruth : Model → Prop
  locality : Model → Prop
  measurementIndependent : Model → Prop

structure AssumptionProfile where
  realism : Stance := .unspecified
  globalTruth : Stance := .unspecified
  locality : Stance := .unspecified
  measurementIndependent : Stance := .unspecified
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

def Stance.Holds : Stance → Prop → Prop
  | .require, p => p
  | .reject, p => ¬ p
  | .unspecified, _ => True

def AssumptionProfile.Satisfied {M : Type} (p : AssumptionProfile)
    (v : Vocabulary M) (m : M) : Prop :=
  p.realism.Holds (v.realism m) ∧ p.globalTruth.Holds (v.globalTruth m) ∧
  p.locality.Holds (v.locality m) ∧
  p.measurementIndependent.Holds (v.measurementIndependent m)

/-- Existence is a separate proof obligation, never inferred from a profile's syntax. -/
def AssumptionProfile.Realizable {M : Type} (p : AssumptionProfile)
    (v : Vocabulary M) : Prop := ∃ m, p.Satisfied v m

/-- All sixteen fully specified binary profiles, without asserting any is realizable. -/
def binaryProfiles : List AssumptionProfile :=
  [Stance.require, .reject].flatMap fun r =>
  [Stance.require, .reject].flatMap fun g =>
  [Stance.require, .reject].flatMap fun l =>
  [Stance.require, .reject].map fun f => ⟨r,g,l,f⟩

theorem binaryProfiles_count : binaryProfiles.length = 16 := by decide

theorem rejection_is_negation (p : Prop) : Stance.reject.Holds p ↔ ¬p := Iff.rfl

theorem unspecified_is_unconstrained (p : Prop) : Stance.unspecified.Holds p := True.intro

/-- If a vocabulary entails global truth from realism, a conflicting profile is empty.
This implication is an explicit hypothesis, not imposed on every definition of realism. -/
theorem inconsistent_profile {M : Type} (v : Vocabulary M)
    (h : ∀ m, v.realism m → v.globalTruth m) :
    ¬ (AssumptionProfile.mk .require .reject .unspecified .unspecified).Realizable v := by
  intro hex
  obtain ⟨m, hm⟩ := hex
  exact hm.2.1 (h m hm.1)

end OntologySeparation
