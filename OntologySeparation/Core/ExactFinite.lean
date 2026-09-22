import OntologySeparation.Core.Comparison
import Mathlib.Tactic

/-! Exact rational prediction semantics for finite-comparison backends.

This layer does not choose a finite domain or claim coverage. It only ties an
executable rational probability function to the common normalized Behavior
semantics used by ExperimentAccess. -/
namespace OntologySeparation.ExactFinite

open ExperimentAccess
open Comparison

variable {P M : Type} {E : Interface}

/-- A backend may participate in automatic exact comparison only when every
reported rational probability is proved equal to the supplied common Behavior
semantics. The possibly noncomputable prediction semantics are a parameter, not
runtime evaluator data. -/
structure Backend (predict : Predictions M P E) where
  probability : M → P → E.Setting → E.Outcome → ℚ
  correct : ∀ m p s o, (predict m p).prob s o = (probability m p s o : ℝ)

/-- Rational equality over an explicitly stated access domain. This is the
computable proposition a finite checker will decide. -/
def EquivalentQ {predict : Predictions M P E} (backend : Backend predict)
    (allowed : P → Prop) (a b : M) : Prop :=
  ∀ p, allowed p → ∀ s o, backend.probability a p s o = backend.probability b p s o

theorem equivalent_of_exact
    {predict : Predictions M P E} (backend : Backend predict)
    (allowed : P → Prop) (a b : M)
    (h : EquivalentQ backend allowed a b) :
    Equivalent predict allowed a b := by
  intro p hp s o
  rw [backend.correct, backend.correct]
  exact_mod_cast h p hp s o

theorem exact_of_equivalent
    {predict : Predictions M P E} (backend : Backend predict)
    (allowed : P → Prop) (a b : M)
    (h : Equivalent predict allowed a b) :
    EquivalentQ backend allowed a b := by
  intro p hp s o
  have he := h p hp s o
  rw [backend.correct, backend.correct] at he
  exact_mod_cast he

theorem equivalent_iff_exact
    {predict : Predictions M P E} (backend : Backend predict)
    (allowed : P → Prop) (a b : M) :
    Equivalent predict allowed a b ↔ EquivalentQ backend allowed a b :=
  ⟨exact_of_equivalent backend allowed a b, equivalent_of_exact backend allowed a b⟩

/-- A checked rational-equality proof becomes the existing domain-agreement
certificate; no new reporting vocabulary is introduced. -/
def domainAgreementOfExact
    {predict : Predictions M P E} (backend : Backend predict)
    (allowed : P → Prop) (a b : M)
    (h : EquivalentQ backend allowed a b) :
    DomainAgreement predict allowed a b :=
  ⟨equivalent_of_exact backend allowed a b h⟩

end OntologySeparation.ExactFinite
