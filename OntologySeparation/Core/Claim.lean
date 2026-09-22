import OntologySeparation.Core.Certified
import OntologySeparation.Core.ExperimentAccess
import Mathlib.Data.Rat.Cast.Defs

/-! One evidence contract for all numerical and theorem reports. Constructors carry
proofs of their exact values; a result category cannot be supplied independently. -/
namespace OntologySeparation
inductive Claim : Type 1 where
  | exact (expression : ℝ) (value : ℚ) (correct : expression = (value : ℝ))
  | bound {M : Type} (admissible : M → Prop) (score : M → ℝ) (ceiling : ℚ)
      (valid : ∀ m, admissible m → score m ≤ (ceiling : ℝ))
  | realizedBound {M : Type} (admissible : M → Prop) (score : M → ℝ) (ceiling : ℚ)
      (valid : ∀ m, admissible m → score m ≤ (ceiling : ℝ))
      (model : M) (satisfies : admissible model)
  | witness {M : Type} (admissible : M → Prop) (score : M → ℝ) (model : M)
      (satisfies : admissible model) (value : ℚ) (correct : score model = (value : ℝ))
  | exclusion {M : Type} (admissible : M → Prop) (model : M) (excluded : ¬ admissible model)
  | agreement {P M : Type} {E : Interface}
      (predict : ExperimentAccess.Predictions M P E) (allowed : P → Prop) (a b : M)
      (proof : ExperimentAccess.Equivalent predict allowed a b)
  | separation {P M : Type} {E : Interface}
      (predict : ExperimentAccess.Predictions M P E) (allowed : P → Prop) (a b : M)
      (witness : ExperimentAccess.Separator predict allowed a b)
  | theoremResult (statement : Prop) (proof : statement)

/-- The proposition displayed by the exporter is derived from the claim, never entered as text. -/
def Claim.statement : Claim → Prop
  | .exact x v _ => x = (v : ℝ)
  | .bound a s v _ => ∀ m, a m → s m ≤ (v : ℝ)
  | .realizedBound a s v _ _ _ => (∀ m, a m → s m ≤ (v : ℝ)) ∧ ∃ m, a m
  | .witness a s _ _ v _ => ∃ m, a m ∧ s m = (v : ℝ)
  | .exclusion a m _ => ¬ a m
  | .agreement predict allowed a b _ => ExperimentAccess.Equivalent predict allowed a b
  | .separation predict allowed a b w =>
      (¬ ExperimentAccess.Equivalent predict allowed a b) ∧
      allowed w.protocol ∧ 0 < w.gap ∧
      (predict a w.protocol).prob w.setting w.outcome -
        (predict b w.protocol).prob w.setting w.outcome = w.gap
  | .theoremResult p _ => p

theorem Claim.sound (c : Claim) : c.statement := by
  cases c with
  | exact _ _ h => exact h
  | bound _ _ _ h => exact h
  | realizedBound _ _ _ h m hm => exact ⟨h, m, hm⟩
  | witness _ _ m hm _ h => exact ⟨m, hm, h⟩
  | exclusion _ _ h => exact h
  | agreement _ _ _ _ h => exact h
  | separation _ _ _ _ w =>
      exact ⟨w.not_equivalent, w.accessible, w.positive, w.difference⟩
  | theoremResult _ h => exact h

/-- Rendering metadata follows the constructor; there is no independent status argument. -/
def Claim.kind : Claim → String
  | .exact .. => "exact"
  | .bound .. => "bound"
  | .realizedBound .. => "realizedBound"
  | .witness .. => "witness"
  | .exclusion .. => "exclusion"
  | .agreement .. => "agreement"
  | .separation .. => "separation"
  | .theoremResult .. => "theorem"
def Claim.quantity : Claim → Option ℚ
  | .exact _ v _ => some v
  | .bound _ _ v _ => some v
  | .realizedBound _ _ v _ _ _ => some v
  | .witness _ _ _ _ v _ => some v
  | _ => none
end OntologySeparation
