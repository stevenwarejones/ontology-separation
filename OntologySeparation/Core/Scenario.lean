import OntologySeparation.Core.Certified
import Mathlib.Data.Rat.Cast.Defs

/-! A shared experimental question, explicit interpretations, and exact table cells.
Rational tables are a reporting convenience; arbitrary real results remain available
through Prediction and PredictionFamily. Labels are commentary, not physical laws. -/
namespace OntologySeparation
structure Scenario (Model Protocol : Type) where
  question : Question
  interpret : Model → Protocol → Behavior question.interface
namespace Scenario
variable {M P : Type}
structure ExactPredictions (s : Scenario M P) where
  value : M → P → ℚ
  correct : ∀ m p, s.question.score (s.interpret m p) = (value m p : ℝ)
def ExactPredictions.prediction {s : Scenario M P} (r : ExactPredictions s)
    (m : M) (p : P) : Prediction s.question (s.interpret m p) :=
  ⟨(r.value m p : ℝ), r.correct m p⟩
/-- A selected, nonempty grid; every selected cell has the indexed proof above. -/
structure Comparison (s : Scenario M P) where
  title : String
  description : String
  models : List (String × M)
  protocols : List (String × P)
  models_nonempty : models ≠ []
  protocols_nonempty : protocols ≠ []
  predictions : ExactPredictions s
/-- Default proof automation removes routine nonempty-selection obligations. -/
def Comparison.ofLists {s : Scenario M P} (title description : String)
    (models : List (String × M)) (protocols : List (String × P))
    (predictions : ExactPredictions s) (hm : models ≠ [] := by simp)
    (hp : protocols ≠ [] := by simp) : Comparison s :=
  ⟨title, description, models, protocols, hm, hp, predictions⟩
end Scenario
end OntologySeparation
