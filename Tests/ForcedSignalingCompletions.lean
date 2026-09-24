import OntologySeparation.Experiments.ForcedSignalingCompletionWitness

namespace Tests.ForcedSignalingCompletions
open OntologySeparation
open OntologySeparation.HiddenInfluence

example : Fintype.card Completion = 512 := completion_count

example :
    ((Finset.univ.filter fun c : Completion => c.slope = 8).card,
     (Finset.univ.filter fun c : Completion => c.slope = 10).card,
     (Finset.univ.filter fun c : Completion => c.slope = 12).card,
     (Finset.univ.filter fun c : Completion => c.slope = 14).card,
     (Finset.univ.filter fun c : Completion => c.slope = 16).card) =
      (64,128,128,128,64) :=
  completion_spectrum

example (m : Model) (c : Completion) (delta : ℝ)
    (h : Within m.behavior delta) :
    completedScore c m.behavior ≤ 6 + (c.slope : ℝ) * delta :=
  completedScore_bound m c delta h

example (c : Completion) :
    Within (CompletionWitness.witness c).behavior (1/16) :=
  CompletionWitness.witness_budget c

example (c : Completion) :
    completedScore c (CompletionWitness.witness c).behavior =
      6 + (c.slope : ℝ) * (1/16) :=
  CompletionWitness.witness_score c

example (c : Completion) :
    (∀ m : Model, ∀ delta : ℝ, Within m.behavior delta →
        completedScore c m.behavior ≤ 6 + (c.slope : ℝ) * delta) ∧
    (∀ k : ℝ,
      (∀ m : Model, Within m.behavior (1/16) →
        completedScore c m.behavior ≤ 6 + k * (1/16)) →
      (c.slope : ℝ) ≤ k) :=
  CompletionWitness.exact_completion_slope c

end Tests.ForcedSignalingCompletions
