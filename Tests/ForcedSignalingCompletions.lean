import OntologySeparation.Experiments.ForcedSignalingCompletions

namespace Tests.ForcedSignalingCompletions
open OntologySeparation
open OntologySeparation.HiddenInfluence
open OntologySeparation.HiddenInfluenceCompletion

example : Fintype.card Completion = 512 :=
  completion_count

example : optimalCompletion.w1 = true := by decide
example : optimalCompletion.w2 = true := by decide
example : optimalCompletion.x5 = true := by decide

/-- The actual all-completions theorem applies to the all-defaults completion. -/
example (K : ℝ) (h : ValidSlope defaultCompletion K) : 8 ≤ K :=
  coefficient_lower_bound_all_completions defaultCompletion K h

/-- The certified K=8 completion is globally slope-optimal. -/
example : ValidSlope optimalCompletion 8 :=
  optimal_completion_globally_sharp.1

/-- Flip all six provably irrelevant raw completion bits while keeping
the same three effective bits. -/
def sameEffectiveVariant : Completion := ⟨511, by norm_num⟩

example : sameEffective optimalCompletion sameEffectiveVariant := by
  decide

/-- Six raw completion bits can change while every conditionally-local score stays equal. -/
example (m : Model) :
    operationalScore optimalCompletion m.behavior =
      operationalScore sameEffectiveVariant m.behavior :=
  score_eq_of_sameEffective (c := optimalCompletion) (d := sameEffectiveVariant) (by decide) m

/-- LC4-matching models have the same exact target score under every completion. -/
example (c : Completion) {m : Model}
    (h : OntologySeparation.ForcedSignalingTheorem2.MatchesCluster m) :
    operationalScore c m.behavior = 4 + 2 * Real.sqrt 2 :=
  operationalScore_of_matchesCluster c h


/-- The all-completions optimum also holds for the finite stochastic class
formalized in #77. -/
example :
    StochasticValidSlope optimalCompletion 8 ∧
      ∀ c : Completion, ∀ K : ℝ, StochasticValidSlope c K → 8 ≤ K :=
  stochastic_completion_globally_sharp

end Tests.ForcedSignalingCompletions
