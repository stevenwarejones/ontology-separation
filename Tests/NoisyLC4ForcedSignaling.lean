import OntologySeparation.Experiments.NoisyLC4ForcedSignaling

namespace Tests.NoisyLC4ForcedSignaling
open OntologySeparation
open OntologySeparation.HiddenInfluence
open OntologySeparation.NoisyLC4

example : 0 < thresholdVisibility := thresholdVisibility_pos
example : thresholdVisibility < 1 := thresholdVisibility_lt_one
example : Threshold.model.signaling = 0 := Threshold.signaling_zero
example : White.model.signaling = 0 := White.signaling_zero

example {p : ℝ} {m : Model} (h : MatchesNoisyCluster p m) :
    sigma p ≤ m.signaling :=
  lower_bound h

example : sigma 0 = 0 := sigma_at_zero
example : sigma 1 = (Real.sqrt 2 - 1) / 4 := sigma_at_one


example (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ m : Model, MatchesNoisyCluster p m → sigma p ≤ m.signaling) ∧
      ∃ m : Model, MatchesNoisyCluster p m ∧ m.signaling = sigma p :=
  exact_curve p hp0 hp1

example : sigma (9/10) = (9 * Real.sqrt 2 - 12) / 40 :=
  sigma_ninety_percent

example : sigma (19/20) = (19 * Real.sqrt 2 - 22) / 80 :=
  sigma_ninetyfive_percent


example (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ (Ω : Type) [Fintype Ω] (m : StochasticModel Ω),
      StochasticMatchesNoisyCluster p m → sigma p ≤ m.signaling) ∧
      ∃ m : StochasticModel Strategy,
        StochasticMatchesNoisyCluster p m ∧ m.signaling = sigma p :=
  exact_curve_stochastic p hp0 hp1

end Tests.NoisyLC4ForcedSignaling
