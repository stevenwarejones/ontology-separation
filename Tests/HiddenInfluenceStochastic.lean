import OntologySeparation.Operational.HiddenInfluenceStochastic
import OntologySeparation.Experiments.ForcedSignalingTheorem2

namespace Tests.HiddenInfluenceStochastic
open OntologySeparation
open OntologySeparation.HiddenInfluence

example (m : Model) :
    ObservationallyEquivalent
      (Model.fromStrategies m.toStrategies).behavior
      m.behavior :=
  m.fromStrategies_toStrategies

example (m : Model) :
    ObservationallyEquivalent
      ((StochasticModel.ofStrategies m.toStrategies).determinize).behavior
      m.behavior :=
  m.stochastic_roundtrip

example {Ω : Type} [Fintype Ω] (m : StochasticModel Ω)
    (e : Early) (y z : Bool) (v : VisibleOutcome) :
    selectedMass (m.toStrategies e) y z v =
      m.factorizedProbability e y z v :=
  m.selected_probability e y z v


example {Ω : Type} [Fintype Ω] (m : StochasticModel Ω)
    (e : Early) (y z : Bool) (v : VisibleOutcome) :
    m.behavior.prob (e, lateFromBool y z) v.toOutcome =
      m.factorizedProbability e y z v :=
  m.behavior_prob_eq_factorized e y z v

example {Ω : Type} [Fintype Ω] (m : StochasticModel Ω) (c : Context) :
    tv m.behavior c = tv m.determinize.behavior c :=
  m.tv_eq_determinize c

example {Ω : Type} [Fintype Ω] (m : StochasticModel Ω) :
    m.signaling = m.determinize.signaling :=
  m.signaling_eq_determinize

example :
    (∀ (Ω : Type) [Fintype Ω] (m : StochasticModel Ω),
      OntologySeparation.ForcedSignalingTheorem2.StochasticMatchesCluster m →
        (Real.sqrt 2 - 1) / 4 ≤ m.signaling) ∧
    ∃ m : StochasticModel Strategy,
      OntologySeparation.ForcedSignalingTheorem2.StochasticMatchesCluster m ∧
        m.signaling = (Real.sqrt 2 - 1) / 4 :=
  OntologySeparation.ForcedSignalingTheorem2.exact_forced_signaling_stochastic_value

end Tests.HiddenInfluenceStochastic
