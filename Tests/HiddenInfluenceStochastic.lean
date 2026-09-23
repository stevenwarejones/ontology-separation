import OntologySeparation.Operational.HiddenInfluenceStochastic

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

end Tests.HiddenInfluenceStochastic
