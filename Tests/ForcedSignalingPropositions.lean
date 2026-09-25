import OntologySeparation.Experiments.ForcedSignalingDirectional

namespace Tests.ForcedSignalingPropositions
open OntologySeparation
open OntologySeparation.HiddenInfluence
open OntologySeparation.ForcedSignalingDirectional

example (m : Model) :
    m.signaling = max (deltaA m) (deltaD m) :=
  signaling_eq_max m

example (m : Model) :
    score m.behavior ≤ 6 + 4 * deltaA m + 4 * deltaD m :=
  directional_bound m

example {m : Model} (h : OntologySeparation.ForcedSignalingTheorem2.MatchesCluster m) :
    (Real.sqrt 2 - 1) / 2 ≤ deltaA m + deltaD m :=
  lc4_directional_lower_bound h

end Tests.ForcedSignalingPropositions
