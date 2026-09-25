import OntologySeparation.Experiments.ForcedSignalingPropositions

namespace Tests.ForcedSignalingPropositions
open OntologySeparation
open OntologySeparation.HiddenInfluence
open OntologySeparation.ForcedSignalingDirectional
open OntologySeparation.ForcedSignalingPropositionWitnesses
open OntologySeparation.ForcedSignalingPropositions

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


example :
    deltaA DirectionalA.model = (Real.sqrt 2 - 1) / 2 ∧
      deltaD DirectionalA.model = 0 := by
  rw [DirectionalA.deltaA_exact, DirectionalA.deltaD_exact, DirectionalA.delta_value]

example :
    deltaA DirectionalD.model = 0 ∧
      deltaD DirectionalD.model = (Real.sqrt 2 - 1) / 2 := by
  rw [DirectionalD.deltaA_exact, DirectionalD.deltaD_exact, DirectionalD.delta_value]

example : OntologySeparation.ForcedSignalingTheorem2.MatchesCluster InvisibleBalanced.model :=
  InvisibleBalanced.matches

example (s : Fin 6) (w y z : Bool) (o : Fin 4) :
    OntologySeparation.ForcedSignalingCertificateModel.marginal4
        InvisibleBalanced.model.behavior
        (OntologySeparation.ForcedSignalingLC4Witness.earlyOf false w)
        (OntologySeparation.ForcedSignalingLC4Witness.lateOf y z)
        (OntologySeparation.ForcedSignalingCertificateModel.projectAProper s) o =
      OntologySeparation.ForcedSignalingCertificateModel.marginal4
        InvisibleBalanced.model.behavior
        (OntologySeparation.ForcedSignalingLC4Witness.earlyOf true w)
        (OntologySeparation.ForcedSignalingLC4Witness.lateOf y z)
        (OntologySeparation.ForcedSignalingCertificateModel.projectAProper s) o :=
  InvisibleBalanced.properA_nonsignaling s w y z o

example :
    deltaA InvisibleBalanced.model = (Real.sqrt 2 - 1) / 4 ∧
      deltaD InvisibleBalanced.model = (Real.sqrt 2 - 1) / 4 := by
  rw [InvisibleBalanced.deltaA_exact, InvisibleBalanced.deltaD_exact,
    InvisibleBalanced.delta_value]

example (c : Context) (o : Recipient) :
    difference InvisibleBalanced.model.behavior c o =
      (InvisibleBalanced.paritySign o : ℝ) *
        difference InvisibleBalanced.model.behavior c 0 :=
  InvisibleBalanced.triple_difference_parity c o


example :
    (∀ m : Model,
      OntologySeparation.ForcedSignalingTheorem2.MatchesCluster m →
      PairwiseInvisible m →
      (Real.sqrt 2 - 1) / 2 ≤ deltaA m + deltaD m) ∧
    ∃ m : Model,
      OntologySeparation.ForcedSignalingTheorem2.MatchesCluster m ∧
      PairwiseInvisible m ∧
      deltaA m + deltaD m = (Real.sqrt 2 - 1) / 2 :=
  pairwise_invisible_optimum

example {Ω : Type} [Fintype Ω] (m : StochasticModel Ω) :
    score m.behavior ≤
      6 + 4 * stochasticDeltaA m + 4 * stochasticDeltaD m :=
  stochastic_directional_bound m
