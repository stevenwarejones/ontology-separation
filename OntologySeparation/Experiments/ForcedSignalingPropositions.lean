import OntologySeparation.Experiments.ForcedSignalingPropositionWitnesses
import OntologySeparation.Operational.HiddenInfluenceStochastic

/-!
# Forced-signaling Propositions 1 and 2

Public theorem layer over the exact directional and pairwise-invisible
certificates.  The certificate data are ported in
ForcedSignalingPropositionWitnesses; this file states the propositions in
model-level form.
-/

namespace OntologySeparation.ForcedSignalingPropositions
noncomputable section

open HiddenInfluence
open ForcedSignalingDirectional
open ForcedSignalingCertificateModel
open ForcedSignalingPropositionWitnesses

/-- All six one-/two-party recipient projections are blind to A and D setting
changes; B and C cannot signal even to their full complementary triples; and the
A/D full-triple difference is a pure parity shift. -/
structure PairwiseInvisible (m : Model) : Prop where
  properA : ∀ s : Fin 6, ∀ w y z : Bool, ∀ o : Fin 4,
    marginal4 m.behavior
        (ForcedSignalingLC4Witness.earlyOf false w)
        (ForcedSignalingLC4Witness.lateOf y z)
        (projectAProper s) o =
      marginal4 m.behavior
        (ForcedSignalingLC4Witness.earlyOf true w)
        (ForcedSignalingLC4Witness.lateOf y z)
        (projectAProper s) o
  properD : ∀ s : Fin 6, ∀ x y z : Bool, ∀ o : Fin 4,
    marginal4 m.behavior
        (ForcedSignalingLC4Witness.earlyOf x false)
        (ForcedSignalingLC4Witness.lateOf y z)
        (projectDProper s) o =
      marginal4 m.behavior
        (ForcedSignalingLC4Witness.earlyOf x true)
        (ForcedSignalingLC4Witness.lateOf y z)
        (projectDProper s) o
  silentB : ∀ e : Early, ∀ z : Fin 2, ∀ o : Recipient,
    marginal m.behavior e (lateChoice 0 z) recipientB o =
      marginal m.behavior e (lateChoice 1 z) recipientB o
  silentC : ∀ e : Early, ∀ y : Fin 2, ∀ o : Recipient,
    marginal m.behavior e (lateChoice y 0) recipientC o =
      marginal m.behavior e (lateChoice y 1) recipientC o

/-- Proposition 1: directional refinement plus the exact LC4 lower bound. -/
theorem proposition1 :
    (∀ m : Model,
      score m.behavior ≤ 6 + 4 * deltaA m + 4 * deltaD m) ∧
    (∀ m : Model, ForcedSignalingTheorem2.MatchesCluster m →
      (Real.sqrt 2 - 1) / 2 ≤ deltaA m + deltaD m) := by
  exact ⟨directional_bound, fun _ h => lc4_directional_lower_bound h⟩

/-- Proposition 1 one-sided attainment in the A direction, using the exact
directional certificate rather than the Proposition-2 witness. -/
theorem proposition1_A_attains :
    ForcedSignalingTheorem2.MatchesCluster DirectionalA.model ∧
    deltaA DirectionalA.model = (Real.sqrt 2 - 1) / 2 ∧
    deltaD DirectionalA.model = 0 := by
  refine ⟨DirectionalA.matches, ?_, DirectionalA.deltaD_exact⟩
  rw [DirectionalA.deltaA_exact, DirectionalA.delta_value]

/-- Proposition 1 one-sided attainment in the D direction. -/
theorem proposition1_D_attains :
    ForcedSignalingTheorem2.MatchesCluster DirectionalD.model ∧
    deltaA DirectionalD.model = 0 ∧
    deltaD DirectionalD.model = (Real.sqrt 2 - 1) / 2 := by
  refine ⟨DirectionalD.matches, DirectionalD.deltaA_exact, ?_⟩
  rw [DirectionalD.deltaD_exact, DirectionalD.delta_value]

def invisibleA : PairwiseInvisible InvisibleA.model where
  properA := InvisibleA.properA_nonsignaling
  properD := InvisibleA.properD_nonsignaling
  silentB := InvisibleA.B_silent
  silentC := InvisibleA.C_silent

def invisibleD : PairwiseInvisible InvisibleD.model where
  properA := InvisibleD.properA_nonsignaling
  properD := InvisibleD.properD_nonsignaling
  silentB := InvisibleD.B_silent
  silentC := InvisibleD.C_silent

def invisibleBalanced : PairwiseInvisible InvisibleBalanced.model where
  properA := InvisibleBalanced.properA_nonsignaling
  properD := InvisibleBalanced.properD_nonsignaling
  silentB := InvisibleBalanced.B_silent
  silentC := InvisibleBalanced.C_silent

/-- Proposition 2 A-only pairwise-invisible attaining model. -/
theorem proposition2_A :
    ForcedSignalingTheorem2.MatchesCluster InvisibleA.model ∧
    PairwiseInvisible InvisibleA.model ∧
    deltaA InvisibleA.model = (Real.sqrt 2 - 1) / 2 ∧
    deltaD InvisibleA.model = 0 := by
  refine ⟨InvisibleA.matches, invisibleA, ?_, InvisibleA.deltaD_exact⟩
  rw [InvisibleA.deltaA_exact, InvisibleA.delta_value]

/-- Proposition 2 D-only pairwise-invisible attaining model. -/
theorem proposition2_D :
    ForcedSignalingTheorem2.MatchesCluster InvisibleD.model ∧
    PairwiseInvisible InvisibleD.model ∧
    deltaA InvisibleD.model = 0 ∧
    deltaD InvisibleD.model = (Real.sqrt 2 - 1) / 2 := by
  refine ⟨InvisibleD.matches, invisibleD, InvisibleD.deltaA_exact, ?_⟩
  rw [InvisibleD.deltaD_exact, InvisibleD.delta_value]

/-- Proposition 2 balanced pairwise-invisible attaining model. -/
theorem proposition2_balanced :
    ForcedSignalingTheorem2.MatchesCluster InvisibleBalanced.model ∧
    PairwiseInvisible InvisibleBalanced.model ∧
    deltaA InvisibleBalanced.model = (Real.sqrt 2 - 1) / 4 ∧
    deltaD InvisibleBalanced.model = (Real.sqrt 2 - 1) / 4 := by
  refine ⟨InvisibleBalanced.matches, invisibleBalanced, ?_, ?_⟩
  · rw [InvisibleBalanced.deltaA_exact, InvisibleBalanced.delta_value]
  · rw [InvisibleBalanced.deltaD_exact, InvisibleBalanced.delta_value]

/-- The LC4 directional optimum is unchanged when all proper recipient subsets
are required to remain blind: the balanced Proposition-2 model attains the
Proposition-1 lower bound. -/
theorem pairwise_invisible_optimum :
    (∀ m : Model,
      ForcedSignalingTheorem2.MatchesCluster m →
      PairwiseInvisible m →
      (Real.sqrt 2 - 1) / 2 ≤ deltaA m + deltaD m) ∧
    ∃ m : Model,
      ForcedSignalingTheorem2.MatchesCluster m ∧
      PairwiseInvisible m ∧
      deltaA m + deltaD m = (Real.sqrt 2 - 1) / 2 := by
  constructor
  · intro m hm _
    exact lc4_directional_lower_bound hm
  · refine ⟨InvisibleBalanced.model, InvisibleBalanced.matches,
      invisibleBalanced, ?_⟩
    rw [InvisibleBalanced.deltaA_exact, InvisibleBalanced.deltaD_exact,
      InvisibleBalanced.delta_value]
    ring

/-- Directional strengths for a finite stochastic conditional-local model are
those of its proved-equivalent deterministic refinement. -/
noncomputable def stochasticDeltaA {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) : ℝ := deltaA m.determinize

noncomputable def stochasticDeltaD {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) : ℝ := deltaD m.determinize

theorem stochastic_signaling_eq_max {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) :
    m.signaling = max (stochasticDeltaA m) (stochasticDeltaD m) := by
  exact signaling_eq_max m.determinize

theorem stochastic_directional_bound {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) :
    score m.behavior ≤
      6 + 4 * stochasticDeltaA m + 4 * stochasticDeltaD m := by
  exact directional_bound m.determinize

theorem stochastic_lc4_directional_lower_bound
    {Ω : Type} [Fintype Ω] {m : StochasticModel Ω}
    (h : ForcedSignalingTheorem2.StochasticMatchesCluster m) :
    (Real.sqrt 2 - 1) / 2 ≤
      stochasticDeltaA m + stochasticDeltaD m :=
  lc4_directional_lower_bound h.toMatchesCluster

end
end OntologySeparation.ForcedSignalingPropositions
