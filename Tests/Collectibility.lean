import OntologySeparation.Experiments.ForcedSignalingTimingExtension
import OntologySeparation.Experiments.ForcedSignalingAccessible
import OntologySeparation.Experiments.ForcedSignalingPinned

open OntologySeparation OntologySeparation.VCausal
open OntologySeparation.HiddenInfluence

example : LC4Layout ForcedSignalingLayouts.minimal 4 := ForcedSignalingLayouts.minimal_lc4
example : ForcedSignalingCollectibility.BothCollectible ForcedSignalingLayouts.restoration :=
  ForcedSignalingCollectibility.restoration_both_collectible

example (R : Finset Event) (h : R.Nonempty) (s : Event) :
    Collectible s R ↔ R.sup' h plus < plus s ∨ R.sup' h minus < minus s :=
  collectible_criterion s R h

example {Ω : Type} [Fintype Ω] (p : Protocol .aFirst Ω)
    (t : TimingProtocol p) (e : Early) (y z : Bool) (r : Triple) :
    recordProb (t.runC e y z) abdRecord r = recordProb (p.run e y z) abdRecord r :=
  t.delayC_preserves_ABD e y z r

example {Ω : Type} [Fintype Ω] (p : Protocol .aFirst Ω)
    (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o : VisibleOutcome) :
    (ForcedSignalingTimingExtension.delayC p e y z).mass o =
      (LC4FullDistribution.quantum e y z).mass o :=
  ForcedSignalingTimingExtension.delayC_quantum p h e y z o

example {Ω : Type} [Fintype Ω]
    (m : VCausal.Model ForcedSignalingLayouts.minimal 4 .aFirst Ω)
    (h : ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel) :
    ∃ c : Context,
      Collectible (ForcedSignalingLayouts.minimal (ForcedSignalingCollectibility.sender c))
        (ForcedSignalingCollectibility.recipients ForcedSignalingLayouts.minimal c) ∧
      (Real.sqrt 2 - 1) / 4 ≤ tv m.toProtocol.toModel.behavior c :=
  ForcedSignalingCollectibility.vcausal_forced_superluminal_signal m h
    ForcedSignalingCollectibility.minimal_both_collectible

example {Ω : Type} [Fintype Ω] (p : Protocol .aFirst Ω)
    (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o : VisibleOutcome) :
    ((ForcedSignalingTimingExtension.quantumTiming p).runC e y z).mass o =
      (LC4FullDistribution.quantum e y z).mass o :=
  ForcedSignalingTimingExtension.quantumTiming_runC p h e y z o

private def threeSite : Layout
  | .A | .D => ⟨0,0⟩
  | .B => ⟨1,-2⟩
  | .C => ⟨1,2⟩

open scoped BigOperators
example {Ω : Type} [Fintype Ω] (p : Protocol .disconnected Ω)
    (h : ForcedSignalingTheorem2.MatchesCluster p.toModel) (x y z w : Bool) :
    (1/2 : ℝ) * ∑ r : Party → Bool,
      |recordProb (p.run (ForcedSignalingLC4Witness.earlyOf x w) y z)
          (ForcedSignalingAccessible.setRecord {.B}) r -
        recordProb (p.run (ForcedSignalingLC4Witness.earlyOf false w) y z)
          (ForcedSignalingAccessible.setRecord {.B}) r| = 0 := by
  apply ForcedSignalingAccessible.zero_accessible_A p h threeSite {.B}
    (by simp) (by norm_num [threeSite]) (by norm_num [threeSite])
    (by norm_num [threeSite]) (by norm_num [threeSite]) _ x y z w
  refine ⟨by simp, threeSite .B, ?_, ?_⟩
  · intro r hr
    simpa using (show lightFuture r (threeSite .B) from by
      simp only [Finset.image_singleton, Finset.mem_singleton] at hr
      subst r
      exact lightFuture_refl _)
  · norm_num [threeSite, lightFuture]
