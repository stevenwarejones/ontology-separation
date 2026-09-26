import OntologySeparation.Experiments.ForcedSignalingTimingExtension
import OntologySeparation.Experiments.ForcedSignalingGeometryRobustness

/-! Citable fixed-frame headline for the restoration layout. The common-law
soundness, realization, collectible lower bound and timing-menu attainment are
bundled without claiming a universal theory for every possible arrangement. -/
namespace OntologySeparation.ForcedSignaling
noncomputable section
open HiddenInfluence VCausal ForcedSignalingLayouts
open ForcedSignalingVCausal ForcedSignalingCollectibility ForcedSignalingTimingExtension

/-- Both delayed branches on the restoration layout receive the other late
party's data through an open hidden cone. -/
def restorationTiming : TimingLayout restoration 10000 where
  blind := restoration_lc4
  delayedC := ⟨lightSpeed/5000000+2,5000⟩
  delayedB := ⟨lightSpeed/5000000+2,-5000⟩
  c_after := by norm_num [lightFuture, restoration, lightSpeed]
  b_after := by norm_num [lightFuture, restoration, lightSpeed]
  bc_connected := by norm_num [precedes, restoration, lightSpeed]
  cb_connected := by norm_num [precedes, restoration, lightSpeed]

/-- Finite classical v-causal protocols, with Bell screening-off and independent
settings, on the fixed-frame restoration geometry: full-behavior soundness,
LC4 realization, forced collectible TV, and an attaining common timing mechanism. -/
theorem physical_main :
    (∀ (Ω : Type) [Fintype Ω] (p : Protocol .aFirst Ω) (e : Early)
      (y z : Bool) (o : VisibleOutcome),
      p.toModel.behavior.prob (e,lateFromBool y z) o.toOutcome = (p.run e y z).mass o) ∧
    (∀ (m : HiddenInfluence.Model) (h : ForcedSignalingTheorem2.MatchesCluster m),
      ∃ p : Protocol .aFirst (EarlyRecord × (Early → Strategy)),
        ObservationallyEquivalent p.toModel.behavior m.behavior) ∧
    (∀ (Ω : Type) [Fintype Ω] (m : VCausal.Model restoration 10000 .aFirst Ω),
      ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel →
      ∃ c : Context, Collectible (restoration (sender c)) (recipients restoration c) ∧
        (Real.sqrt 2-1)/4 ≤ tv m.toProtocol.toModel.behavior c) ∧
    (∃ (m : VCausal.Model restoration 10000 .aFirst (EarlyRecord × (Early → Strategy)))
      (t : TimingProtocol m.toProtocol),
      ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel ∧
      m.toProtocol.toModel.signaling = (Real.sqrt 2-1)/4 ∧
      (∀ e y z o, (t.runC e y z).mass o = (LC4FullDistribution.quantum e y z).mass o) ∧
      (∀ e y z o, (t.runB e y z).mass o = (LC4FullDistribution.quantum e y z).mass o)) := by
  refine ⟨fun _ _ p e y z o => p.full_behavior e y z o, ?_, ?_, ?_⟩
  · intro m h
    exact ⟨realizeLC4 m h .aFirst, realizeLC4_behavior m h .aFirst⟩
  · intro Ω _ m h
    exact vcausal_forced_superluminal_signal m h restoration_both_collectible
  · exact attaining_timing_extension restorationTiming restoration_order

end
end OntologySeparation.ForcedSignaling
