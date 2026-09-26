import OntologySeparation.Operational.VCausalMeasure
import OntologySeparation.Experiments.ForcedSignalingVCausalCompletions
import OntologySeparation.Experiments.ForcedSignalingCollectibility

/-! General-measure transfer. All probability statements use the full-behavior
compression proved in VCausalMeasure; no finite-support assumption is imposed
on the original hidden law. Stochastic kernels over arbitrary spaces are not
silently identified with deterministic measurable response tables. -/
namespace OntologySeparation.ForcedSignalingMeasures
noncomputable section
open HiddenInfluence VCausal ForcedSignalingVCausal ForcedSignalingCollectibility
open HiddenInfluenceCompletion

structure Model (L : Layout) (v : ℚ) (order : EarlyOrder)
    (Ω : Type*) [MeasurableSpace Ω] extends MeasurableProtocol order Ω where
  layout : LC4Layout L v
  geometry : GeometryOrder L v order

def Model.toFinite {L : Layout} {v : ℚ} {order : EarlyOrder}
    {Ω : Type*} [MeasurableSpace Ω] (m : Model L v order Ω) :
    VCausal.Model L v order ResponseTable where
  toProtocol := m.toMeasurableProtocol.toFinite
  layout := m.layout
  geometry := m.geometry

theorem tradeoff {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) :
    score p.toFinite.toModel.behavior ≤ 6 + 8 * p.toFinite.toModel.signaling :=
  vcausal_tradeoff p.toFinite

theorem lower_bound {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω)
    (h : ForcedSignalingTheorem2.MatchesCluster p.toFinite.toModel) :
    (Real.sqrt 2 - 1) / 4 ≤ p.toFinite.toModel.signaling := by
  rw [← ForcedSignalingTheorem2.targetDelta_value]
  exact ForcedSignalingTheorem2.lower_bound h

theorem noise_lower_bound {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) (visibility : ℝ)
    (h : NoisyLC4.MatchesNoisyCluster visibility p.toFinite.toModel) :
    max 0 ((visibility * (4 + 2 * Real.sqrt 2) - 6) / 8) ≤ p.toFinite.toModel.signaling :=
  vcausal_noise_lower_bound p.toFinite visibility h

def witness {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    Model L v order (EarlyRecord × ResponseTable) where
  toMeasurableProtocol := (witnessOn hL ho).toProtocol.toMeasurable
  layout := hL
  geometry := ho

theorem witness_matches {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    ForcedSignalingTheorem2.MatchesCluster (witness hL ho).toFinite.toProtocol.toModel := by
  change ForcedSignalingTheorem2.MatchesCluster
    (witnessOn hL ho).toProtocol.toMeasurable.toFinite.toModel
  rw [Protocol.toMeasurable_toModel]
  exact witnessOn_matches hL ho

theorem witness_signaling {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    (witness hL ho).toFinite.toProtocol.toModel.signaling = (Real.sqrt 2 - 1) / 4 := by
  change (witnessOn hL ho).toProtocol.toMeasurable.toFinite.toModel.signaling = _
  rw [Protocol.toMeasurable_toModel]
  exact witnessOn_signaling hL ho

/-- Exact minimum over general measurable deterministic-table protocols, with
an explicit attainer obtained by embedding the already certified finite witness. -/
theorem exact_minimum {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    (∀ (Ω : Type) [MeasurableSpace Ω] (m : Model L v order Ω),
      ForcedSignalingTheorem2.MatchesCluster m.toFinite.toProtocol.toModel →
      (Real.sqrt 2 - 1) / 4 ≤ m.toFinite.toProtocol.toModel.signaling) ∧
    ∃ m : Model L v order (EarlyRecord × ResponseTable),
      ForcedSignalingTheorem2.MatchesCluster m.toFinite.toProtocol.toModel ∧
      m.toFinite.toProtocol.toModel.signaling = (Real.sqrt 2 - 1) / 4 := by
  exact ⟨fun _ _ m h => lower_bound m.toMeasurableProtocol h,
    witness hL ho, witness_matches hL ho, witness_signaling hL ho⟩

def ValidSlope (L : Layout) (v : ℚ) (order : EarlyOrder) (c : Completion) (K : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (m : Model L v order Ω),
    operationalScore c m.toFinite.toProtocol.toModel.behavior ≤
      6 + K * m.toFinite.toProtocol.toModel.signaling

theorem coefficient_lower_bound_all_completions
    {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order)
    (c : Completion) (K : ℝ) (h : ValidSlope L v order c K) : 8 ≤ K := by
  have hk := h _ (witness hL ho)
  rw [operationalScore_of_matchesCluster c (witness_matches hL ho), witness_signaling] at hk
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hgt : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  nlinarith

theorem optimal_completion_globally_sharp
    {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    ValidSlope L v order optimalCompletion 8 ∧
      ∀ c K, ValidSlope L v order c K → 8 ≤ K := by
  constructor
  · intro Ω inst m
    rw [operationalScore_optimal_eq_score]
    exact tradeoff m.toMeasurableProtocol
  · exact coefficient_lower_bound_all_completions hL ho

theorem collectible_signal {L : Layout} {v : ℚ} {order : EarlyOrder}
    {Ω : Type*} [MeasurableSpace Ω] (m : Model L v order Ω)
    (hQ : ForcedSignalingTheorem2.MatchesCluster m.toFinite.toProtocol.toModel)
    (hL : BothCollectible L) :
    ∃ c : Context, Collectible (L (sender c)) (recipients L c) ∧
      (Real.sqrt 2 - 1) / 4 ≤ tv m.toFinite.toProtocol.toModel.behavior c :=
  vcausal_forced_superluminal_signal m.toFinite hQ hL

theorem noisy_collectible_signal {L : Layout} {v : ℚ} {order : EarlyOrder}
    {Ω : Type*} [MeasurableSpace Ω] (m : Model L v order Ω) (visibility : ℝ)
    (hQ : NoisyLC4.MatchesNoisyCluster visibility m.toFinite.toProtocol.toModel)
    (hL : BothCollectible L) :
    ∃ c : Context, Collectible (L (sender c)) (recipients L c) ∧
      max 0 ((visibility * (4 + 2 * Real.sqrt 2) - 6) / 8) ≤
        tv m.toFinite.toProtocol.toModel.behavior c :=
  ForcedSignalingCollectibility.noisy_collectible_signal m.toFinite visibility hQ hL

/-- The lower-bound component of the restoration-layout headline now ranges
over general measurable hidden laws. Timing-kernel extensions remain separate. -/
theorem physical_main_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (m : Model ForcedSignalingLayouts.restoration 10000 .aFirst Ω)
    (hQ : ForcedSignalingTheorem2.MatchesCluster m.toFinite.toProtocol.toModel) :
    ∃ c : Context,
      Collectible (ForcedSignalingLayouts.restoration (sender c))
        (recipients ForcedSignalingLayouts.restoration c) ∧
      (Real.sqrt 2 - 1) / 4 ≤ tv m.toFinite.toProtocol.toModel.behavior c :=
  collectible_signal m hQ restoration_both_collectible

end
end OntologySeparation.ForcedSignalingMeasures
