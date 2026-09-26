import OntologySeparation.Operational.VCausalRealization
import OntologySeparation.Experiments.ForcedSignalingTheorem2
import OntologySeparation.Experiments.NoisyLC4ForcedSignaling

namespace OntologySeparation.ForcedSignalingVCausal
noncomputable section
open scoped BigOperators
open HiddenInfluence ForcedSignalingLC4 ForcedSignalingLC4Witness
open VCausal

/-- The physical lower bound follows through the full-behavior bridge. -/
theorem vcausal_forced_signaling_lower_bound
    {L : Layout} {v : ℚ} {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (m : VCausal.Model L v order Ω)
    (h : ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel) :
    (Real.sqrt 2 - 1) / 4 ≤ m.toProtocol.toModel.signaling := by
  rw [← ForcedSignalingTheorem2.targetDelta_value]
  exact ForcedSignalingTheorem2.lower_bound h


/-- The certified slope-8 inequality transfers. Sharpness is a separate
realizability obligation and is not inferred from inclusion of model classes. -/
theorem vcausal_tradeoff {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) :
    score p.toModel.behavior ≤ 6 + 8 * p.toModel.signaling :=
  score_bound p.toModel _ ((signaling_le_iff _ _).mp le_rfl)

theorem vcausal_noise_lower_bound {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (visibility : ℝ)
    (h : NoisyLC4.MatchesNoisyCluster visibility p.toModel) :
    max 0 ((visibility * (4 + 2 * Real.sqrt 2) - 6) / 8) ≤ p.toModel.signaling :=
  NoisyLC4.lower_bound h

/-- Real-valued uniform early records; the latent space is still finite. -/
def uniformEarly (order : EarlyOrder) : EarlyModel order EarlyRecord where
  shared :=
    { mass := fun _ => 1/4
      nonneg := fun _ => by norm_num
      total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool] }
  record r _ := r
  allowed := fun _ _ => ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact matrix calculation from the existing LC4 definition. -/
theorem lc4_AD_uniform : ∀ x y w a d,
    (∑ b : Bool, ForcedSignalingLC4.abd x y w a b d) = qrat (1/4) := by
  intro x y w a d
  simp_rw [← seed_abd_matches]
  cases x <;> cases y <;> cases w <;> cases a <;> cases d <;>
    with_unfolding_all decide +kernel

set_option maxHeartbeats 0 in
private theorem early_marginal_coeff : ∀ e x y w a d (s : Strategy),
    (∑ b : Bool,
      let o := output (strategyAtom e s) (lateOf y false)
      (if e = earlyOf x w ∧ o.val / 8 = a.toNat ∧
        o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat then (1 : ℝ) else 0)) =
      if e = earlyOf x w ∧ s.record = (a,d) then 1 else 0 := by
  intro e x y w a d s
  rw [show lateOf y false = lateFromBool y false from rfl]
  simp only [strategy_visible_output]
  simp only [Fintype.sum_bool]
  rcases s with ⟨sa,sd,sb0,sb1,sc0,sc1⟩
  cases y <;> cases a <;> cases d <;> cases sa <;> cases sd <;>
    cases sb0 <;> cases sb1 <;> cases sc0 <;> cases sc1 <;>
    simp [Fintype.sum_bool, Strategy.visible, VisibleOutcome.toOutcome, Strategy.record]

theorem early_marginal_fromStrategies (q : Early → FiniteDistribution Strategy)
    (x y w a d : Bool) :
    (∑ b : Bool, modelABD (HiddenInfluence.Model.fromStrategies q) x y w a b d) =
      (FiniteKernel.map (q (earlyOf x w)) Strategy.record).mass (a,d) := by
  unfold modelABD
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [← atomEquiv.sum_comp]
  simp only [atomEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type]
  simp only [strategy_early, HiddenInfluence.Model.fromStrategies_weight_strategyAtom, early_marginal_coeff]
  rw [FiniteKernel.map_mass]
  simp [ite_mul, ite_and, Finset.sum_ite_irrel]

/-- LC4 matching supplies a realizable early law for every early causal order. -/
theorem matches_early_uniform (m : HiddenInfluence.Model)
    (h : ForcedSignalingTheorem2.MatchesCluster m) (order : EarlyOrder) :
    EarlyMatches (uniformEarly order) m.toStrategies := by
  intro e r
  obtain ⟨a,d⟩ := r
  have he : ∃ x w, earlyOf x w = e := by
    fin_cases e
    · exact ⟨false,false,rfl⟩
    · exact ⟨false,true,rfl⟩
    · exact ⟨true,false,rfl⟩
    · exact ⟨true,true,rfl⟩
  obtain ⟨x,w,rfl⟩ := he
  rw [← early_marginal_fromStrategies m.toStrategies x false w a d]
  have hr : ∀ b, modelABD (HiddenInfluence.Model.fromStrategies m.toStrategies) x false w a b d =
      modelABD m x false w a b d := by
    intro b
    unfold modelABD
    simp_rw [HiddenInfluence.Model.fromStrategies_toStrategies_weight]
  simp_rw [hr, h.abd]
  rw [← toReal_sum, lc4_AD_uniform, toReal_qrat]
  norm_num [FiniteKernel.map_mass, uniformEarly, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Every LC4-matching completion has a finite, setting-independent causal
realization. This is a fixed-layout theorem, not an extension across timings. -/
def realizeLC4 (m : HiddenInfluence.Model)
    (h : ForcedSignalingTheorem2.MatchesCluster m) (order : EarlyOrder) :
    Protocol order (EarlyRecord × (Early → Strategy)) :=
  realize (uniformEarly order) m.toStrategies (matches_early_uniform m h order)

theorem realizeLC4_weight (m : HiddenInfluence.Model)
    (h : ForcedSignalingTheorem2.MatchesCluster m) (order : EarlyOrder) (j : Atom) :
    (realizeLC4 m h order).toModel.weight j = m.weight j := by
  unfold Protocol.toModel HiddenInfluence.Model.fromStrategies
  simp only [realizeLC4, HiddenInfluence.Model.ofAtoms, atomWeights]
  simp_rw [realize_strategies]
  exact m.fromStrategies_toStrategies_weight j

/-- Full observed behavior is preserved by LC4 realization. -/
theorem realizeLC4_behavior (m : HiddenInfluence.Model)
    (h : ForcedSignalingTheorem2.MatchesCluster m) (order : EarlyOrder) :
    ObservationallyEquivalent (realizeLC4 m h order).toModel.behavior m.behavior := by
  intro setting outcome
  unfold HiddenInfluence.Model.behavior
  simp_rw [realizeLC4_weight]

theorem stochastic_realization {Ω : Type} [Fintype Ω] (m : StochasticModel Ω)
    (h : ForcedSignalingTheorem2.StochasticMatchesCluster m) (order : EarlyOrder) :
    ∃ p : Protocol order (EarlyRecord × (Early → Strategy)),
      ObservationallyEquivalent p.toModel.behavior m.behavior := by
  exact ⟨realizeLC4 m.determinize h.toMatchesCluster order,
    realizeLC4_behavior m.determinize h.toMatchesCluster order⟩

def witnessOn {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    VCausal.Model L v order (EarlyRecord × (Early → Strategy)) where
  toProtocol := realizeLC4 ForcedSignalingLC4Witness.model ForcedSignalingTheorem2.witness_matches order
  layout := hL
  geometry := ho

theorem witnessOn_matches {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    ForcedSignalingTheorem2.MatchesCluster (witnessOn hL ho).toProtocol.toModel := by
  constructor
  · intro x y w a b d
    unfold modelABD
    simp_rw [witnessOn, realizeLC4_weight]
    exact ForcedSignalingLC4Witness.model_abd_matches x y w a b d
  · intro x z w a c d
    unfold modelACD
    simp_rw [witnessOn, realizeLC4_weight]
    exact ForcedSignalingLC4Witness.model_acd_matches x z w a c d

theorem witnessOn_signaling {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    (witnessOn hL ho).toProtocol.toModel.signaling = (Real.sqrt 2 - 1) / 4 := by
  have ext : ∀ m n : HiddenInfluence.Model, (∀ j, m.weight j = n.weight j) → m = n := by
    rintro ⟨a,ha,ta⟩ ⟨b,hb,tb⟩ h
    have he : a = b := funext h
    cases he
    rfl
  have he : (witnessOn hL ho).toProtocol.toModel = ForcedSignalingLC4Witness.model :=
    ext _ _ (realizeLC4_weight _ ForcedSignalingTheorem2.witness_matches order)
  rw [he, ForcedSignalingLC4Witness.signaling_exact, ForcedSignalingTheorem2.targetDelta_value]

/-- Exact fixed-layout optimum, with a nonempty physically realizable class. -/
theorem vcausal_exact_forced_signaling {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    (∀ (Ω : Type) [Fintype Ω] (m : VCausal.Model L v order Ω),
      ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel →
      (Real.sqrt 2 - 1) / 4 ≤ m.toProtocol.toModel.signaling) ∧
    ∃ m : VCausal.Model L v order (EarlyRecord × (Early → Strategy)),
      ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel ∧
      m.toProtocol.toModel.signaling = (Real.sqrt 2 - 1) / 4 := by
  exact ⟨fun _ _ m h => vcausal_forced_signaling_lower_bound m h,
    witnessOn hL ho, witnessOn_matches hL ho, witnessOn_signaling hL ho⟩

end
end OntologySeparation.ForcedSignalingVCausal
