import OntologySeparation.Experiments.ForcedSignalingVCausal
import OntologySeparation.Experiments.ForcedSignalingCompletions

namespace OntologySeparation.ForcedSignalingVCausal
noncomputable section
open HiddenInfluence HiddenInfluenceCompletion VCausal

/-- The slope premise ranges only over physical protocols on this layout. -/
def PhysicalValidSlope (L : Layout) (v : ℚ) (order : EarlyOrder)
    (c : Completion) (K : ℝ) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (m : VCausal.Model L v order Ω),
    operationalScore c m.toProtocol.toModel.behavior ≤ 6 + K * m.toProtocol.toModel.signaling

/-- Sharpness uses the realized LC4 witness, not just inclusion of classes. -/
theorem vcausal_coefficient_lower_bound_all_completions
    {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order)
    (c : Completion) (K : ℝ) (h : PhysicalValidSlope L v order c K) : 8 ≤ K := by
  have hk := h _ (witnessOn hL ho)
  rw [operationalScore_of_matchesCluster c (witnessOn_matches hL ho), witnessOn_signaling] at hk
  have hsqrt : (1 : ℝ) < Real.sqrt 2 := by
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  nlinarith

theorem vcausal_optimal_completion_globally_sharp
    {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    PhysicalValidSlope L v order optimalCompletion 8 ∧
      ∀ c K, PhysicalValidSlope L v order c K → 8 ≤ K := by
  constructor
  · intro Ω inst m
    rw [operationalScore_optimal_eq_score]
    exact vcausal_tradeoff m.toProtocol
  · exact vcausal_coefficient_lower_bound_all_completions hL ho

end
end OntologySeparation.ForcedSignalingVCausal
