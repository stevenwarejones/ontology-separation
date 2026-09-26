import OntologySeparation.Experiments.ForcedSignalingVCausal
import OntologySeparation.Experiments.ForcedSignalingLayouts

namespace OntologySeparation.ForcedSignalingCollectibility
noncomputable section
open scoped BigOperators
open HiddenInfluence VCausal

/-- The context encoding in HiddenInfluence uses 0..7 for A, 8..15 for D. -/
def sender (c : Context) : Party := if c.val < 8 then .A else .D

def recipients (L : Layout) (c : Context) : Finset Event :=
  if c.val < 8 then {L .B, L .C, L .D} else {L .A, L .B, L .C}

/-- Both full complements are essential: the maximum could occur in either
setting direction and can be invisible to every proper recipient subset. -/
def BothCollectible (L : Layout) : Prop :=
  Collectible (L .A) {L .B,L .C,L .D} ∧ Collectible (L .D) {L .A,L .B,L .C}

theorem both_collectible_context {L : Layout} (h : BothCollectible L) (c : Context) :
    Collectible (L (sender c)) (recipients L c) := by
  by_cases hc : c.val < 8
  · simpa [sender,recipients,hc] using h.1
  · simpa [sender,recipients,hc] using h.2

/-- A finite maximum is achieved by an actual setting switch. -/
theorem signaling_attained (m : HiddenInfluence.Model) :
    ∃ c : Context, m.signaling = tv m.behavior c := by
  exact Finset.exists_mem_eq_sup' Finset.univ_nonempty (tv m.behavior) |>.imp
    (fun _ h => h.2)

/-- Main physical payoff in a fixed preferred frame. TV is to the complete
recipient record, all other settings held fixed. -/
theorem vcausal_forced_superluminal_signal
    {L : Layout} {v : ℚ} {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (m : VCausal.Model L v order Ω)
    (hQ : ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel)
    (hL : BothCollectible L) :
    ∃ c : Context, Collectible (L (sender c)) (recipients L c) ∧
      (Real.sqrt 2 - 1) / 4 ≤ tv m.toProtocol.toModel.behavior c := by
  obtain ⟨c,hc⟩ := signaling_attained m.toProtocol.toModel
  refine ⟨c,both_collectible_context hL c,?_⟩
  rw [← hc]
  exact ForcedSignalingVCausal.vcausal_forced_signaling_lower_bound m hQ

theorem minimal_both_collectible : BothCollectible ForcedSignalingLayouts.minimal :=
  ⟨ForcedSignalingLayouts.minimal_A_collectible, ForcedSignalingLayouts.minimal_D_collectible⟩

theorem restoration_both_collectible : BothCollectible ForcedSignalingLayouts.restoration :=
  ⟨ForcedSignalingLayouts.restoration_A_collectible, ForcedSignalingLayouts.restoration_D_collectible⟩

end
end OntologySeparation.ForcedSignalingCollectibility
