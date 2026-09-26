import OntologySeparation.Operational.VCausalTiming
import OntologySeparation.Experiments.ForcedSignalingCollectibility

namespace OntologySeparation.ForcedSignalingTiming
noncomputable section
open scoped BigOperators
open HiddenInfluence VCausal ForcedSignalingLC4Witness ForcedSignalingLC4

private theorem abd_bits (s : Strategy) (y : Bool) (a b d : Bool) :
    ((s.visible y false).toOutcome.val / 8 = a.toNat ∧
      (s.visible y false).toOutcome.val / 4 % 2 = b.toNat ∧
      (s.visible y false).toOutcome.val % 2 = d.toNat) ↔
      abdRecord (s.visible y false) = (a,b,d) := by
  rcases s with ⟨sa,sd,sb0,sb1,sc0,sc1⟩
  cases y <;> cases a <;> cases b <;> cases d <;> cases sa <;> cases sd <;>
    cases sb0 <;> cases sb1 <;> cases sc0 <;> cases sc1 <;> decide

private theorem acd_bits (s : Strategy) (z : Bool) (a c d : Bool) :
    ((s.visible false z).toOutcome.val / 8 = a.toNat ∧
      (s.visible false z).toOutcome.val / 2 % 2 = c.toNat ∧
      (s.visible false z).toOutcome.val % 2 = d.toNat) ↔
      acdRecord (s.visible false z) = (a,c,d) := by
  rcases s with ⟨sa,sd,sb0,sb1,sc0,sc1⟩
  cases z <;> cases a <;> cases c <;> cases d <;> cases sa <;> cases sd <;>
    cases sb0 <;> cases sb1 <;> cases sc0 <;> cases sc1 <;> decide

theorem protocol_ABD {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (x y w a b d : Bool) :
    modelABD p.toModel x y w a b d =
      recordProb (p.run (earlyOf x w) y false) abdRecord (a,b,d) := by
  unfold modelABD Protocol.toModel
  rw [← atomEquiv.sum_comp]
  simp only [atomEquiv, Fintype.sum_prod_type, strategy_early,
    show lateOf y false = lateFromBool y false from rfl,
    strategy_visible_output, HiddenInfluence.Model.fromStrategies_weight_strategyAtom]
  simp_rw [and_assoc, abd_bits]
  simp only [ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold recordProb Protocol.run
  rw [FiniteKernel.map_mean]
  have hh := FiniteKernel.map_mean p.shared (fun ω => p.table ω (earlyOf x w))
    (fun s => if abdRecord (s.visible y false) = (a,b,d) then (1 : ℝ) else 0)
  simpa [Protocol.strategies, mul_ite, ite_mul] using hh

theorem protocol_ACD {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (x z w a c d : Bool) :
    modelACD p.toModel x z w a c d =
      recordProb (p.run (earlyOf x w) false z) acdRecord (a,c,d) := by
  unfold modelACD Protocol.toModel
  rw [← atomEquiv.sum_comp]
  simp only [atomEquiv, Fintype.sum_prod_type, strategy_early,
    show lateOf false z = lateFromBool false z from rfl,
    strategy_visible_output, HiddenInfluence.Model.fromStrategies_weight_strategyAtom]
  simp_rw [and_assoc, acd_bits]
  simp only [ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold recordProb Protocol.run
  rw [FiniteKernel.map_mean]
  have hh := FiniteKernel.map_mean p.shared (fun ω => p.table ω (earlyOf x w))
    (fun s => if acdRecord (s.visible false z) = (a,c,d) then (1 : ℝ) else 0)
  simpa [Protocol.strategies, mul_ite, ite_mul] using hh


/-- Concrete independent delay choices can be made at the original events.
Each delayed branch is A -> D -> undelayed -> delayed at speed 4. -/
def minimalTiming : TimingLayout ForcedSignalingLayouts.minimal 4 where
  blind := ForcedSignalingLayouts.minimal_lc4
  delayedC := ⟨19/20,1/10⟩
  delayedB := ⟨19/20,-1/10⟩
  c_after := by norm_num [lightFuture, ForcedSignalingLayouts.minimal]
  b_after := by norm_num [lightFuture, ForcedSignalingLayouts.minimal]
  bc_connected := by norm_num [precedes, ForcedSignalingLayouts.minimal]
  cb_connected := by norm_num [precedes, ForcedSignalingLayouts.minimal]

/-- Reproduction is required in the two connected branches. The conclusion
transfers these observed families to the blind branch of the SAME mechanism. -/
structure ConnectedMatches {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    {p : Protocol order Ω} (t : TimingProtocol p) : Prop where
  abd : ∀ x y w a b d,
    recordProb (t.runC (earlyOf x w) y false) abdRecord (a,b,d) =
      Q2.toReal (ForcedSignalingLC4.abd x y w a b d)
  acd : ∀ x z w a c d,
    recordProb (t.runB (earlyOf x w) false z) acdRecord (a,c,d) =
      Q2.toReal (ForcedSignalingLC4.acd x z w a c d)

theorem ConnectedMatches.blind_matches {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    {p : Protocol order Ω} {t : TimingProtocol p} (h : ConnectedMatches t) :
    ForcedSignalingTheorem2.MatchesCluster p.toModel := by
  constructor
  · intro x y w a b d
    rw [protocol_ABD, ← t.delayC_preserves_ABD]
    exact h.abd x y w a b d
  · intro x z w a c d
    rw [protocol_ACD, ← t.delayB_preserves_ACD]
    exact h.acd x z w a c d

/-- The operational payoff with marginal matching derived from the connected
branches, rather than assumed directly in the blind branch. -/
theorem timing_forced_superluminal_signal
    {L : Layout} {v : ℚ} {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (m : VCausal.Model L v order Ω) (timing : TimingLayout L v)
    (t : TimingProtocol m.toProtocol)
    (hQ : ConnectedMatches t) (hL : ForcedSignalingCollectibility.BothCollectible L) :
    ∃ c : Context,
      Collectible (L (ForcedSignalingCollectibility.sender c))
        (ForcedSignalingCollectibility.recipients L c) ∧
      (Real.sqrt 2 - 1) / 4 ≤ tv m.toProtocol.toModel.behavior c := by
  exact ForcedSignalingCollectibility.vcausal_forced_superluminal_signal m hQ.blind_matches hL

end
end OntologySeparation.ForcedSignalingTiming
