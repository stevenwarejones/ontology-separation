import OntologySeparation.Experiments.ForcedSignalingTheorem2

/-! Lemma 2: for an early sender, every recipient set omitting B or C is a
projection of one of the four pinned pairs BD, CD, AB, AC. The theorem below
allows arbitrary deterministic projections, including constants and singletons. -/
namespace OntologySeparation.ForcedSignalingPinned
noncomputable section
open scoped BigOperators
open HiddenInfluence ForcedSignalingLC4 ForcedSignalingLC4Witness

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem quantum_BD : ∀ x y w b d,
    (∑ a : Bool, abd x y w a b d) = ∑ a : Bool, abd false y w a b d := by
  intro x y w b d
  simp_rw [← ForcedSignalingLC4Witness.seed_abd_matches]
  cases x <;> cases y <;> cases w <;> cases b <;> cases d <;>
    with_unfolding_all decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem quantum_CD : ∀ x z w c d,
    (∑ a : Bool, acd x z w a c d) = ∑ a : Bool, acd false z w a c d := by
  intro x z w c d
  simp_rw [← ForcedSignalingLC4Witness.seed_acd_matches]
  cases x <;> cases z <;> cases w <;> cases c <;> cases d <;>
    with_unfolding_all decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem quantum_AB : ∀ x y w a b,
    (∑ d : Bool, abd x y w a b d) = ∑ d : Bool, abd x y false a b d := by
  intro x y w a b
  simp_rw [← ForcedSignalingLC4Witness.seed_abd_matches]
  cases x <;> cases y <;> cases w <;> cases a <;> cases b <;>
    with_unfolding_all decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem quantum_AC : ∀ x z w a c,
    (∑ d : Bool, acd x z w a c d) = ∑ d : Bool, acd x z false a c d := by
  intro x z w a c
  simp_rw [← ForcedSignalingLC4Witness.seed_acd_matches]
  cases x <;> cases z <;> cases w <;> cases a <;> cases c <;>
    with_unfolding_all decide +kernel

theorem pinned_BD {m : Model} (h : ForcedSignalingTheorem2.MatchesCluster m)
    (x y w b d : Bool) :
    (∑ a : Bool, modelABD m x y w a b d) = ∑ a : Bool, modelABD m false y w a b d := by
  simp_rw [h.abd]
  rw [← toReal_sum, ← toReal_sum, quantum_BD]

theorem pinned_CD {m : Model} (h : ForcedSignalingTheorem2.MatchesCluster m)
    (x z w c d : Bool) :
    (∑ a : Bool, modelACD m x z w a c d) = ∑ a : Bool, modelACD m false z w a c d := by
  simp_rw [h.acd]
  rw [← toReal_sum, ← toReal_sum, quantum_CD]

theorem pinned_AB {m : Model} (h : ForcedSignalingTheorem2.MatchesCluster m)
    (x y w a b : Bool) :
    (∑ d : Bool, modelABD m x y w a b d) = ∑ d : Bool, modelABD m x y false a b d := by
  simp_rw [h.abd]
  rw [← toReal_sum, ← toReal_sum, quantum_AB]

theorem pinned_AC {m : Model} (h : ForcedSignalingTheorem2.MatchesCluster m)
    (x z w a c : Bool) :
    (∑ d : Bool, modelACD m x z w a c d) = ∑ d : Bool, modelACD m x z false a c d := by
  simp_rw [h.acd]
  rw [← toReal_sum, ← toReal_sum, quantum_AC]

/-- Any projection of a pinned distribution is pinned, including every smaller
recipient set. This is marginalization, with no outcome-based selection. -/
theorem pinned_projection {α β : Type} [Fintype α] [DecidableEq β]
    (p q : α → ℝ) (h : ∀ a, p a = q a) (f : α → β) (b : β) :
    (∑ a, if f a = b then p a else 0) = ∑ a, if f a = b then q a else 0 := by
  simp_rw [h]

end
end OntologySeparation.ForcedSignalingPinned
