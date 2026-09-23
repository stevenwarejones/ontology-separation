import OntologySeparation.Experiments.ForcedSignalingLC4Witness
import OntologySeparation.Experiments.SignalingTradeoff
import OntologySeparation.Core.SharpOptimum

namespace OntologySeparation.ForcedSignalingTheorem2
noncomputable section

open scoped BigOperators
open HiddenInfluence
open ForcedSignalingLC4
open ForcedSignalingLC4Witness

structure MatchesCluster (m : Model) : Prop where
  abd : ∀ x y w a b d,
    modelABD m x y w a b d =
      Q2.toReal (ForcedSignalingLC4.abd x y w a b d)
  acd : ∀ x z w a c d,
    modelACD m x z w a c d =
      Q2.toReal (ForcedSignalingLC4.acd x z w a c d)

def sgn (b : Bool) : ℤ := if b then -1 else 1

noncomputable def marginalScore (m : Model) : ℝ :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) * modelABD m false false true a b d) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) * modelABD m false true true a b d) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) * modelABD m true false false a b d) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) * modelABD m true true false a b d) +
  2 * (∑ a : Bool, ∑ c : Bool, ∑ d : Bool,
      (sgn c * sgn d : ℤ) * modelACD m true false false a c d) +
  2 * (∑ a : Bool, ∑ c : Bool, ∑ d : Bool,
      (sgn a * sgn c * sgn d : ℤ) * modelACD m false true true a c d)

def marginalCoeff (j : Atom) : ℤ :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b) *
        (if
          let o := output j (lateOf false false)
          early j = earlyOf false true ∧
          o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b) *
        (if
          let o := output j (lateOf true false)
          early j = earlyOf false true ∧
          o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d) *
        (if
          let o := output j (lateOf false false)
          early j = earlyOf true false ∧
          o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d) *
        (if
          let o := output j (lateOf true false)
          early j = earlyOf true false ∧
          o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  2 * (∑ a : Bool, ∑ c : Bool, ∑ d : Bool,
      (sgn c * sgn d) *
        (if
          let o := output j (lateOf false false)
          early j = earlyOf true false ∧
          o.val / 8 = a.toNat ∧ o.val / 2 % 2 = c.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  2 * (∑ a : Bool, ∑ c : Bool, ∑ d : Bool,
      (sgn a * sgn c * sgn d) *
        (if
          let o := output j (lateOf false true)
          early j = earlyOf false true ∧
          o.val / 8 = a.toNat ∧ o.val / 2 % 2 = c.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem marginalCoeff_eq_scoreCoeff : ∀ j : Atom,
    marginalCoeff j = scoreCoeff j := by
  with_unfolding_all decide +kernel

theorem marginalScore_eq_score (m : Model) :
    marginalScore m = score m.behavior := by
  rw [score_eq]
  unfold marginalScore modelABD modelACD
  simp only [Fintype.sum_bool, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← marginalCoeff_eq_scoreCoeff]
  simp only [marginalCoeff, Fintype.sum_bool, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_zero, Int.cast_one]
  ring

def targetMarginalScoreQ2 : Q2 :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      qmul (qrat (sgn a * sgn b))
        (ForcedSignalingLC4.abd false false true a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      qmul (qrat (sgn a * sgn b))
        (ForcedSignalingLC4.abd false true true a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      qmul (qrat (sgn a * sgn b * sgn d))
        (ForcedSignalingLC4.abd true false false a b d)) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      qmul (qrat (sgn a * sgn b * sgn d))
        (ForcedSignalingLC4.abd true true false a b d)) +
  qmul (qrat 2) (∑ a : Bool, ∑ c : Bool, ∑ d : Bool,
      qmul (qrat (sgn c * sgn d))
        (ForcedSignalingLC4.acd true false false a c d)) +
  qmul (qrat 2) (∑ a : Bool, ∑ c : Bool, ∑ d : Bool,
      qmul (qrat (sgn a * sgn c * sgn d))
        (ForcedSignalingLC4.acd false true true a c d))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem targetMarginalScore_exact :
    targetMarginalScoreQ2 = ForcedSignalingLC4.score := by
  with_unfolding_all decide +kernel

private theorem toReal_sub (a b : Q2) :
    Q2.toReal (a - b) = Q2.toReal a - Q2.toReal b := by
  simp [Q2.toReal]
  ring

theorem matches_score {m : Model} (h : MatchesCluster m) :
    score m.behavior = 4 + 2 * Real.sqrt 2 := by
  rw [← marginalScore_eq_score]
  unfold marginalScore
  simp_rw [h.abd, h.acd]
  have hq : Q2.toReal targetMarginalScoreQ2 = 4 + 2 * Real.sqrt 2 := by
    rw [targetMarginalScore_exact, score_exact_real]
  rw [← hq]
  simp [targetMarginalScoreQ2, toReal_add, toReal_sub, toReal_qmul, toReal_sum]

theorem lower_bound {m : Model} (h : MatchesCluster m) :
    ForcedSignalingLC4Witness.targetDelta ≤ m.signaling := by
  have hb : Within m.behavior m.signaling :=
    (signaling_le_iff m m.signaling).mp le_rfl
  have hs := score_bound m m.signaling hb
  rw [matches_score h] at hs
  unfold ForcedSignalingLC4Witness.targetDelta
  simp [ForcedSignalingLC4Witness.targetDeltaQ2, Q2.toReal, q]
  linarith

theorem witness_matches : MatchesCluster ForcedSignalingLC4Witness.model where
  abd := ForcedSignalingLC4Witness.model_abd_matches
  acd := ForcedSignalingLC4Witness.model_acd_matches

/-- The existing `SharpOptimum` interface maximizes its observable, so the
minimum signaling is represented by maximizing negative signaling. -/
def optimum :
    OntologySeparation.SharpOptimum
      (fun m : Model => MatchesCluster m)
      (fun m => -m.signaling)
      (-ForcedSignalingLC4Witness.targetDelta) where
  upper := fun _ hm => neg_le_neg (lower_bound hm)
  model := ForcedSignalingLC4Witness.model
  satisfies := witness_matches
  attains := congrArg Neg.neg ForcedSignalingLC4Witness.signaling_exact

theorem exact_forced_signaling :
    (∀ m : Model, MatchesCluster m →
      ForcedSignalingLC4Witness.targetDelta ≤ m.signaling) ∧
    ∃ m : Model, MatchesCluster m ∧
      m.signaling = ForcedSignalingLC4Witness.targetDelta := by
  obtain ⟨hbound, m, hm, hattains⟩ := optimum.sound
  constructor
  · intro m hm
    exact neg_le_neg_iff.mp (hbound m hm)
  · exact ⟨m, hm, neg_injective hattains⟩

theorem targetDelta_value :
    ForcedSignalingLC4Witness.targetDelta =
      (Real.sqrt 2 - 1) / 4 := by
  unfold ForcedSignalingLC4Witness.targetDelta
  simp [ForcedSignalingLC4Witness.targetDeltaQ2, Q2.toReal, q]
  ring

end
end OntologySeparation.ForcedSignalingTheorem2
