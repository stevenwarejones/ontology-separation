import OntologySeparation.Experiments.ForcedSignalingLC4Witness
import OntologySeparation.Experiments.SignalingTradeoff
import OntologySeparation.Operational.HiddenInfluenceStochastic
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
  intro j
  fin_cases j <;> with_unfolding_all decide +kernel

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
  rw [ForcedSignalingLC4.score_exact]
  unfold targetMarginalScoreQ2
  simp_rw [← seed_abd_matches, ← seed_acd_matches]
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


/-- ABD marginal of a finite stochastic conditional-local model, expressed
through its proved-equivalent deterministic refinement. The observable
probability bridge in `HiddenInfluenceStochastic` identifies this with the
original factorized stochastic kernels. -/
noncomputable def stochasticABD {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) (x y w a b d : Bool) : ℝ :=
  modelABD m.determinize x y w a b d

/-- ACD marginal of a finite stochastic conditional-local model. -/
noncomputable def stochasticACD {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) (x z w a c d : Bool) : ℝ :=
  modelACD m.determinize x z w a c d

/-- The LC4 marginal-matching premise stated directly for finite stochastic
conditional-local hidden-influence models. -/
structure StochasticMatchesCluster {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) : Prop where
  abd : ∀ x y w a b d,
    stochasticABD m x y w a b d =
      Q2.toReal (ForcedSignalingLC4.abd x y w a b d)
  acd : ∀ x z w a c d,
    stochasticACD m x z w a c d =
      Q2.toReal (ForcedSignalingLC4.acd x z w a c d)

/-- A stochastic LC4-matching model determinizes to a model satisfying the
original Theorem-2 premise. -/
theorem StochasticMatchesCluster.toMatchesCluster
    {Ω : Type} [Fintype Ω] {m : StochasticModel Ω}
    (h : StochasticMatchesCluster m) :
    MatchesCluster m.determinize where
  abd := h.abd
  acd := h.acd

/-- Theorem 2 for the full finite stochastic conditional-local model class. -/
theorem stochastic_lower_bound
    {Ω : Type} [Fintype Ω] {m : StochasticModel Ω}
    (h : StochasticMatchesCluster m) :
    ForcedSignalingLC4Witness.targetDelta ≤ m.signaling := by
  simpa [StochasticModel.signaling] using
    (lower_bound (m := m.determinize) h.toMatchesCluster)

/-- Explicit stochastic representative of the exact LC4 attaining witness. -/
noncomputable def stochasticWitness :
    StochasticModel Strategy :=
  StochasticModel.ofStrategies ForcedSignalingLC4Witness.model.toStrategies

theorem stochasticWitness_determinize_weight (j : Atom) :
    stochasticWitness.determinize.weight j =
      ForcedSignalingLC4Witness.model.weight j := by
  exact ForcedSignalingLC4Witness.model.stochastic_roundtrip_weight j

theorem stochasticWitness_matches :
    StochasticMatchesCluster stochasticWitness := by
  constructor
  · intro x y w a b d
    unfold stochasticABD modelABD
    simp_rw [stochasticWitness_determinize_weight]
    exact ForcedSignalingLC4Witness.model_abd_matches x y w a b d
  · intro x z w a c d
    unfold stochasticACD modelACD
    simp_rw [stochasticWitness_determinize_weight]
    exact ForcedSignalingLC4Witness.model_acd_matches x z w a c d

theorem stochasticWitness_signaling :
    stochasticWitness.signaling =
      ForcedSignalingLC4Witness.targetDelta := by
  unfold stochasticWitness
  rw [ForcedSignalingLC4Witness.model.stochastic_roundtrip_signaling]
  exact ForcedSignalingLC4Witness.signaling_exact

/-- Exact forced-signaling theorem over finite stochastic conditional-local
models: the LC4 marginal constraints force the same minimum, and a stochastic
model attains it. -/
theorem exact_forced_signaling_stochastic :
    (∀ (Ω : Type) [Fintype Ω] (m : StochasticModel Ω),
      StochasticMatchesCluster m →
        ForcedSignalingLC4Witness.targetDelta ≤ m.signaling) ∧
    ∃ m : StochasticModel Strategy,
      StochasticMatchesCluster m ∧
        m.signaling = ForcedSignalingLC4Witness.targetDelta := by
  constructor
  · intro Ω _ m hm
    exact stochastic_lower_bound hm
  · exact ⟨stochasticWitness, stochasticWitness_matches,
      stochasticWitness_signaling⟩

theorem exact_forced_signaling_stochastic_value :
    (∀ (Ω : Type) [Fintype Ω] (m : StochasticModel Ω),
      StochasticMatchesCluster m →
        (Real.sqrt 2 - 1) / 4 ≤ m.signaling) ∧
    ∃ m : StochasticModel Strategy,
      StochasticMatchesCluster m ∧
        m.signaling = (Real.sqrt 2 - 1) / 4 := by
  rw [← targetDelta_value]
  exact exact_forced_signaling_stochastic

end
end OntologySeparation.ForcedSignalingTheorem2
