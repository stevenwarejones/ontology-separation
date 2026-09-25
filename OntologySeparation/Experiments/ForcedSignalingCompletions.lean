import OntologySeparation.Experiments.ForcedSignalingTheorem2

/-!
# Operational completions of the S4 witness

The six correlators entering S4 do not by themselves specify a single full
four-party setting for each estimated correlator. A completion fixes the unused
settings. There are nine independent binary choices, hence 512 raw completions.

This module keeps the raw completion visible. Later theorems prove which choices
drop out for conditionally-local hidden-influence models and establish exact
completion-independent sharpness of the slope 8 lower bound.
-/

namespace OntologySeparation.HiddenInfluenceCompletion
noncomputable section

open scoped BigOperators
open HiddenInfluence
open ForcedSignalingLC4Witness
open ForcedSignalingTheorem2

/-- Nine binary choices specifying the unused settings in the six S4 terms.

The source ordering is
`((z₁,w₁),(z₂,w₂),z₃,z₄,(x₅,y₅),y₆)`.

We represent the nine bits by `Fin 512` so exhaustive kernel checks range over
exactly the raw completion family without relying on a derived product `Fintype`.
-/
abbrev Completion := Fin 512

private def completionBit (c : Completion) (k : Nat) : Bool :=
  decide (c.val / (2^k) % 2 = 1)

def Completion.z1 (c : Completion) : Bool := completionBit c 0
def Completion.w1 (c : Completion) : Bool := completionBit c 1
def Completion.z2 (c : Completion) : Bool := completionBit c 2
def Completion.w2 (c : Completion) : Bool := completionBit c 3
def Completion.z3 (c : Completion) : Bool := completionBit c 4
def Completion.z4 (c : Completion) : Bool := completionBit c 5
def Completion.x5 (c : Completion) : Bool := completionBit c 6
def Completion.y5 (c : Completion) : Bool := completionBit c 7
def Completion.y6 (c : Completion) : Bool := completionBit c 8

/-- The completion used by the exact K=8 certificate:
`((0,1),(0,1),0,0,(1,0),0)`. -/
def optimalCompletion : Completion := ⟨74, by norm_num⟩

/-- The all-zero/default completion used as a common comparison in the source
numerics. -/
def defaultCompletion : Completion := 0

/-- The three completion choices that remain after quotienting the blind-party
settings by conditional locality. The reduction itself is proved below rather
than assumed in this definition. -/
def Completion.effective (c : Completion) : Bool × Bool × Bool :=
  (c.w1, c.w2, c.x5)

def sameEffective (c d : Completion) : Prop :=
  c.effective = d.effective

/-- Raw operational S4 score for an arbitrary full behavior and an explicit
completion. No hidden-variable assumptions are built into this definition. -/
noncomputable def operationalScore
    (c : Completion) (p : Behavior HiddenInfluence.interface) : ℝ :=
  mean p (earlyOf false c.w1) (lateOf false c.z1)
      (fun o => (parity 0 o : ℝ)) +
  mean p (earlyOf false c.w2) (lateOf true c.z2)
      (fun o => (parity 1 o : ℝ)) +
  mean p (earlyOf true false) (lateOf false c.z3)
      (fun o => (parity 2 o : ℝ)) -
  mean p (earlyOf true false) (lateOf true c.z4)
      (fun o => (parity 3 o : ℝ)) +
  2 * mean p (earlyOf c.x5 false) (lateOf c.y5 false)
      (fun o => (parity 4 o : ℝ)) +
  2 * mean p (earlyOf false true) (lateOf c.y6 true)
      (fun o => (parity 5 o : ℝ))

/-- A completion-specific linear tradeoff with the standard intercept 6. -/
def ValidSlope (c : Completion) (K : ℝ) : Prop :=
  ∀ m : Model, operationalScore c m.behavior ≤ 6 + K * m.signaling


theorem completion_count : Fintype.card Completion = 512 := by
  simp [Completion]

/-- Integer coefficient of one deterministic hidden-response atom in the raw
completed score. -/
def operationalCoeff (c : Completion) (j : Atom) : ℤ :=
  (if early j = earlyOf false c.w1
    then parity 0 (output j (lateOf false c.z1)) else 0) +
  (if early j = earlyOf false c.w2
    then parity 1 (output j (lateOf true c.z2)) else 0) +
  (if early j = earlyOf true false
    then parity 2 (output j (lateOf false c.z3)) else 0) -
  (if early j = earlyOf true false
    then parity 3 (output j (lateOf true c.z4)) else 0) +
  2 * (if early j = earlyOf c.x5 false
    then parity 4 (output j (lateOf c.y5 false)) else 0) +
  2 * (if early j = earlyOf false true
    then parity 5 (output j (lateOf c.y6 true)) else 0)

theorem operationalScore_eq_sum (c : Completion) (m : Model) :
    operationalScore c m.behavior =
      ∑ j, (operationalCoeff c j : ℝ) * m.weight j := by
  unfold operationalScore
  rw [mean_eq, mean_eq, mean_eq, mean_eq, mean_eq, mean_eq]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [operationalCoeff, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_ite, Int.cast_zero]
  ring

/-- Same completed score expressed only through the two observable no-blind-pair
marginal families. Blind-party completion settings are absent here; the theorem
below proves this marginal expression equals the raw operational score for every
conditionally-local response model. -/
noncomputable def marginalScore (c : Completion) (m : Model) : ℝ :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) * modelABD m false false c.w1 a b d) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) * modelABD m false true c.w2 a b d) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) * modelABD m true false false a b d) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) * modelABD m true true false a b d) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn cc * sgn d : ℤ) * modelACD m c.x5 false false a cc d) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn a * sgn cc * sgn d : ℤ) * modelACD m false true true a cc d)

def marginalCoeffAt (c : Completion) (j : Atom) : ℤ :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b) *
        (if
          let o := output j (lateOf false false)
          early j = earlyOf false c.w1 ∧
          o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b) *
        (if
          let o := output j (lateOf true false)
          early j = earlyOf false c.w2 ∧
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
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn cc * sgn d) *
        (if
          let o := output j (lateOf false false)
          early j = earlyOf c.x5 false ∧
          o.val / 8 = a.toNat ∧ o.val / 2 % 2 = cc.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn a * sgn cc * sgn d) *
        (if
          let o := output j (lateOf false true)
          early j = earlyOf false true ∧
          o.val / 8 = a.toNat ∧ o.val / 2 % 2 = cc.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0))

/-- Coefficient after removing the six blind-party completion choices.
Only the three effective early-setting bits remain. -/
def reducedOperationalCoeff (w1 w2 x5 : Bool) (j : Atom) : ℤ :=
  (if early j = earlyOf false w1
    then parity 0 (output j (lateOf false false)) else 0) +
  (if early j = earlyOf false w2
    then parity 1 (output j (lateOf true false)) else 0) +
  (if early j = earlyOf true false
    then parity 2 (output j (lateOf false false)) else 0) -
  (if early j = earlyOf true false
    then parity 3 (output j (lateOf true false)) else 0) +
  2 * (if early j = earlyOf x5 false
    then parity 4 (output j (lateOf false false)) else 0) +
  2 * (if early j = earlyOf false true
    then parity 5 (output j (lateOf false true)) else 0)

/-- Marginal coefficient parameterized directly by the three effective
completion bits, avoiding any enumeration over the 512 raw completions. -/
def reducedMarginalCoeffAt (w1 w2 x5 : Bool) (j : Atom) : ℤ :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b) *
        (if
          let o := output j (lateOf false false)
          early j = earlyOf false w1 ∧
          o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b) *
        (if
          let o := output j (lateOf true false)
          early j = earlyOf false w2 ∧
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
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn cc * sgn d) *
        (if
          let o := output j (lateOf false false)
          early j = earlyOf x5 false ∧
          o.val / 8 = a.toNat ∧ o.val / 2 % 2 = cc.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0)) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn a * sgn cc * sgn d) *
        (if
          let o := output j (lateOf false true)
          early j = earlyOf false true ∧
          o.val / 8 = a.toNat ∧ o.val / 2 % 2 = cc.toNat ∧ o.val % 2 = d.toNat
        then 1 else 0))

set_option maxRecDepth 100000 in
theorem parity0_blind_z : ∀ (j : Atom) (z : Bool),
    parity 0 (output j (lateOf false z)) =
      parity 0 (output j (lateOf false false)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem parity1_blind_z : ∀ (j : Atom) (z : Bool),
    parity 1 (output j (lateOf true z)) =
      parity 1 (output j (lateOf true false)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem parity2_blind_z : ∀ (j : Atom) (z : Bool),
    parity 2 (output j (lateOf false z)) =
      parity 2 (output j (lateOf false false)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem parity3_blind_z : ∀ (j : Atom) (z : Bool),
    parity 3 (output j (lateOf true z)) =
      parity 3 (output j (lateOf true false)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem parity4_blind_y : ∀ (j : Atom) (y : Bool),
    parity 4 (output j (lateOf y false)) =
      parity 4 (output j (lateOf false false)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem parity5_blind_y : ∀ (j : Atom) (y : Bool),
    parity 5 (output j (lateOf y true)) =
      parity 5 (output j (lateOf false true)) := by
  decide +kernel

theorem operationalCoeff_eq_reduced (c : Completion) (j : Atom) :
    operationalCoeff c j =
      reducedOperationalCoeff c.w1 c.w2 c.x5 j := by
  unfold operationalCoeff reducedOperationalCoeff
  rw [parity0_blind_z j c.z1, parity1_blind_z j c.z2,
    parity2_blind_z j c.z3, parity3_blind_z j c.z4,
    parity4_blind_y j c.y5, parity5_blind_y j c.y6]

theorem marginalCoeffAt_eq_reduced (c : Completion) (j : Atom) :
    marginalCoeffAt c j =
      reducedMarginalCoeffAt c.w1 c.w2 c.x5 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reducedOperationalCoeff_eq_reducedMarginal :
    ∀ w1 w2 x5 : Bool, ∀ j : Atom,
      reducedOperationalCoeff w1 w2 x5 j =
        reducedMarginalCoeffAt w1 w2 x5 j := by
  decide +kernel

theorem operationalCoeff_eq_marginalCoeffAt
    (c : Completion) (j : Atom) :
    operationalCoeff c j = marginalCoeffAt c j := by
  rw [operationalCoeff_eq_reduced, marginalCoeffAt_eq_reduced,
    reducedOperationalCoeff_eq_reducedMarginal]

theorem marginalScore_eq_sum (c : Completion) (m : Model) :
    marginalScore c m =
      ∑ j, (marginalCoeffAt c j : ℝ) * m.weight j := by
  unfold marginalScore modelABD modelACD
  simp only [Fintype.sum_bool, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [marginalCoeffAt, Fintype.sum_bool, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_zero, Int.cast_one]
  ring

/-- Conditional locality makes the six blind-party completion choices
operationally irrelevant. The raw completed score equals the expression built
only from the reproduced ABD/ACD marginal families. -/
theorem operationalScore_eq_marginalScore (c : Completion) (m : Model) :
    operationalScore c m.behavior = marginalScore c m := by
  rw [operationalScore_eq_sum, marginalScore_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [operationalCoeff_eq_marginalCoeffAt]

/-- Therefore two raw completions with the same three effective choices have
identical scores on every conditionally-local response model. -/
theorem score_eq_of_sameEffective {c d : Completion}
    (h : sameEffective c d) (m : Model) :
    operationalScore c m.behavior = operationalScore d m.behavior := by
  rw [operationalScore_eq_marginalScore, operationalScore_eq_marginalScore]
  unfold sameEffective Completion.effective at h
  have hw1 : c.w1 = d.w1 := congrArg Prod.fst h
  have htail : (c.w2, c.x5) = (d.w2, d.x5) := congrArg Prod.snd h
  have hw2 : c.w2 = d.w2 := congrArg Prod.fst htail
  have hx5 : c.x5 = d.x5 := congrArg Prod.snd htail
  simp [marginalScore, hw1, hw2, hx5]


/-- LC4 no-blind-pair value of a completed score, before embedding Q(sqrt 2)
into the reals. -/
def targetMarginalScoreQ2 (c : Completion) : ForcedSignalingLC4.Q2 :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b))
        (ForcedSignalingLC4.abd false false c.w1 a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b))
        (ForcedSignalingLC4.abd false true c.w2 a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b * sgn d))
        (ForcedSignalingLC4.abd true false false a b d)) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b * sgn d))
        (ForcedSignalingLC4.abd true true false a b d)) +
  ForcedSignalingLC4.qmul (ForcedSignalingLC4.qrat 2)
    (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn cc * sgn d))
        (ForcedSignalingLC4.acd c.x5 false false a cc d)) +
  ForcedSignalingLC4.qmul (ForcedSignalingLC4.qrat 2)
    (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn cc * sgn d))
        (ForcedSignalingLC4.acd false true true a cc d))

def targetMarginalScoreQ2Effective (w1 w2 x5 : Bool) :
    ForcedSignalingLC4.Q2 :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b))
        (ForcedSignalingLC4.abd false false w1 a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b))
        (ForcedSignalingLC4.abd false true w2 a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b * sgn d))
        (ForcedSignalingLC4.abd true false false a b d)) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn b * sgn d))
        (ForcedSignalingLC4.abd true true false a b d)) +
  ForcedSignalingLC4.qmul (ForcedSignalingLC4.qrat 2)
    (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn cc * sgn d))
        (ForcedSignalingLC4.acd x5 false false a cc d)) +
  ForcedSignalingLC4.qmul (ForcedSignalingLC4.qrat 2)
    (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      ForcedSignalingLC4.qmul
        (ForcedSignalingLC4.qrat (sgn a * sgn cc * sgn d))
        (ForcedSignalingLC4.acd false true true a cc d))

theorem targetMarginalScoreQ2_eq_effective (c : Completion) :
    targetMarginalScoreQ2 c =
      targetMarginalScoreQ2Effective c.w1 c.w2 c.x5 := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem targetMarginalScoreQ2Effective_eq_score :
    ∀ w1 w2 x5 : Bool,
      targetMarginalScoreQ2Effective w1 w2 x5 =
        ForcedSignalingLC4.score := by
  decide +kernel

/-- The LC4 target has the same S4 value for every operational completion. -/
theorem targetMarginalScoreQ2_eq_score (c : Completion) :
    targetMarginalScoreQ2 c = ForcedSignalingLC4.score := by
  rw [targetMarginalScoreQ2_eq_effective,
    targetMarginalScoreQ2Effective_eq_score]

private theorem toReal_sub
    (a b : ForcedSignalingLC4.Q2) :
    ForcedSignalingLC4.Q2.toReal (a - b) =
      ForcedSignalingLC4.Q2.toReal a - ForcedSignalingLC4.Q2.toReal b := by
  simp [ForcedSignalingLC4.Q2.toReal]
  ring

/-- Any model reproducing the LC4 no-blind-pair marginals has the quantum target
score under every completion. -/
theorem marginalScore_of_matchesCluster
    (c : Completion) {m : Model} (h : MatchesCluster m) :
    marginalScore c m = 4 + 2 * Real.sqrt 2 := by
  unfold marginalScore
  simp_rw [h.abd, h.acd]
  have hq :
      ForcedSignalingLC4.Q2.toReal (targetMarginalScoreQ2 c) =
        4 + 2 * Real.sqrt 2 := by
    rw [targetMarginalScoreQ2_eq_score, ForcedSignalingLC4.score_exact_real]
  rw [← hq]
  simp [targetMarginalScoreQ2, ForcedSignalingLC4.toReal_add, toReal_sub,
    ForcedSignalingLC4.toReal_qmul, ForcedSignalingLC4.toReal_sum]

theorem operationalScore_of_matchesCluster
    (c : Completion) {m : Model} (h : MatchesCluster m) :
    operationalScore c m.behavior = 4 + 2 * Real.sqrt 2 := by
  rw [operationalScore_eq_marginalScore]
  exact marginalScore_of_matchesCluster c h

/-- Exact all-completions optimality: with intercept 6 fixed, no valid
completion-specific linear tradeoff can have slope below 8. -/
theorem coefficient_lower_bound_all_completions
    (c : Completion) (K : ℝ) (h : ValidSlope c K) :
    8 ≤ K := by
  have hk := h ForcedSignalingLC4Witness.model
  rw [operationalScore_of_matchesCluster c
      ForcedSignalingTheorem2.witness_matches,
    ForcedSignalingLC4Witness.signaling_exact,
    ForcedSignalingTheorem2.targetDelta_value] at hk
  have hsqrt : (1 : ℝ) < Real.sqrt 2 := by
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem operationalCoeff_optimal_eq_scoreCoeff :
    ∀ j : Atom, operationalCoeff optimalCompletion j = scoreCoeff j := by
  with_unfolding_all decide +kernel

theorem operationalScore_optimal_eq_score (m : Model) :
    operationalScore optimalCompletion m.behavior = score m.behavior := by
  rw [operationalScore_eq_sum, score_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [operationalCoeff_optimal_eq_scoreCoeff]

/-- The existing K=8 completion attains the universal minimum slope, while the
preceding theorem proves that no other valid completion can do better. -/
theorem optimal_completion_globally_sharp :
    ValidSlope optimalCompletion 8 ∧
      ∀ c : Completion, ∀ K : ℝ, ValidSlope c K → 8 ≤ K := by
  constructor
  · intro m
    rw [operationalScore_optimal_eq_score]
    exact HiddenInfluence.score_bound m m.signaling
      ((HiddenInfluence.signaling_le_iff m m.signaling).mp le_rfl)
  · intro c K hK
    exact coefficient_lower_bound_all_completions c K hK
/-- Completion-specific tradeoff premise stated directly for the finite stochastic
conditional-local class. -/
def StochasticValidSlope (c : Completion) (K : ℝ) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (m : StochasticModel Ω),
    operationalScore c m.behavior ≤ 6 + K * m.signaling

/-- Any deterministic-model tradeoff immediately lifts to the finite stochastic
class because stochastic behavior and signaling are defined through, and proved
preserved by, determinization. -/
theorem validSlope_to_stochastic
    (c : Completion) (K : ℝ) (h : ValidSlope c K) :
    StochasticValidSlope c K := by
  intro Ω _ m
  simpa [StochasticModel.behavior, StochasticModel.signaling] using
    h m.determinize

/-- Conversely, a stochastic-class tradeoff applies to every deterministic model
through the explicit stochastic round-trip representative. -/
theorem stochasticValidSlope_to_valid
    (c : Completion) (K : ℝ) (h : StochasticValidSlope c K) :
    ValidSlope c K := by
  intro m
  have hs := h Strategy (StochasticModel.ofStrategies m.toStrategies)
  rw [m.stochastic_roundtrip_signaling] at hs
  have hscore :
      operationalScore c
        (StochasticModel.ofStrategies m.toStrategies).behavior =
      operationalScore c m.behavior := by
    change operationalScore c
        ((StochasticModel.ofStrategies m.toStrategies).determinize).behavior =
      operationalScore c m.behavior
    unfold operationalScore mean
    simp_rw [m.stochastic_roundtrip]
  rw [hscore] at hs
  exact hs

/-- Exact all-completions optimality for finite stochastic conditional-local
models: no valid completion admits slope below 8, and the certified completion
achieves slope 8 for the whole stochastic class. -/
theorem stochastic_completion_globally_sharp :
    StochasticValidSlope optimalCompletion 8 ∧
      ∀ c : Completion, ∀ K : ℝ, StochasticValidSlope c K → 8 ≤ K := by
  constructor
  · exact validSlope_to_stochastic optimalCompletion 8
      optimal_completion_globally_sharp.1
  · intro c K hK
    exact coefficient_lower_bound_all_completions c K
      (stochasticValidSlope_to_valid c K hK)

end
end OntologySeparation.HiddenInfluenceCompletion
