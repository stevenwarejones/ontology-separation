import OntologySeparation.Experiments.ForcedSignalingTheorem2
import OntologySeparation.Experiments.SignalingTradeoff

/-!
# White-noise robustness of the LC4 forced-signaling theorem

For visibility `p`, the target no-blind-pair marginals are those of

  p |LC4><LC4| + (1-p) I/16.

The white-noise contribution to every ABD/ACD marginal is 1/8.  This module
builds exact zero-signaling endpoint models at p=0 and at the S4 threshold, then
uses convex interpolation with the exact LC4 witness to prove the full
piecewise forced-signaling curve.
-/

namespace OntologySeparation.NoisyLC4
noncomputable section

open scoped BigOperators
open HiddenInfluence
open ForcedSignalingLC4
open ForcedSignalingLC4Witness
open ForcedSignalingTheorem2

def noisyABD (p : ℝ) (x y w a b d : Bool) : ℝ :=
  p * Q2.toReal (ForcedSignalingLC4.abd x y w a b d) + (1-p) / 8

def noisyACD (p : ℝ) (x z w a c d : Bool) : ℝ :=
  p * Q2.toReal (ForcedSignalingLC4.acd x z w a c d) + (1-p) / 8

structure MatchesNoisyCluster (p : ℝ) (m : Model) : Prop where
  abd : ∀ x y w a b d, modelABD m x y w a b d = noisyABD p x y w a b d
  acd : ∀ x z w a c d, modelACD m x z w a c d = noisyACD p x z w a c d

def thresholdVisibilityQ2 : Q2 := q 3 (-3/2)
noncomputable def thresholdVisibility : ℝ := Q2.toReal thresholdVisibilityQ2

theorem thresholdVisibility_value :
    thresholdVisibility = 3 - 3 * Real.sqrt 2 / 2 := by
  simp [thresholdVisibility, thresholdVisibilityQ2, Q2.toReal, q]
  ring

theorem thresholdVisibility_score :
    thresholdVisibility * (4 + 2 * Real.sqrt 2) = 6 := by
  rw [thresholdVisibility_value]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  ring_nf
  nlinarith

theorem thresholdVisibility_pos : 0 < thresholdVisibility := by
  rw [thresholdVisibility_value]
  nlinarith [ForcedSignalingLC4Witness.sqrtTwo_ge_one,
    ForcedSignalingLC4Witness.sqrtTwo_le_two,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem thresholdVisibility_lt_one : thresholdVisibility < 1 := by
  rw [thresholdVisibility_value]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

private def noisyQ2 (p qv : Q2) : Q2 :=
  qmul p qv + qmul (qrat 1 - p) (qrat (1/8))

def thresholdABD (x y w a b d : Bool) : Q2 :=
  noisyQ2 thresholdVisibilityQ2 (ForcedSignalingLC4.abd x y w a b d)

def thresholdACD (x z w a c d : Bool) : Q2 :=
  noisyQ2 thresholdVisibilityQ2 (ForcedSignalingLC4.acd x z w a c d)

private theorem toReal_sub (a b : Q2) :
    Q2.toReal (a-b) = Q2.toReal a - Q2.toReal b := by
  simp [Q2.toReal]
  ring

private theorem toReal_noisyQ2 (qv : Q2) :
    Q2.toReal (noisyQ2 thresholdVisibilityQ2 qv) =
      thresholdVisibility * Q2.toReal qv + (1-thresholdVisibility)/8 := by
  simp [noisyQ2, thresholdVisibility, toReal_add, toReal_sub, toReal_qmul]
  ring

namespace Threshold

abbrev Seed := Fin 72

def atoms (k : Seed) : Atom :=
  (#[0,2,3,12,17,18,19,23,27,36,40,44,45,46,51,61,62,63,64,65,66,68,72,80,
     82,83,87,91,98,109,110,111,117,121,124,125,127,128,136,137,138,140,145,
     148,149,151,157,160,164,165,166,172,181,185,186,187,192,199,200,207,211,
     213,218,220,225,228,235,238,242,246,249,253] : Array Atom)[k.val]

def weightQ2 (k : Seed) : Q2 :=
  (#[q (-3/16) (3/16),q (3/8) (-3/16),q (-1/4) (3/16),q (5/16) (-3/16),
     qrat (1/8),q (-1/4) (3/16),q (-1/4) (3/16),q (5/16) (-3/16),
     q (5/16) (-3/16),q (5/16) (-3/16),q (5/16) (-3/16),q (-1/4) (3/16),
     q (-1/4) (3/16),qrat (1/8),q (5/16) (-3/16),qrat (1/8),
     q (-1/4) (3/16),qrat (1/16),q (-1/4) (3/16),qrat (1/8),
     q (-1/4) (3/16),q (5/16) (-3/16),q (5/16) (-3/16),q (-1/4) (3/16),
     q (3/8) (-3/16),q (-1/2) (3/8),q (5/16) (-3/16),q (5/16) (-3/16),
     q (5/16) (-3/16),q (-1/4) (3/16),q (-3/16) (3/16),q (3/8) (-3/16),
     q (5/16) (-3/16),q (5/16) (-3/16),qrat (1/8),q (-1/4) (3/16),
     q (-1/4) (3/16),q (5/16) (-3/16),q (-1/4) (3/16),q (-1/4) (3/16),
     qrat (1/8),q (5/16) (-3/16),q (5/16) (-3/16),q (-1/4) (3/16),
     q (-1/4) (3/16),qrat (1/8),q (5/16) (-3/16),q (5/16) (-3/16),
     q (-1/4) (3/16),q (-1/4) (3/16),qrat (1/8),q (5/16) (-3/16),
     q (5/16) (-3/16),q (-3/16) (3/16),q (-1/4) (3/16),q (3/8) (-3/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16)] : Array Q2)[k.val]

set_option maxRecDepth 100000 in
private theorem weight_cases : ∀ k : Seed,
    weightQ2 k = q (-3/16) (3/16) ∨
    weightQ2 k = q (3/8) (-3/16) ∨
    weightQ2 k = q (-1/4) (3/16) ∨
    weightQ2 k = q (5/16) (-3/16) ∨
    weightQ2 k = qrat (1/8) ∨
    weightQ2 k = qrat (1/16) ∨
    weightQ2 k = q (-1/2) (3/8) := by
  with_unfolding_all decide +kernel

theorem weight_nonnegative (k : Seed) : 0 ≤ Q2.toReal (weightQ2 k) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  rcases weight_cases k with h | h | h | h | h | h | h <;> rw [h] <;>
    simp [Q2.toReal, q, qrat] <;> nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalsQ2 : ∀ e : Early,
    (∑ k : Seed, if early (atoms k) = e then weightQ2 k else 0) = qrat 1 := by
  with_unfolding_all decide +kernel

noncomputable def model : Model :=
  Model.ofAtoms atoms (fun k => Q2.toReal (weightQ2 k))
    weight_nonnegative
    (fun e => by
      have h := congrArg Q2.toReal (totalsQ2 e)
      rw [toReal_sum] at h
      simpa only [apply_ite, toReal_zero, toReal_qrat, Rat.cast_one] using h)

def seedABD (x y w a b d : Bool) : Q2 :=
  ∑ k : Seed,
    let o := output (atoms k) (lateOf y false)
    if early (atoms k) = earlyOf x w ∧
       o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
    then weightQ2 k else 0

def seedACD (x z w a c d : Bool) : Q2 :=
  ∑ k : Seed,
    let o := output (atoms k) (lateOf false z)
    if early (atoms k) = earlyOf x w ∧
       o.val / 8 = a.toNat ∧ o.val / 2 % 2 = c.toNat ∧ o.val % 2 = d.toNat
    then weightQ2 k else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_abd_matches :
    ∀ x y w a b d, seedABD x y w a b d = thresholdABD x y w a b d := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_acd_matches :
    ∀ x z w a c d, seedACD x z w a c d = thresholdACD x z w a c d := by
  with_unfolding_all decide +kernel

private theorem toReal_indicator (P : Prop) [Decidable P] (w : Q2) :
    (if P then (1 : ℝ) else 0) * Q2.toReal w = Q2.toReal (if P then w else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul, toReal_zero]

theorem model_abd_matches (x y w a b d : Bool) :
    modelABD model x y w a b d = noisyABD thresholdVisibility x y w a b d := by
  unfold modelABD model
  dsimp only [Model.ofAtoms]
  rw [HiddenInfluence.atomWeights_sum]
  simp_rw [toReal_indicator]
  rw [← ForcedSignalingLC4.toReal_sum]
  change Q2.toReal (seedABD x y w a b d) = _
  rw [seed_abd_matches]
  exact toReal_noisyQ2 (ForcedSignalingLC4.abd x y w a b d)

theorem model_acd_matches (x z w a c d : Bool) :
    modelACD model x z w a c d = noisyACD thresholdVisibility x z w a c d := by
  unfold modelACD model
  dsimp only [Model.ofAtoms]
  rw [HiddenInfluence.atomWeights_sum]
  simp_rw [toReal_indicator]
  rw [← ForcedSignalingLC4.toReal_sum]
  change Q2.toReal (seedACD x z w a c d) = _
  rw [seed_acd_matches]
  exact toReal_noisyQ2 (ForcedSignalingLC4.acd x z w a c d)

def diffQ2 (c : Context) (o : Recipient) : Q2 :=
  ∑ k : Seed, qmul (qrat (differenceCoeff c o (atoms k))) (weightQ2 k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_zero : ∀ c o, diffQ2 c o = 0 := by
  with_unfolding_all decide +kernel

theorem difference_zero (c : Context) (o : Recipient) :
    difference model.behavior c o = 0 := by
  rw [model, HiddenInfluence.ofAtoms_difference]
  have h := congrArg Q2.toReal (diff_zero c o)
  change Q2.toReal
      (∑ k, qmul (qrat (differenceCoeff c o (atoms k))) (weightQ2 k)) =
    Q2.toReal 0 at h
  rw [ForcedSignalingLC4.toReal_sum, ForcedSignalingLC4.toReal_zero] at h
  simpa [ForcedSignalingLC4.toReal_qmul, ForcedSignalingLC4.toReal_qrat] using h

theorem tv_zero (c : Context) : tv model.behavior c = 0 := by
  simp [tv, difference_zero]

theorem signaling_zero : model.signaling = 0 := by
  apply le_antisymm
  · exact (signaling_le_iff _ _).mpr (fun c => by simp [tv_zero])
  · exact signaling_nonnegative model

theorem matches_noisy : MatchesNoisyCluster thresholdVisibility model where
  abd := model_abd_matches
  acd := model_acd_matches

end Threshold

namespace White

abbrev Seed := Fin 56

def atoms (k : Seed) : Atom :=
  (#[0,7,11,12,18,29,34,37,41,46,49,62,66,77,80,87,91,92,97,110,115,116,
     120,127,128,135,139,140,145,146,156,159,162,165,169,174,176,179,189,
     190,197,198,200,203,211,212,216,223,224,231,235,236,240,243,253,254] :
     Array Atom)[k.val]

def weightQ2 (k : Seed) : Q2 :=
  (#[qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/8),qrat (1/8),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/8),qrat (1/8),
     qrat (1/8),qrat (1/8),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/8),qrat (1/8),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16)] : Array Q2)[k.val]

theorem weight_nonnegative (k : Seed) : 0 ≤ Q2.toReal (weightQ2 k) := by
  fin_cases k <;> norm_num [weightQ2, Q2.toReal, qrat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalsQ2 : ∀ e : Early,
    (∑ k : Seed, if early (atoms k) = e then weightQ2 k else 0) = qrat 1 := by
  with_unfolding_all decide +kernel

noncomputable def model : Model :=
  Model.ofAtoms atoms (fun k => Q2.toReal (weightQ2 k))
    weight_nonnegative
    (fun e => by
      have h := congrArg Q2.toReal (totalsQ2 e)
      rw [toReal_sum] at h
      simpa only [apply_ite, toReal_zero, toReal_qrat, Rat.cast_one] using h)

def seedABD (x y w a b d : Bool) : Q2 :=
  ∑ k : Seed,
    let o := output (atoms k) (lateOf y false)
    if early (atoms k) = earlyOf x w ∧
       o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
    then weightQ2 k else 0

def seedACD (x z w a c d : Bool) : Q2 :=
  ∑ k : Seed,
    let o := output (atoms k) (lateOf false z)
    if early (atoms k) = earlyOf x w ∧
       o.val / 8 = a.toNat ∧ o.val / 2 % 2 = c.toNat ∧ o.val % 2 = d.toNat
    then weightQ2 k else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem seed_abd_uniform : ∀ x y w a b d, seedABD x y w a b d = qrat (1/8) := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem seed_acd_uniform : ∀ x z w a c d, seedACD x z w a c d = qrat (1/8) := by
  with_unfolding_all decide +kernel

private theorem toReal_indicator (P : Prop) [Decidable P] (w : Q2) :
    (if P then (1 : ℝ) else 0) * Q2.toReal w = Q2.toReal (if P then w else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul, toReal_zero]

theorem model_abd_matches (x y w a b d : Bool) :
    modelABD model x y w a b d = noisyABD 0 x y w a b d := by
  unfold modelABD model
  dsimp only [Model.ofAtoms]
  rw [HiddenInfluence.atomWeights_sum]
  simp_rw [toReal_indicator]
  rw [← ForcedSignalingLC4.toReal_sum]
  change Q2.toReal (seedABD x y w a b d) = _
  rw [seed_abd_uniform]
  simp [noisyABD]

theorem model_acd_matches (x z w a c d : Bool) :
    modelACD model x z w a c d = noisyACD 0 x z w a c d := by
  unfold modelACD model
  dsimp only [Model.ofAtoms]
  rw [HiddenInfluence.atomWeights_sum]
  simp_rw [toReal_indicator]
  rw [← ForcedSignalingLC4.toReal_sum]
  change Q2.toReal (seedACD x z w a c d) = _
  rw [seed_acd_uniform]
  simp [noisyACD]

def diffQ2 (c : Context) (o : Recipient) : Q2 :=
  ∑ k : Seed, qmul (qrat (differenceCoeff c o (atoms k))) (weightQ2 k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_zero : ∀ c o, diffQ2 c o = 0 := by
  with_unfolding_all decide +kernel

theorem difference_zero (c : Context) (o : Recipient) :
    difference model.behavior c o = 0 := by
  rw [model, HiddenInfluence.ofAtoms_difference]
  have h := congrArg Q2.toReal (diff_zero c o)
  change Q2.toReal
      (∑ k, qmul (qrat (differenceCoeff c o (atoms k))) (weightQ2 k)) =
    Q2.toReal 0 at h
  rw [ForcedSignalingLC4.toReal_sum, ForcedSignalingLC4.toReal_zero] at h
  simpa [ForcedSignalingLC4.toReal_qmul, ForcedSignalingLC4.toReal_qrat] using h

theorem tv_zero (c : Context) : tv model.behavior c = 0 := by
  simp [tv, difference_zero]

theorem signaling_zero : model.signaling = 0 := by
  apply le_antisymm
  · exact (signaling_le_iff _ _).mpr (fun c => by simp [tv_zero])
  · exact signaling_nonnegative model

theorem matches_noisy : MatchesNoisyCluster 0 model where
  abd := model_abd_matches
  acd := model_acd_matches

end White

theorem modelABD_mix (a b : Model) (t : ℝ) (h0 h1)
    (x y w aa bb d : Bool) :
    modelABD (a.mix b t h0 h1) x y w aa bb d =
      t * modelABD a x y w aa bb d + (1-t) * modelABD b x y w aa bb d := by
  unfold modelABD Model.mix
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [mul_left_comm _ t, mul_left_comm _ (1-t)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem modelACD_mix (a b : Model) (t : ℝ) (h0 h1)
    (x z w aa cc d : Bool) :
    modelACD (a.mix b t h0 h1) x z w aa cc d =
      t * modelACD a x z w aa cc d + (1-t) * modelACD b x z w aa cc d := by
  unfold modelACD Model.mix
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [mul_left_comm _ t, mul_left_comm _ (1-t)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem noisyABD_affine (p q t : ℝ) :
    noisyABD (t*p + (1-t)*q) =
      fun x y w a b d =>
        t * noisyABD p x y w a b d + (1-t) * noisyABD q x y w a b d := by
  funext x y w a b d
  unfold noisyABD
  ring

theorem noisyACD_affine (p q t : ℝ) :
    noisyACD (t*p + (1-t)*q) =
      fun x z w a c d =>
        t * noisyACD p x z w a c d + (1-t) * noisyACD q x z w a c d := by
  funext x z w a c d
  unfold noisyACD
  ring

theorem MatchesNoisyCluster.mix {a b : Model} {p q t : ℝ}
    (ha : MatchesNoisyCluster p a) (hb : MatchesNoisyCluster q b)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    MatchesNoisyCluster (t*p + (1-t)*q) (a.mix b t h0 h1) := by
  constructor
  · intro x y w aa bb d
    rw [modelABD_mix, ha.abd, hb.abd]
    simpa [noisyABD_affine]
  · intro x z w aa cc d
    rw [modelACD_mix, ha.acd, hb.acd]
    simpa [noisyACD_affine]

noncomputable def targetMarginalScoreReal : ℝ :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) *
        Q2.toReal (ForcedSignalingLC4.abd false false true a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) *
        Q2.toReal (ForcedSignalingLC4.abd false true true a b d)) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) *
        Q2.toReal (ForcedSignalingLC4.abd true false false a b d)) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) *
        Q2.toReal (ForcedSignalingLC4.abd true true false a b d)) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn cc * sgn d : ℤ) *
        Q2.toReal (ForcedSignalingLC4.acd true false false a cc d)) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn a * sgn cc * sgn d : ℤ) *
        Q2.toReal (ForcedSignalingLC4.acd false true true a cc d))

theorem targetMarginalScoreReal_value :
    targetMarginalScoreReal = 4 + 2 * Real.sqrt 2 := by
  have h := ForcedSignalingTheorem2.matches_score
    ForcedSignalingTheorem2.witness_matches
  rw [← ForcedSignalingTheorem2.marginalScore_eq_score] at h
  unfold ForcedSignalingTheorem2.marginalScore at h
  simp_rw [ForcedSignalingTheorem2.witness_matches.abd,
    ForcedSignalingTheorem2.witness_matches.acd] at h
  exact h

noncomputable def noisyMarginalScore (p : ℝ) : ℝ :=
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) * noisyABD p false false true a b d) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b : ℤ) * noisyABD p false true true a b d) +
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) * noisyABD p true false false a b d) -
  (∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      (sgn a * sgn b * sgn d : ℤ) * noisyABD p true true false a b d) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn cc * sgn d : ℤ) * noisyACD p true false false a cc d) +
  2 * (∑ a : Bool, ∑ cc : Bool, ∑ d : Bool,
      (sgn a * sgn cc * sgn d : ℤ) * noisyACD p false true true a cc d)

theorem noisyMarginalScore_eq (p : ℝ) :
    noisyMarginalScore p = p * targetMarginalScoreReal := by
  unfold noisyMarginalScore targetMarginalScoreReal noisyABD noisyACD
  simp only [Fintype.sum_bool]
  simp [sgn]
  ring

/-- The S4 score forced by the noisy no-blind-pair marginals. -/
theorem matches_score {p : ℝ} {m : Model} (h : MatchesNoisyCluster p m) :
    score m.behavior = p * (4 + 2 * Real.sqrt 2) := by
  rw [← ForcedSignalingTheorem2.marginalScore_eq_score]
  change ForcedSignalingTheorem2.marginalScore m = _
  unfold ForcedSignalingTheorem2.marginalScore
  simp_rw [h.abd, h.acd]
  change noisyMarginalScore p = _
  rw [noisyMarginalScore_eq, targetMarginalScoreReal_value]

theorem lower_bound {p : ℝ} {m : Model} (h : MatchesNoisyCluster p m) :
    max 0 ((p * (4 + 2 * Real.sqrt 2) - 6) / 8) ≤ m.signaling := by
  have hb : Within m.behavior m.signaling :=
    (signaling_le_iff m m.signaling).mp le_rfl
  have hs := score_bound m m.signaling hb
  rw [matches_score h] at hs
  apply max_le
  · exact signaling_nonnegative m
  · linarith

/-- Exact forced-signaling value predicted for a white-noise visibility p. -/
noncomputable def sigma (p : ℝ) : ℝ :=
  max 0 ((p * (4 + 2 * Real.sqrt 2) - 6) / 8)

theorem sigma_at_zero : sigma 0 = 0 := by
  unfold sigma
  norm_num

theorem sigma_at_one :
    sigma 1 = (Real.sqrt 2 - 1) / 4 := by
  unfold sigma
  have h : 0 ≤ (Real.sqrt 2 - 1) / 4 := by
    nlinarith [ForcedSignalingLC4Witness.sqrtTwo_ge_one]
  rw [max_eq_right]
  · ring
  · nlinarith [ForcedSignalingLC4Witness.sqrtTwo_ge_one]


theorem mix_difference_zero (a b : Model) (t : ℝ) (h0 h1)
    (ha : ∀ c o, difference a.behavior c o = 0)
    (hb : ∀ c o, difference b.behavior c o = 0)
    (c : Context) (o : Recipient) :
    difference (a.mix b t h0 h1).behavior c o = 0 := by
  rw [HiddenInfluence.mix_difference, ha, hb]
  ring

theorem mix_signaling_zero (a b : Model) (t : ℝ) (h0 h1)
    (ha : ∀ c o, difference a.behavior c o = 0)
    (hb : ∀ c o, difference b.behavior c o = 0) :
    (a.mix b t h0 h1).signaling = 0 := by
  apply le_antisymm
  · apply (signaling_le_iff _ _).mpr
    intro c
    unfold tv
    simp_rw [mix_difference_zero a b t h0 h1 ha hb]
    simp
  · exact signaling_nonnegative _

noncomputable def belowWeight (p : ℝ) : ℝ :=
  p / thresholdVisibility

theorem belowWeight_nonnegative (p : ℝ) (hp0 : 0 ≤ p) :
    0 ≤ belowWeight p := by
  unfold belowWeight
  exact div_nonneg hp0 (le_of_lt thresholdVisibility_pos)

theorem belowWeight_le_one (p : ℝ) (hp1 : p ≤ thresholdVisibility) :
    belowWeight p ≤ 1 := by
  unfold belowWeight
  exact (div_le_one thresholdVisibility_pos).2 hp1

noncomputable def belowModel (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ thresholdVisibility) : Model :=
  Threshold.model.mix White.model (belowWeight p)
    (belowWeight_nonnegative p hp0) (belowWeight_le_one p hp1)

theorem belowModel_matches (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ thresholdVisibility) :
    MatchesNoisyCluster p (belowModel p hp0 hp1) := by
  have hm := MatchesNoisyCluster.mix
    Threshold.matches_noisy White.matches_noisy
    (belowWeight_nonnegative p hp0) (belowWeight_le_one p hp1)
  have hp :
      belowWeight p * thresholdVisibility +
          (1-belowWeight p) * 0 = p := by
    unfold belowWeight
    field_simp [ne_of_gt thresholdVisibility_pos]
    ring
  rw [hp] at hm
  exact hm

theorem belowModel_signaling (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ thresholdVisibility) :
    (belowModel p hp0 hp1).signaling = 0 := by
  exact mix_signaling_zero Threshold.model White.model (belowWeight p)
    (belowWeight_nonnegative p hp0) (belowWeight_le_one p hp1)
    Threshold.difference_zero White.difference_zero

theorem sigma_eq_zero_of_le_threshold (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ thresholdVisibility) :
    sigma p = 0 := by
  unfold sigma
  rw [max_eq_left]
  have hS : 0 < 4 + 2 * Real.sqrt 2 := by positivity
  have h := thresholdVisibility_score
  nlinarith

noncomputable def aboveWeight (p : ℝ) : ℝ :=
  (p - thresholdVisibility) / (1 - thresholdVisibility)

theorem aboveWeight_nonnegative (p : ℝ) (hp : thresholdVisibility ≤ p) :
    0 ≤ aboveWeight p := by
  unfold aboveWeight
  exact div_nonneg (sub_nonneg.mpr hp)
    (sub_nonneg.mpr (le_of_lt thresholdVisibility_lt_one))

theorem aboveWeight_le_one (p : ℝ) (hp : p ≤ 1) :
    aboveWeight p ≤ 1 := by
  unfold aboveWeight
  exact (div_le_one (sub_pos.mpr thresholdVisibility_lt_one)).2 (by linarith)

noncomputable def aboveModel (p : ℝ)
    (hp0 : thresholdVisibility ≤ p) (hp1 : p ≤ 1) : Model :=
  ForcedSignalingLC4Witness.model.mix Threshold.model (aboveWeight p)
    (aboveWeight_nonnegative p hp0) (aboveWeight_le_one p hp1)

theorem witness_matches_noisy_one :
    MatchesNoisyCluster 1 ForcedSignalingLC4Witness.model := by
  constructor
  · intro x y w a b d
    simpa [noisyABD] using
      ForcedSignalingLC4Witness.model_abd_matches x y w a b d
  · intro x z w a cc d
    simpa [noisyACD] using
      ForcedSignalingLC4Witness.model_acd_matches x z w a cc d

theorem aboveModel_matches (p : ℝ)
    (hp0 : thresholdVisibility ≤ p) (hp1 : p ≤ 1) :
    MatchesNoisyCluster p (aboveModel p hp0 hp1) := by
  have hm := MatchesNoisyCluster.mix
    witness_matches_noisy_one Threshold.matches_noisy
    (aboveWeight_nonnegative p hp0) (aboveWeight_le_one p hp1)
  have hp :
      aboveWeight p * 1 +
          (1-aboveWeight p) * thresholdVisibility = p := by
    unfold aboveWeight
    field_simp [ne_of_gt (sub_pos.mpr thresholdVisibility_lt_one)]
    ring
  rw [hp] at hm
  exact hm

theorem aboveModel_tv (p : ℝ)
    (hp0 : thresholdVisibility ≤ p) (hp1 : p ≤ 1) (c : Context) :
    tv (aboveModel p hp0 hp1).behavior c =
      aboveWeight p * tv ForcedSignalingLC4Witness.model.behavior c := by
  unfold aboveModel tv
  simp_rw [HiddenInfluence.mix_difference,
    Threshold.difference_zero, mul_zero, add_zero,
    abs_mul, abs_of_nonneg (aboveWeight_nonnegative p hp0)]
  rw [← Finset.mul_sum]
  ring

theorem aboveModel_signaling (p : ℝ)
    (hp0 : thresholdVisibility ≤ p) (hp1 : p ≤ 1) :
    (aboveModel p hp0 hp1).signaling =
      aboveWeight p * ForcedSignalingLC4Witness.targetDelta := by
  apply le_antisymm
  · apply (signaling_le_iff _ _).mpr
    intro c
    rw [aboveModel_tv]
    exact mul_le_mul_of_nonneg_left
      (ForcedSignalingLC4Witness.budget c)
      (aboveWeight_nonnegative p hp0)
  · have h := tv_le_signaling (aboveModel p hp0 hp1) 5
    rw [aboveModel_tv, ForcedSignalingLC4Witness.tv_exact] at h
    norm_num at h
    exact h

theorem sigma_eq_linear_of_threshold_le (p : ℝ)
    (hp0 : thresholdVisibility ≤ p) :
    sigma p = (p * (4 + 2 * Real.sqrt 2) - 6) / 8 := by
  unfold sigma
  rw [max_eq_right]
  have hS : 0 < 4 + 2 * Real.sqrt 2 := by positivity
  have h := thresholdVisibility_score
  nlinarith

theorem aboveModel_signaling_eq_sigma (p : ℝ)
    (hp0 : thresholdVisibility ≤ p) (hp1 : p ≤ 1) :
    (aboveModel p hp0 hp1).signaling = sigma p := by
  rw [aboveModel_signaling, sigma_eq_linear_of_threshold_le p hp0]
  have hT := thresholdVisibility_score
  have hden : 1 - thresholdVisibility ≠ 0 :=
    ne_of_gt (sub_pos.mpr thresholdVisibility_lt_one)
  have hdelta :
      ForcedSignalingLC4Witness.targetDelta =
        ((4 + 2 * Real.sqrt 2) - 6) / 8 := by
    rw [ForcedSignalingTheorem2.targetDelta_value]
    ring
  rw [hdelta]
  unfold aboveWeight
  field_simp [hden]
  nlinarith

/-- Exact forced-signaling curve for the white-noise LC4 family. -/
theorem exact_curve (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ m : Model, MatchesNoisyCluster p m → sigma p ≤ m.signaling) ∧
    ∃ m : Model, MatchesNoisyCluster p m ∧ m.signaling = sigma p := by
  constructor
  · intro m hm
    exact lower_bound hm
  · by_cases h : p ≤ thresholdVisibility
    · refine ⟨belowModel p hp0 h, belowModel_matches p hp0 h, ?_⟩
      rw [belowModel_signaling, sigma_eq_zero_of_le_threshold p hp0 h]
    · have hge : thresholdVisibility ≤ p := le_of_not_ge h
      refine ⟨aboveModel p hge hp1, aboveModel_matches p hge hp1,
        aboveModel_signaling_eq_sigma p hge hp1⟩

theorem sigma_ninety_percent :
    sigma (9/10) = (9 * Real.sqrt 2 - 12) / 40 := by
  rw [sigma_eq_linear_of_threshold_le]
  · ring
  · rw [thresholdVisibility_value]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith

theorem sigma_ninetyfive_percent :
    sigma (19/20) = (19 * Real.sqrt 2 - 22) / 80 := by
  rw [sigma_eq_linear_of_threshold_le]
  · ring
  · rw [thresholdVisibility_value]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith


/-- Noisy-LC4 matching stated directly for a finite stochastic
conditional-local model via its proved-equivalent deterministic refinement. -/
def StochasticMatchesNoisyCluster {Ω : Type} [Fintype Ω]
    (p : ℝ) (m : StochasticModel Ω) : Prop :=
  MatchesNoisyCluster p m.determinize

theorem stochastic_lower_bound {Ω : Type} [Fintype Ω]
    {p : ℝ} {m : StochasticModel Ω}
    (h : StochasticMatchesNoisyCluster p m) :
    sigma p ≤ m.signaling := by
  simpa [sigma, StochasticModel.signaling] using lower_bound h

/-- Exact white-noise forced-signaling curve for the finite stochastic
conditional-local class, with an explicit stochastic attaining representative. -/
theorem exact_curve_stochastic (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ (Ω : Type) [Fintype Ω] (m : StochasticModel Ω),
      StochasticMatchesNoisyCluster p m → sigma p ≤ m.signaling) ∧
    ∃ m : StochasticModel Strategy,
      StochasticMatchesNoisyCluster p m ∧ m.signaling = sigma p := by
  constructor
  · intro Ω _ m hm
    exact stochastic_lower_bound hm
  · obtain ⟨m, hm, hs⟩ := (exact_curve p hp0 hp1).2
    let sm : StochasticModel Strategy :=
      StochasticModel.ofStrategies m.toStrategies
    have hmatch : StochasticMatchesNoisyCluster p sm := by
      constructor
      · intro x y w a b d
        unfold sm modelABD
        simp_rw [m.stochastic_roundtrip_weight]
        exact hm.abd x y w a b d
      · intro x z w a cc d
        unfold sm modelACD
        simp_rw [m.stochastic_roundtrip_weight]
        exact hm.acd x z w a cc d
    have hsig : sm.signaling = sigma p := by
      unfold sm
      rw [m.stochastic_roundtrip_signaling]
      exact hs
    exact ⟨sm, hmatch, hsig⟩

end
end OntologySeparation.NoisyLC4
