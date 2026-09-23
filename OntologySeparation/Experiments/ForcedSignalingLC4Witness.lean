import OntologySeparation.Experiments.ForcedSignalingLC4
import OntologySeparation.Operational.HiddenInfluenceWitness

/-!
# Exact physical LC4 hidden-influence witness

This file ports only the 59 nonzero hidden-response weights from the exact
Theorem-2 primal certificate.  The LP absolute-value slack variables are not
imported: Lean recomputes the observable recipient differences and total
variation directly from the resulting physical HiddenInfluence.Model.

The seed mixture is checked against the 128 exact LC4 no-blind-pair marginals
defined from the cluster state in ForcedSignalingLC4.
-/

namespace OntologySeparation.ForcedSignalingLC4Witness
noncomputable section

open scoped BigOperators
open ForcedSignalingLC4
open HiddenInfluence

abbrev Seed := Fin 59

def atoms (k : Seed) : Atom :=
  (#[0,2,6,10,17,19,29,34,44,46,53,57,61,63,64,65,76,82,83,95,
     102,106,110,111,117,121,124,125,128,136,138,140,145,149,151,
     157,160,164,166,172,181,185,187,193,197,202,206,210,215,216,
     221,224,230,233,239,243,244,251,252] : Array Atom)[k.val]

def weightQ2 (k : Seed) : Q2 :=
  (#[qrat (1/8),q (-1/8) (1/8),q (1/8) (-1/16),q (1/8) (-1/16),
     q 0 (1/16),qrat (1/8),q (1/8) (-1/16),q (1/8) (-1/16),
     qrat (1/8),q 0 (1/16),q (1/8) (-1/16),q (1/8) (-1/16),
     q (-1/8) (1/8),qrat (1/8),q 0 (1/16),qrat (1/8),
     q (1/8) (-1/16),qrat (1/8),q 0 (1/16),q (1/8) (-1/16),
     q (1/8) (-1/16),q (1/8) (-1/16),q (-1/8) (1/8),qrat (1/8),
     q (1/8) (-1/16),q (1/8) (-1/16),qrat (1/8),q (-1/8) (1/8),
     q (1/8) (-1/16),q (-1/8) (1/8),qrat (1/8),q (1/8) (-1/16),
     q (1/8) (-1/16),q (-1/8) (1/8),qrat (1/8),q (1/8) (-1/16),
     q (1/8) (-1/16),q (-1/8) (1/8),qrat (1/8),q (1/8) (-1/16),
     q (1/8) (-1/16),q 0 (1/16),qrat (1/8),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),
     qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16),qrat (1/16)] : Array Q2)[k.val]

def targetDeltaQ2 : Q2 := q (-1/4) (1/4)
noncomputable def targetDelta : ℝ := Q2.toReal targetDeltaQ2

theorem sqrtTwo_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

theorem sqrtTwo_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

set_option maxRecDepth 100000 in
private theorem weight_cases : ∀ k : Seed,
    weightQ2 k = qrat (1/8) ∨
    weightQ2 k = q (-1/8) (1/8) ∨
    weightQ2 k = q (1/8) (-1/16) ∨
    weightQ2 k = q 0 (1/16) ∨
    weightQ2 k = qrat (1/16) := by
  with_unfolding_all decide +kernel

theorem weight_nonnegative (k : Seed) : 0 ≤ Q2.toReal (weightQ2 k) := by
  rcases weight_cases k with h | h | h | h | h <;> rw [h] <;>
    simp [Q2.toReal, q, qrat] <;>
    nlinarith [sqrtTwo_ge_one, sqrtTwo_le_two, Real.sqrt_nonneg (2 : ℝ)]

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

def earlyOf (x w : Bool) : Early :=
  ⟨2*x.toNat + w.toNat, by
    have hx := Bool.toNat_le x
    have hw := Bool.toNat_le w
    omega⟩

def lateOf (y z : Bool) : Late :=
  ⟨2*y.toNat + z.toNat, by
    have hy := Bool.toNat_le y
    have hz := Bool.toNat_le z
    omega⟩

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
    ∀ x y w a b d, seedABD x y w a b d = ForcedSignalingLC4.abd x y w a b d := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_acd_matches :
    ∀ x z w a c d, seedACD x z w a c d = ForcedSignalingLC4.acd x z w a c d := by
  with_unfolding_all decide +kernel

noncomputable def modelABD (m : Model) (x y w a b d : Bool) : ℝ :=
  ∑ j : Atom,
    let o := output j (lateOf y false)
    (if early j = earlyOf x w ∧
        o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
     then 1 else 0) * m.weight j

noncomputable def modelACD (m : Model) (x z w a c d : Bool) : ℝ :=
  ∑ j : Atom,
    let o := output j (lateOf false z)
    (if early j = earlyOf x w ∧
        o.val / 8 = a.toNat ∧ o.val / 2 % 2 = c.toNat ∧ o.val % 2 = d.toNat
     then 1 else 0) * m.weight j

private theorem toReal_indicator (P : Prop) [Decidable P] (w : Q2) :
    (if P then (1 : ℝ) else 0) * Q2.toReal w = Q2.toReal (if P then w else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul, toReal_zero]

theorem model_abd_matches (x y w a b d : Bool) :
    modelABD model x y w a b d =
      Q2.toReal (ForcedSignalingLC4.abd x y w a b d) := by
  unfold modelABD model
  dsimp only [Model.ofAtoms]
  rw [HiddenInfluence.atomWeights_sum]
  rw [← seed_abd_matches]
  unfold seedABD
  rw [ForcedSignalingLC4.toReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  exact toReal_indicator _ _

theorem model_acd_matches (x z w a c d : Bool) :
    modelACD model x z w a c d =
      Q2.toReal (ForcedSignalingLC4.acd x z w a c d) := by
  unfold modelACD model
  dsimp only [Model.ofAtoms]
  rw [HiddenInfluence.atomWeights_sum]
  rw [← seed_acd_matches]
  unfold seedACD
  rw [ForcedSignalingLC4.toReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  exact toReal_indicator _ _

def diffQ2 (c : Context) (o : Recipient) : Q2 :=
  ∑ k : Seed,
    ForcedSignalingLC4.qmul
      (ForcedSignalingLC4.qrat (differenceCoeff c o (atoms k)))
      (weightQ2 k)

theorem difference_exact (c : Context) (o : Recipient) :
    difference model.behavior c o = Q2.toReal (diffQ2 c o) := by
  rw [model, HiddenInfluence.ofAtoms_difference]
  simp [diffQ2, ForcedSignalingLC4.toReal_sum, ForcedSignalingLC4.toReal_qmul]

def epsilonQ2 : Q2 := q (-1/16) (1/16)

set_option maxRecDepth 100000 in
private theorem diff_shape : ∀ c o,
    diffQ2 c o = 0 ∨ diffQ2 c o = epsilonQ2 ∨ diffQ2 c o = -epsilonQ2 := by
  with_unfolding_all decide +kernel

theorem epsilon_nonnegative : 0 ≤ Q2.toReal epsilonQ2 := by
  simp [epsilonQ2, Q2.toReal, q]
  nlinarith [sqrtTwo_ge_one]

theorem targetDelta_nonnegative : 0 ≤ targetDelta := by
  simp [targetDelta, targetDeltaQ2, Q2.toReal, q]
  nlinarith [sqrtTwo_ge_one]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_active : ∀ c o,
    if c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14 then
      diffQ2 c o = epsilonQ2 ∨ diffQ2 c o = -epsilonQ2
    else diffQ2 c o = 0 := by
  with_unfolding_all decide +kernel

private theorem abs_difference_exact (c : Context) (o : Recipient) :
    |difference model.behavior c o| =
      if c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14
      then Q2.toReal epsilonQ2 else 0 := by
  have h := diff_active c o
  by_cases hc : c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14
  · simp only [hc, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [difference_exact, h, abs_of_nonneg epsilon_nonnegative]
    · rw [difference_exact, h]
      have hn : Q2.toReal (-epsilonQ2) = -Q2.toReal epsilonQ2 := by
        simp [Q2.toReal]
        ring
      rw [hn, abs_neg, abs_of_nonneg epsilon_nonnegative]
  · simp only [hc, ↓reduceIte] at h ⊢
    rw [difference_exact, h]
    simp

/-- The certificate model has exactly the four active comparisons identified by
the exact Theorem-2 verifier; all other recipient TVs vanish. -/
theorem tv_exact (c : Context) :
    tv model.behavior c =
      if c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14
      then targetDelta else 0 := by
  unfold tv
  simp_rw [abs_difference_exact]
  by_cases hc : c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14
  · simp [hc, epsilonQ2, targetDelta, targetDeltaQ2, Q2.toReal, q]
    ring
  · simp [hc]

theorem budget : Within model.behavior targetDelta := by
  intro c
  rw [tv_exact]
  split <;> simp_all [targetDelta_nonnegative]

theorem signaling_exact : model.signaling = targetDelta := by
  apply le_antisymm ((signaling_le_iff _ _).mpr budget)
  have h := tv_le_signaling model 5
  rw [tv_exact] at h
  norm_num at h
  exact h

end
end OntologySeparation.ForcedSignalingLC4Witness
