import OntologySeparation.Experiments.ForcedSignalingDirectional
import OntologySeparation.Experiments.ForcedSignalingLC4Witness

namespace OntologySeparation.ForcedSignalingCertificateModel
noncomputable section
open scoped BigOperators
open HiddenInfluence
open ForcedSignalingLC4
open ForcedSignalingLC4Witness

abbrev WeightQ2 := Atom → Q2

theorem sqrtTwo_ge_one : (1 : ℝ) ≤ Real.sqrt 2 :=
  ForcedSignalingLC4Witness.sqrtTwo_ge_one

theorem sqrtTwo_le_two : Real.sqrt 2 ≤ (2 : ℝ) :=
  ForcedSignalingLC4Witness.sqrtTwo_le_two

def AllowedWeight (w : Q2) : Prop :=
  w = 0 ∨
  w = qrat (1/8) ∨
  w = q (-1/8) (1/8) ∨
  w = q (1/8) (-1/16) ∨
  w = q 0 (1/16) ∨
  w = q (-1/16) (1/16) ∨
  w = qrat (1/16)

theorem allowedWeight_nonnegative {w : Q2} (h : AllowedWeight w) :
    0 ≤ Q2.toReal w := by
  rcases h with h | h | h | h | h | h | h <;> rw [h] <;>
    simp [Q2.toReal, q, qrat] <;>
    nlinarith [sqrtTwo_ge_one, sqrtTwo_le_two, Real.sqrt_nonneg (2 : ℝ)]

noncomputable def modelOfWeight (w : WeightQ2)
    (hn : ∀ j, 0 ≤ Q2.toReal (w j))
    (ht : ∀ e : Early, (∑ j, if early j = e then w j else 0) = qrat 1) : Model where
  weight j := Q2.toReal (w j)
  nonnegative := hn
  normalized e := by
    have h := congrArg Q2.toReal (ht e)
    rw [ForcedSignalingLC4.toReal_sum] at h
    simpa only [apply_ite, ForcedSignalingLC4.toReal_zero,
      ForcedSignalingLC4.toReal_qrat, Rat.cast_one] using h

def abdQ2 (w : WeightQ2) (x y ww a b d : Bool) : Q2 :=
  ∑ j : Atom,
    let o := output j (lateOf y false)
    if early j = earlyOf x ww ∧
       o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat
    then w j else 0

def acdQ2 (w : WeightQ2) (x z ww a c d : Bool) : Q2 :=
  ∑ j : Atom,
    let o := output j (lateOf false z)
    if early j = earlyOf x ww ∧
       o.val / 8 = a.toNat ∧ o.val / 2 % 2 = c.toNat ∧ o.val % 2 = d.toNat
    then w j else 0

private theorem toReal_indicator (P : Prop) [Decidable P] (w : Q2) :
    (if P then (1 : ℝ) else 0) * Q2.toReal w =
      Q2.toReal (if P then w else 0) := by
  by_cases h : P <;> simp [h]

theorem modelABD_eq (w : WeightQ2) (hn ht) (x y ww a b d : Bool) :
    modelABD (modelOfWeight w hn ht) x y ww a b d =
      Q2.toReal (abdQ2 w x y ww a b d) := by
  unfold modelABD modelOfWeight abdQ2
  rw [ForcedSignalingLC4.toReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  exact toReal_indicator _ _

theorem modelACD_eq (w : WeightQ2) (hn ht) (x z ww a c d : Bool) :
    modelACD (modelOfWeight w hn ht) x z ww a c d =
      Q2.toReal (acdQ2 w x z ww a c d) := by
  unfold modelACD modelOfWeight acdQ2
  rw [ForcedSignalingLC4.toReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  exact toReal_indicator _ _

def diffQ2 (w : WeightQ2) (c : Context) (o : Recipient) : Q2 :=
  ∑ j : Atom, qmul (qrat (differenceCoeff c o j)) (w j)

theorem difference_eq_toReal (w : WeightQ2) (hn ht) (c : Context) (o : Recipient) :
    difference (modelOfWeight w hn ht).behavior c o =
      Q2.toReal (diffQ2 w c o) := by
  rw [difference_eq]
  unfold modelOfWeight diffQ2
  rw [ForcedSignalingLC4.toReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [ForcedSignalingLC4.toReal_qmul, ForcedSignalingLC4.toReal_qrat]

/-- Six proper recipient subsets of a three-party record: three singles then
three pairs. The result lives in Fin 4; single-party projections use only 0,1. -/
def properProject (r0 r1 r2 : Fin 2) (s : Fin 6) : Fin 4 :=
  ⟨if s.val = 0 then r0.val
    else if s.val = 1 then r1.val
    else if s.val = 2 then r2.val
    else if s.val = 3 then 2*r0.val+r1.val
    else if s.val = 4 then 2*r0.val+r2.val
    else 2*r1.val+r2.val, by
      have h0 := r0.isLt
      have h1 := r1.isLt
      have h2 := r2.isLt
      omega⟩

def projectAProper (s : Fin 6) (o : Outcome) : Fin 4 :=
  properProject
    ⟨o.val / 4 % 2, Nat.mod_lt _ (by omega)⟩
    ⟨o.val / 2 % 2, Nat.mod_lt _ (by omega)⟩
    ⟨o.val % 2, Nat.mod_lt _ (by omega)⟩ s

def projectDProper (s : Fin 6) (o : Outcome) : Fin 4 :=
  properProject
    ⟨o.val / 8, by omega⟩
    ⟨o.val / 4 % 2, Nat.mod_lt _ (by omega)⟩
    ⟨o.val / 2 % 2, Nat.mod_lt _ (by omega)⟩ s

noncomputable def marginal4 (p : Behavior interface) (e : Early) (l : Late)
    (project : Outcome → Fin 4) (o : Fin 4) : ℝ :=
  mean p e l (fun full => if project full = o then 1 else 0)

def properMarginalQ2 (w : WeightQ2) (e : Early) (l : Late)
    (project : Outcome → Fin 4) (o : Fin 4) : Q2 :=
  ∑ j : Atom,
    if early j = e ∧ project (output j l) = o then w j else 0

theorem marginal4_eq_toReal (w : WeightQ2) (hn ht) (e : Early) (l : Late)
    (project : Outcome → Fin 4) (o : Fin 4) :
    marginal4 (modelOfWeight w hn ht).behavior e l project o =
      Q2.toReal (properMarginalQ2 w e l project o) := by
  unfold marginal4 properMarginalQ2
  rw [mean_eq, ForcedSignalingLC4.toReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : early j = e ∧ project (output j l) = o <;>
    simp [h, modelOfWeight]

end
end OntologySeparation.ForcedSignalingCertificateModel
