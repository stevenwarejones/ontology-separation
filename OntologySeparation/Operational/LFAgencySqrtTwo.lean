import OntologySeparation.Experiments.LFAgencyAngleOptimality
import Mathlib.Tactic

/-!
# Direct physical bridge for the relaxed-CHSH Local-Agency bound

The certificate behind the sqrt(2) result is a relaxed CHSH inequality.  Rather
than re-encoding an LF joint table into a large finite LP, this module proves the
physical statement directly from:

* exact friend readout;
* setting-independent absolute records;
* the two record-revealed total-variation distances.

For the readout setting 0 and Wigner setting 2,

  CHSH <= 2 + 2 (TV_A + TV_B).

Hence if both TVs are at most delta, CHSH <= 2 + 4 delta.
-/

namespace OntologySeparation.LFAgencyRelaxation.SqrtTwoPhysical
noncomputable section

open LFJoint
open scoped BigOperators

private def sgn (b : Bool) : ℝ := RealQuantum.sign b

private def recCorr (r : Record) : ℝ := sgn r.1 * sgn r.2
private def recBobCorr (r : Record) (b : Bool) : ℝ := sgn r.1 * sgn b
private def aliceRecCorr (r : Record) (a : Bool) : ℝ := sgn a * sgn r.2
private def outCorr (a b : Bool) : ℝ := sgn a * sgn b

private theorem sign_abs (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn, RealQuantum.sign]

private theorem corr_abs_rec (r : Record) : |recCorr r| = 1 := by
  rcases r with ⟨c,d⟩
  simp [recCorr, sign_abs]

private theorem corr_abs_rb (r : Record) (b : Bool) : |recBobCorr r b| = 1 := by
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;> cases b <;> simp [recBobCorr, sgn, RealQuantum.sign]

private theorem corr_abs_ar (r : Record) (a : Bool) : |aliceRecCorr r a| = 1 := by
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;> cases a <;> simp [aliceRecCorr, sgn, RealQuantum.sign]

private theorem corr_abs_out (a b : Bool) : |outCorr a b| = 1 := by
  cases a <;> cases b <;> simp [outCorr, sgn, RealQuantum.sign]

/-- A bounded observable changes by at most twice total variation. -/
theorem weighted_difference_le_tv
    {α : Type} [Fintype α] (p q f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    (∑ x, f x * p x) - (∑ x, f x * q x) ≤
      ∑ x, |p x - q x| := by
  calc
    (∑ x, f x * p x) - (∑ x, f x * q x)
        = ∑ x, (f x * p x - f x * q x) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ x, f x * (p x - q x) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ ≤ ∑ x, |p x - q x| := by
      apply Finset.sum_le_sum
      intro x _
      calc
        f x * (p x - q x) ≤ |f x * (p x - q x)| := le_abs_self _
        _ = |f x| * |p x - q x| := abs_mul _ _
        _ ≤ 1 * |p x - q x| := by
          exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
        _ = |p x - q x| := one_mul _

private theorem wrongA_zero (j : AbsoluteEventTable) (hr : Readable j)
    (r : Record) (y : Fin 3) (b : Bool) :
    j.prob (0,y) r (!r.1,b) = 0 := by
  have hread := hr.1 r y
  have hn0 := j.nonneg (0,y) r (!r.1,false)
  have hn1 := j.nonneg (0,y) r (!r.1,true)
  unfold LFJoint.Table.mass at hread
  rw [Fintype.sum_prod_type] at hread
  simp only [Fintype.sum_bool] at hread
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;> cases b <;>
    simp only [Bool.not_false, Bool.not_true] at hread hn0 hn1 ⊢ <;>
    linarith

private theorem wrongB_zero (j : AbsoluteEventTable) (hr : Readable j)
    (r : Record) (x : Fin 3) (a : Bool) :
    j.prob (x,0) r (a,!r.2) = 0 := by
  have hread := hr.2 r x
  have hn0 := j.nonneg (x,0) r (false,!r.2)
  have hn1 := j.nonneg (x,0) r (true,!r.2)
  unfold LFJoint.Table.mass at hread
  rw [Fintype.sum_prod_type] at hread
  simp only [Fintype.sum_bool] at hread
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;> cases a <;>
    simp only [Bool.not_false, Bool.not_true] at hread hn0 hn1 ⊢ <;>
    linarith

private theorem corr00_as_records (j : AbsoluteEventTable) (hr : Readable j) :
    RealQuantum.correlator j.behavior 0 0 =
      ∑ r : Record, recCorr r * j.mass (0,0) r := by
  change (∑ o : Bool × Bool,
    RealQuantum.sign o.1 * RealQuantum.sign o.2 *
      ∑ r : Record, j.prob (0,0) r o) =
    ∑ r : Record, recCorr r * j.mass (0,0) r)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;>
    simp [recCorr, sgn, RealQuantum.sign, LFJoint.Table.mass,
      Fintype.sum_prod_type, wrongA_zero j hr, wrongB_zero j hr] <;> ring

private theorem corr02_as_recordBob (j : AbsoluteEventTable) (hr : Readable j) :
    RealQuantum.correlator j.behavior 0 2 =
      ∑ r : Record, ∑ b : Bool, recBobCorr r b * recordBob j 0 2 r b := by
  change (∑ o : Bool × Bool,
    RealQuantum.sign o.1 * RealQuantum.sign o.2 *
      ∑ r : Record, j.prob (0,2) r o) =
    ∑ r : Record, ∑ b : Bool, recBobCorr r b * recordBob j 0 2 r b)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;>
    simp [recBobCorr, sgn, RealQuantum.sign, Fintype.sum_prod_type,
      wrongA_zero j hr] <;> ring

private theorem corr20_as_recordAlice (j : AbsoluteEventTable) (hr : Readable j) :
    RealQuantum.correlator j.behavior 2 0 =
      ∑ r : Record, ∑ a : Bool, aliceRecCorr r a * recordAlice j 2 0 r a := by
  change (∑ o : Bool × Bool,
    RealQuantum.sign o.1 * RealQuantum.sign o.2 *
      ∑ r : Record, j.prob (2,0) r o) =
    ∑ r : Record, ∑ a : Bool, aliceRecCorr r a * recordAlice j 2 0 r a)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;>
    simp [aliceRecCorr, sgn, RealQuantum.sign, Fintype.sum_prod_type,
      wrongB_zero j hr] <;> ring

private theorem corr22_as_joint (j : AbsoluteEventTable) :
    RealQuantum.correlator j.behavior 2 2 =
      ∑ r : Record, ∑ a : Bool, ∑ b : Bool,
        outCorr a b * j.prob (2,2) r (a,b) := by
  change (∑ o : Bool × Bool,
    RealQuantum.sign o.1 * RealQuantum.sign o.2 *
      ∑ r : Record, j.prob (2,2) r o) =
    ∑ r : Record, ∑ a : Bool, ∑ b : Bool,
      outCorr a b * j.prob (2,2) r (a,b))
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type]
  rfl

private theorem record_mass_at_22 (j : AbsoluteEventTable)
    (hi : IndependentRecords j) (r : Record) :
    j.mass (0,0) r = j.mass (2,2) r := by
  exact hi (0,0) (2,2) r

private theorem recordBob22_mass (j : AbsoluteEventTable) (r : Record) :
    ∑ b : Bool, recordBob j 2 2 r b = j.mass (2,2) r := by
  unfold recordBob LFJoint.Table.mass
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (fun o : Bool × Bool => j.prob (2,2) r o)).symm

private theorem recordAlice22_mass (j : AbsoluteEventTable) (r : Record) :
    ∑ a : Bool, recordAlice j 2 2 r a = j.mass (2,2) r := by
  unfold recordAlice LFJoint.Table.mass
  exact (Fintype.sum_prod_type (fun o : Bool × Bool => j.prob (2,2) r o)).symm

private theorem reference_chsh_le_two (j : AbsoluteEventTable) :
    (∑ r : Record, recCorr r * j.mass (2,2) r) -
      (∑ r : Record, ∑ b : Bool, recBobCorr r b * recordBob j 2 2 r b) +
      (∑ r : Record, ∑ a : Bool, aliceRecCorr r a * recordAlice j 2 2 r a) +
      RealQuantum.correlator j.behavior 2 2 ≤ 2 := by
  rw [corr22_as_joint]
  have hrecord (r : Record) :
      recCorr r * j.mass (2,2) r -
        (∑ b : Bool, recBobCorr r b * recordBob j 2 2 r b) +
        (∑ a : Bool, aliceRecCorr r a * recordAlice j 2 2 r a) +
        (∑ a : Bool, ∑ b : Bool, outCorr a b * j.prob (2,2) r (a,b))
        ≤ 2 * j.mass (2,2) r := by
    rcases r with ⟨c,d⟩
    cases c <;> cases d <;>
      simp only [LFJoint.Table.mass, recordBob, recordAlice, Fintype.sum_prod_type,
        Fintype.sum_bool, recCorr, recBobCorr, aliceRecCorr, outCorr, sgn,
        RealQuantum.sign] <;>
      have hff := j.nonneg (2,2) (false,false) (false,false) <;>
      have hft := j.nonneg (2,2) (false,false) (false,true) <;>
      have htf := j.nonneg (2,2) (false,false) (true,false) <;>
      have htt := j.nonneg (2,2) (false,false) (true,true) <;>
      have hff' := j.nonneg (2,2) (false,true) (false,false) <;>
      have hft' := j.nonneg (2,2) (false,true) (false,true) <;>
      have htf' := j.nonneg (2,2) (false,true) (true,false) <;>
      have htt' := j.nonneg (2,2) (false,true) (true,true) <;>
      have hff'' := j.nonneg (2,2) (true,false) (false,false) <;>
      have hft'' := j.nonneg (2,2) (true,false) (false,true) <;>
      have htf'' := j.nonneg (2,2) (true,false) (true,false) <;>
      have htt'' := j.nonneg (2,2) (true,false) (true,true) <;>
      have hff''' := j.nonneg (2,2) (true,true) (false,false) <;>
      have hft''' := j.nonneg (2,2) (true,true) (false,true) <;>
      have htf''' := j.nonneg (2,2) (true,true) (true,false) <;>
      have htt''' := j.nonneg (2,2) (true,true) (true,true) <;>
      linarith
  have hsum :
      (∑ r : Record,
        (recCorr r * j.mass (2,2) r -
          (∑ b : Bool, recBobCorr r b * recordBob j 2 2 r b) +
          (∑ a : Bool, aliceRecCorr r a * recordAlice j 2 2 r a) +
          (∑ a : Bool, ∑ b : Bool, outCorr a b * j.prob (2,2) r (a,b)))) ≤
      ∑ r : Record, 2 * j.mass (2,2) r := by
    exact Finset.sum_le_sum (fun r _ => hrecord r)
  have hmass : (∑ r : Record, j.mass (2,2) r) = 1 := by
    simpa [LFJoint.Table.mass] using j.normalized (2,2)
  have hleft :
      (∑ r : Record,
        (recCorr r * j.mass (2,2) r -
          (∑ b : Bool, recBobCorr r b * recordBob j 2 2 r b) +
          (∑ a : Bool, aliceRecCorr r a * recordAlice j 2 2 r a) +
          (∑ a : Bool, ∑ b : Bool, outCorr a b * j.prob (2,2) r (a,b)))) =
      (∑ r : Record, recCorr r * j.mass (2,2) r) -
        (∑ r : Record, ∑ b : Bool, recBobCorr r b * recordBob j 2 2 r b) +
        (∑ r : Record, ∑ a : Bool, aliceRecCorr r a * recordAlice j 2 2 r a) +
        (∑ r : Record, ∑ a : Bool, ∑ b : Bool,
          outCorr a b * j.prob (2,2) r (a,b)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hleft] at hsum
  have hright : (∑ r : Record, 2 * j.mass (2,2) r) = 2 := by
    rw [← Finset.mul_sum, hmass]
    norm_num
  rw [hright] at hsum
  exact hsum

private theorem bob_transport (j : AbsoluteEventTable) :
    -(∑ r : Record, ∑ b : Bool, recBobCorr r b * recordBob j 0 2 r b) ≤
      -(∑ r : Record, ∑ b : Bool, recBobCorr r b * recordBob j 2 2 r b) +
        2 * recordTVBob j 0 2 2 := by
  have h := weighted_difference_le_tv
    (p := fun rb : Record × Bool => recordBob j 2 2 rb.1 rb.2)
    (q := fun rb : Record × Bool => recordBob j 0 2 rb.1 rb.2)
    (f := fun rb : Record × Bool => recBobCorr rb.1 rb.2)
    (by intro rb; simpa [corr_abs_rb])
  rw [Fintype.sum_prod_type] at h
  unfold recordTVBob
  linarith

private theorem alice_transport (j : AbsoluteEventTable) :
    (∑ r : Record, ∑ a : Bool, aliceRecCorr r a * recordAlice j 2 0 r a) ≤
      (∑ r : Record, ∑ a : Bool, aliceRecCorr r a * recordAlice j 2 2 r a) +
        2 * recordTVAlice j 2 0 2 := by
  have h := weighted_difference_le_tv
    (p := fun ra : Record × Bool => recordAlice j 2 0 ra.1 ra.2)
    (q := fun ra : Record × Bool => recordAlice j 2 2 ra.1 ra.2)
    (f := fun ra : Record × Bool => aliceRecCorr ra.1 ra.2)
    (by intro ra; simpa [corr_abs_ar])
  rw [Fintype.sum_prod_type] at h
  unfold recordTVAlice
  linarith

/-- Direct Hall-type relaxed-CHSH theorem for readable absolute friend records. -/
theorem relaxed_chsh_bound (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j) :
    RealQuantum.correlator j.behavior 0 0 -
      RealQuantum.correlator j.behavior 0 2 +
      RealQuantum.correlator j.behavior 2 0 +
      RealQuantum.correlator j.behavior 2 2
      ≤ 2 + 2 * (recordTVAlice j 2 0 2 + recordTVBob j 0 2 2) := by
  rw [corr00_as_records j hr, corr02_as_recordBob j hr, corr20_as_recordAlice j hr]
  have h00 :
      (∑ r : Record, recCorr r * j.mass (0,0) r) =
        ∑ r : Record, recCorr r * j.mass (2,2) r := by
    apply Finset.sum_congr rfl
    intro r _
    rw [record_mass_at_22 j hi r]
  rw [h00]
  have href := reference_chsh_le_two j
  have hb := bob_transport j
  have ha := alice_transport j
  linarith

theorem relaxed_chsh_uniform (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j) {delta : ℝ}
    (ha : recordTVAlice j 2 0 2 ≤ delta)
    (hb : recordTVBob j 0 2 2 ≤ delta) :
    RealQuantum.correlator j.behavior 0 0 -
      RealQuantum.correlator j.behavior 0 2 +
      RealQuantum.correlator j.behavior 2 0 +
      RealQuantum.correlator j.behavior 2 2 ≤ 2 + 4 * delta := by
  have h := relaxed_chsh_bound j hr hi
  linarith

theorem explicit_angle_quantum_bound (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j)
    (hp : j.behavior = RealQuantum.behavior explicitAlice explicitBob) :
    sqrtTwoDelta ≤ recordTVAlice j 2 0 2 ∨
      sqrtTwoDelta ≤ recordTVBob j 0 2 2 := by
  have hchsh := relaxed_chsh_bound j hr hi
  have hval :
      RealQuantum.correlator j.behavior 0 0 -
        RealQuantum.correlator j.behavior 0 2 +
        RealQuantum.correlator j.behavior 2 0 +
        RealQuantum.correlator j.behavior 2 2 = 2 * Real.sqrt 2 := by
    rw [hp]
    simpa [AngleOptimality.chshNumerator, AngleOptimality.correlator_behavior] using
      AngleOptimality.explicit_chshNumerator
  rw [hval] at hchsh
  by_contra hn
  push_neg at hn
  unfold sqrtTwoDelta at hn
  linarith

end
end OntologySeparation.LFAgencyRelaxation.SqrtTwoPhysical
