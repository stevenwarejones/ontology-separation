import OntologySeparation.Experiments.LFJoint
import OntologySeparation.Core.Claim
/-! Sharp relaxed-LF readout-error bounds for the finite joint-event model.
The symmetric 6+8ε bound is established prior art (Moreno et al., Quantum 6, 785,
2022). This module connects explicit disagreement events to a checked whole-class
bound and attaining family. No finite-shot inference or quantum attainability of
the extremal no-signaling family is asserted. -/
namespace OntologySeparation.LFReadout
noncomputable section

def errorA (p : Behavior LF.interface) (c : Bool) : ℝ := 1 - ∑ b, p.prob (0,0) (c,b)
def errorB (p : Behavior LF.interface) (d : Bool) : ℝ := 1 - ∑ a, p.prob (0,0) (a,d)

theorem errorA_moment (p : Behavior LF.interface) (c : Bool) :
    errorA p c = (1 - RealQuantum.sign c * RealQuantum.marginalA p 0 0) / 2 := by
  have hn := p.normalized (0,0)
  cases c <;> simp [errorA, RealQuantum.sign, RealQuantum.marginalA, Fintype.sum_prod_type] at * <;> linarith

theorem errorB_moment (p : Behavior LF.interface) (d : Bool) :
    errorB p d = (1 - RealQuantum.sign d * RealQuantum.marginalB p 0 0) / 2 := by
  have hn := p.normalized (0,0)
  cases d <;> simp [errorB, RealQuantum.sign, RealQuantum.marginalB, Fintype.sum_prod_type] at * <;> linarith

set_option maxHeartbeats 2000000 in
theorem response_bound (p : Behavior LF.interface) (h : Shared.NoSignaling p) (c d : Bool) :
    RealQuantum.genuineLF p ≤ 6 + 4 * (errorA p c + errorB p d) := by
  have h00ff := Shared.moment_positive p h 0 0 false false
  have h00ft := Shared.moment_positive p h 0 0 false true
  have h00tf := Shared.moment_positive p h 0 0 true false
  have h00tt := Shared.moment_positive p h 0 0 true true
  have h01ff := Shared.moment_positive p h 0 1 false false
  have h01ft := Shared.moment_positive p h 0 1 false true
  have h01tf := Shared.moment_positive p h 0 1 true false
  have h01tt := Shared.moment_positive p h 0 1 true true
  have h02ff := Shared.moment_positive p h 0 2 false false
  have h02ft := Shared.moment_positive p h 0 2 false true
  have h02tf := Shared.moment_positive p h 0 2 true false
  have h02tt := Shared.moment_positive p h 0 2 true true
  have h10ff := Shared.moment_positive p h 1 0 false false
  have h10ft := Shared.moment_positive p h 1 0 false true
  have h10tf := Shared.moment_positive p h 1 0 true false
  have h10tt := Shared.moment_positive p h 1 0 true true
  have h11ff := Shared.moment_positive p h 1 1 false false
  have h11ft := Shared.moment_positive p h 1 1 false true
  have h11tf := Shared.moment_positive p h 1 1 true false
  have h11tt := Shared.moment_positive p h 1 1 true true
  have h12ff := Shared.moment_positive p h 1 2 false false
  have h12ft := Shared.moment_positive p h 1 2 false true
  have h12tf := Shared.moment_positive p h 1 2 true false
  have h12tt := Shared.moment_positive p h 1 2 true true
  have h20ff := Shared.moment_positive p h 2 0 false false
  have h20ft := Shared.moment_positive p h 2 0 false true
  have h20tf := Shared.moment_positive p h 2 0 true false
  have h20tt := Shared.moment_positive p h 2 0 true true
  have h21ff := Shared.moment_positive p h 2 1 false false
  have h21ft := Shared.moment_positive p h 2 1 false true
  have h21tf := Shared.moment_positive p h 2 1 true false
  have h21tt := Shared.moment_positive p h 2 1 true true
  have h22ff := Shared.moment_positive p h 2 2 false false
  have h22ft := Shared.moment_positive p h 2 2 false true
  have h22tf := Shared.moment_positive p h 2 2 true false
  have h22tt := Shared.moment_positive p h 2 2 true true
  rw [errorA_moment, errorB_moment]
  unfold RealQuantum.genuineLF
  cases c <;> cases d <;>
    simp only [RealQuantum.sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul,
      mul_one, mul_neg, neg_neg] at * <;> linarith

variable {Λ : Type} [Fintype Λ]

/-- Linearity under setting-independent preparation; reuse the existing response interface. -/
theorem score_mean (m : FriendRecords.Model Λ) (hi : FriendRecords.IndependentPreparation m) :
    RealQuantum.genuineLF m.behavior =
      ∑ l, (m.preparation (0,0)).mass l * RealQuantum.genuineLF (m.response l) := by
  have hA (x y : Fin 3) : RealQuantum.marginalA m.behavior x y =
      ∑ l, (m.preparation (0,0)).mass l * RealQuantum.marginalA (m.response l) x y := by
    simp only [RealQuantum.marginalA, FriendRecords.Model.behavior]
    simp_rw [hi (x,y) (0,0), Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro o _
    ring
  have hB (x y : Fin 3) : RealQuantum.marginalB m.behavior x y =
      ∑ l, (m.preparation (0,0)).mass l * RealQuantum.marginalB (m.response l) x y := by
    simp only [RealQuantum.marginalB, FriendRecords.Model.behavior]
    simp_rw [hi (x,y) (0,0), Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro o _
    ring
  have hE (x y : Fin 3) : RealQuantum.correlator m.behavior x y =
      ∑ l, (m.preparation (0,0)).mass l * RealQuantum.correlator (m.response l) x y := by
    simp only [RealQuantum.correlator, FriendRecords.Model.behavior]
    simp_rw [hi (x,y) (0,0), Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro o _
    ring
  unfold RealQuantum.genuineLF
  simp_rw [hA, hB, hE]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem operational_bound (m : FriendRecords.Model Λ)
    (hl : FriendRecords.ConditionalLocality m) (hi : FriendRecords.IndependentPreparation m) :
    RealQuantum.genuineLF m.behavior ≤ 6 + 4 *
      ∑ l, (m.preparation (0,0)).mass l * (errorA (m.response l) (m.charlie l) +
        errorB (m.response l) (m.debbie l)) := by
  rw [score_mean m hi]
  calc
    _ ≤ ∑ l, (m.preparation (0,0)).mass l * (6 + 4 *
        (errorA (m.response l) (m.charlie l) + errorB (m.response l) (m.debbie l))) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
        (response_bound (m.response l) (hl l) (m.charlie l) (m.debbie l))
        ((m.preparation (0,0)).nonneg l)
    _ = ∑ l, (6 * (m.preparation (0,0)).mass l + 4 *
        ((m.preparation (0,0)).mass l * (errorA (m.response l) (m.charlie l) +
          errorB (m.response l) (m.debbie l)))) := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        (m.preparation (0,0)).total]
      ring


open LFJoint

/-- Joint probabilities of disagreeing with Charlie and Debbie, at the read/read setting. -/
def mismatchA (j : Table) : ℝ := ∑ r, ∑ b, j.prob (0,0) r (!r.1,b)
def mismatchB (j : Table) : ℝ := ∑ r, ∑ a, j.prob (0,0) r (a,!r.2)

theorem mismatchA_nonneg (j : Table) : 0 ≤ mismatchA j :=
  Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun b _ => j.nonneg _ r (!r.1,b)
theorem mismatchB_nonneg (j : Table) : 0 ≤ mismatchB j :=
  Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun a _ => j.nonneg _ r (a,!r.2)

theorem mismatchA_mean (j : Table) (hi : IndependentRecords j) :
    mismatchA j = ∑ r, j.mass (0,0) r * errorA (conditional j hi r) r.1 := by
  apply Finset.sum_congr rfl
  intro r _
  rw [errorA, mul_sub, mul_one, Finset.mul_sum]
  simp_rw [conditional_reconstruct]
  rcases r with ⟨c,d⟩
  cases c <;> simp [Table.mass, Outcome, Fintype.sum_prod_type]

theorem mismatchB_mean (j : Table) (hi : IndependentRecords j) :
    mismatchB j = ∑ r, j.mass (0,0) r * errorB (conditional j hi r) r.2 := by
  apply Finset.sum_congr rfl
  intro r _
  rw [errorB, mul_sub, mul_one, Finset.mul_sum]
  simp_rw [conditional_reconstruct]
  rcases r with ⟨c,d⟩
  cases d <;> simp [Table.mass, Outcome, Fintype.sum_prod_type] <;> ring

/-- Relax only perfect record readout, retaining a joint extension, NSD and locality. -/
theorem joint_bound (j : Table) (hl : Local j) (hi : IndependentRecords j) :
    RealQuantum.genuineLF j.behavior ≤ 6 + 4 * (mismatchA j + mismatchB j) := by
  have h := operational_bound (toOperational j hi)
    (toOperational_local j hi hl) (toOperational_independent j hi)
  rw [toOperational_behavior] at h
  simpa only [toOperational, mul_add, Finset.sum_add_distrib,
    ← mismatchA_mean j hi, ← mismatchB_mean j hi] using h

/-- An exact score requires at least this much total readout disagreement under the retained laws. -/
theorem required_mismatch (j : Table) (hl : Local j) (hi : IndependentRecords j) :
    (RealQuantum.genuineLF j.behavior - 6) / 4 ≤ mismatchA j + mismatchB j := by
  have h := joint_bound j hl hi
  linarith


/-- Embed an arbitrary behavior with one fixed record pair. Readability is not assumed. -/
def withRecord (p : Behavior LF.interface) (r0 : Record) : Table where
  prob s r o := if r = r0 then p.prob s o else 0
  nonneg s r o := by split; exact p.nonneg s o; exact le_rfl
  normalized s := by
    calc
      _ = ∑ r : Record, if r = r0 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases h : r = r0 <;> simp [h, p.normalized]
      _ = 1 := by simp

theorem withRecord_independent (p : Behavior LF.interface) (r0 : Record) :
    IndependentRecords (withRecord p r0) := by
  intro s t r
  simp only [Table.mass, withRecord]
  by_cases h : r = r0 <;> simp [h, p.normalized]

theorem withRecord_local (p : Behavior LF.interface) (r0 : Record) (hp : Shared.NoSignaling p) :
    Local (withRecord p r0) := by
  constructor
  · intro r x y y' a
    change (∑ b, if r = r0 then p.prob (x,y) (a,b) else 0) = _
    by_cases h : r = r0
    · simpa [withRecord, h] using hp.1 x y y' a
    · simp [withRecord, h]
  · intro r x x' y b
    change (∑ a, if r = r0 then p.prob (x,y) (a,b) else 0) = _
    by_cases h : r = r0
    · simpa [withRecord, h] using hp.2 x x' y b
    · simp [withRecord, h]

theorem withRecord_behavior (p : Behavior LF.interface) (r0 : Record) :
    (withRecord p r0).behavior = p := by
  have he : (withRecord p r0).behavior.prob = p.prob := by
    funext s o
    simp [Table.behavior, withRecord]
  cases ha : (withRecord p r0).behavior
  cases p
  simp only [ha] at he
  cases he
  rfl

theorem mix_local (p q : Behavior LF.interface) (hp : Shared.NoSignaling p)
    (hq : Shared.NoSignaling q) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Shared.NoSignaling (p.mix q t h0 h1) := by
  constructor
  · intro x y y' a
    simp only [Behavior.mix, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hp.1 x y y' a, hq.1 x y y' a]
  · intro x x' y b
    simp only [Behavior.mix, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hp.2 x x' y b, hq.2 x x' y b]

/-- Existing extremal models give an explicit family, with total mismatch t. -/
def sharpTable (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Table :=
  withRecord (Shared.nsExtreme.mix Shared.saturatingModel.behavior t h0 h1) (false,true)

theorem sharpTable_independent (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IndependentRecords (sharpTable t h0 h1) := withRecord_independent _ _

theorem sharpTable_local (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Local (sharpTable t h0 h1) := by
  apply withRecord_local
  apply mix_local _ _ Shared.nsExtreme_noSignaling
  simpa [Shared.saturatingModel, LF.Model.behavior, LF.Component.behavior] using
    Shared.lf_noSignaling (Shared.deterministic (fun _ => false) (fun _ => true))

theorem sharpTable_score (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    RealQuantum.genuineLF (sharpTable t h0 h1).behavior = 6 + 4*t := by
  rw [sharpTable, withRecord_behavior]
  exact Shared.LF_NS_contamination_attained t h0 h1

theorem sharpTable_mismatchA (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    mismatchA (sharpTable t h0 h1) = t/2 := by
  simp [mismatchA, sharpTable, withRecord, Record,
    Behavior.mix, Shared.nsExtreme, Shared.saturatingModel, LF.Model.behavior,
    LF.Component.prob, LF.Component.a, LF.Component.b, LF.Component.e,
    Shared.deterministic, LF.sign, RealQuantum.sign]
  ring

theorem sharpTable_mismatchB (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    mismatchB (sharpTable t h0 h1) = t/2 := by
  simp [mismatchB, sharpTable, withRecord, Record,
    Behavior.mix, Shared.nsExtreme, Shared.saturatingModel, LF.Model.behavior,
    LF.Component.prob, LF.Component.a, LF.Component.b, LF.Component.e,
    Shared.deterministic, LF.sign, RealQuantum.sign]
  ring

/-- A whole-class optimum for a total readout-error budget in [0,1].
Both the upper bound and an attaining admissible joint table are provided. -/
theorem sharp_total_budget (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (∀ j : Table, Local j → IndependentRecords j → mismatchA j + mismatchB j ≤ t →
      RealQuantum.genuineLF j.behavior ≤ 6 + 4*t) ∧
    ∃ j : Table, Local j ∧ IndependentRecords j ∧
      mismatchA j + mismatchB j = t ∧ RealQuantum.genuineLF j.behavior = 6 + 4*t := by
  constructor
  · intro j hl hi he
    have h := joint_bound j hl hi
    linarith
  · refine ⟨sharpTable t h0 h1, sharpTable_local t h0 h1, sharpTable_independent t h0 h1, ?_,
      sharpTable_score t h0 h1⟩
    rw [sharpTable_mismatchA, sharpTable_mismatchB]
    ring


/-- Error budgets are constraints on the same joint extension as the LF score. -/
def budgetTheory (t : ℝ) (p : Behavior LF.interface) : Prop :=
  ∃ j : Table, Local j ∧ IndependentRecords j ∧ mismatchA j + mismatchB j ≤ t ∧ j.behavior = p

theorem budget_bound (t : ℝ) (p : Behavior LF.interface) (h : budgetTheory t p) :
    RealQuantum.genuineLF p ≤ 6 + 4*t := by
  rcases h with ⟨j, hl, hi, he, hp⟩
  have hb := joint_bound j hl hi
  rw [hp] at hb
  linarith

theorem quantum_required_error (t : ℝ) (h : budgetTheory t RealQuantum.lfBehavior) :
    (65453 : ℝ) / 361250 ≤ t := by
  have hb := budget_bound t RealQuantum.lfBehavior h
  rw [RealQuantum.lfBehavior_value] at hb
  linarith

theorem quantum_excluded (t : ℝ) (ht : t < (65453 : ℝ) / 361250) :
    ¬ budgetTheory t RealQuantum.lfBehavior := by
  intro h
  exact (not_lt_of_ge (quantum_required_error t h)) ht

/-- On this class, disagreement at the read setting is independent of the remote setting. -/
theorem mismatchA_remote (j : Table) (hl : Local j) (y : Fin 3) :
    (∑ r, ∑ b, j.prob (0,y) r (!r.1,b)) = mismatchA j := by
  apply Finset.sum_congr rfl
  intro r _
  exact hl.1 r 0 y 0 (!r.1)

theorem mismatchB_remote (j : Table) (hl : Local j) (x : Fin 3) :
    (∑ r, ∑ a, j.prob (x,0) r (a,!r.2)) = mismatchB j := by
  apply Finset.sum_congr rfl
  intro r _
  exact hl.2 r x 0 0 (!r.2)

/-- Separate user-supplied error ceilings imply a checked score ceiling. -/
theorem separate_budgets (j : Table) (hl : Local j) (hi : IndependentRecords j)
    (a b : ℝ) (ha : mismatchA j ≤ a) (hb : mismatchB j ≤ b) :
    RealQuantum.genuineLF j.behavior ≤ 6 + 4*(a+b) := by
  have h := joint_bound j hl hi
  linarith


/-- The admissible models behind a numerical report; no perfect-readout law is hidden here. -/
def withinBudget (t : ℝ) (j : Table) : Prop :=
  Local j ∧ IndependentRecords j ∧ mismatchA j + mismatchB j ≤ t

theorem sharpTable_within (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    withinBudget t (sharpTable t h0 h1) := by
  refine ⟨sharpTable_local t h0 h1, sharpTable_independent t h0 h1, ?_⟩
  rw [sharpTable_mismatchA, sharpTable_mismatchB]
  linarith

/-- A proof-bearing ceiling with an explicit satisfying model. Numbers derive from the budget. -/
def budgetClaim (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Claim :=
  .realizedBound (withinBudget (t : ℝ)) (fun j => RealQuantum.genuineLF j.behavior)
    (6 + 4*t)
    (by
      intro j h
      have hb := joint_bound j h.1 h.2.1
      have he := h.2.2
      push_cast
      linarith)
    (sharpTable (t : ℝ) (by exact_mod_cast h0) (by exact_mod_cast h1))
    (sharpTable_within (t : ℝ) (by exact_mod_cast h0) (by exact_mod_cast h1))

def attainingClaim (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Claim :=
  .witness (withinBudget (t : ℝ)) (fun j => RealQuantum.genuineLF j.behavior)
    (sharpTable (t : ℝ) (by exact_mod_cast h0) (by exact_mod_cast h1))
    (sharpTable_within (t : ℝ) (by exact_mod_cast h0) (by exact_mod_cast h1))
    (6 + 4*t) (by push_cast; exact sharpTable_score _ _ _)

/-- The quantum target is excluded only when the supplied error budget is small enough. -/
def exclusionClaim (t : ℚ) (ht : t < 65453 / 361250) : Claim :=
  .exclusion (budgetTheory (t : ℝ)) RealQuantum.lfBehavior
    (quantum_excluded _ (by
      have hh : (t : ℝ) < ((65453 / 361250 : ℚ) : ℝ) := by exact_mod_cast ht
      norm_num at hh
      exact hh))

end
end OntologySeparation.LFReadout
