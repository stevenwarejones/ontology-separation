import OntologySeparation.Experiments.SignalingTradeoff
import OntologySeparation.Operational.HiddenInfluenceCausality

/-!
# All operational completions of the S4 witness

The six correlators in S4 omit one or two settings.  A concrete experimental
score must choose those unused settings.  There are 512 such completions.

This module makes the completion finite data, derives the exact slope function
suggested by the source's numerical 512-completion scan, and proves the spectrum
and multiplicities in the Lean kernel.  The physical universal bound is proved
below from the fixed K=8 theorem plus no-signaling/TV comparison lemmas; no
floating-point LP result is a proof rule.
-/

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators
noncomputable section

/-- The nine otherwise-unused binary settings needed to turn the six S4
correlators into full experimental contexts. -/
structure Completion where
  z1 : Bool
  w1 : Bool
  z2 : Bool
  w2 : Bool
  z3 : Bool
  z4 : Bool
  x5 : Bool
  y5 : Bool
  y6 : Bool
  deriving DecidableEq, Fintype

/-- The completion used by the existing K=8 certificate. -/
def optimalCompletion : Completion :=
  { z1 := false, w1 := true
    z2 := false, w2 := true
    z3 := false, z4 := false
    x5 := true, y5 := false, y6 := false }

/-- Exact completion-dependent signaling slope.

Only the two early-D choices used to complete the AB terms and the early-A
choice used to complete the doubled CD term affect the slope. -/
def Completion.slope (c : Completion) : ℤ :=
  16 - 2 * c.w1.toNat - 2 * c.w2.toNat - 4 * c.x5.toNat

theorem optimalCompletion_slope : optimalCompletion.slope = 8 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Completion.slope_mem (c : Completion) :
    c.slope = 8 ∨ c.slope = 10 ∨ c.slope = 12 ∨
      c.slope = 14 ∨ c.slope = 16 := by
  rcases c with ⟨z1,w1,z2,w2,z3,z4,x5,y5,y6⟩
  cases w1 <;> cases w2 <;> cases x5 <;> simp [Completion.slope]

/-- There are exactly 512 operational completions. -/
theorem completion_count : Fintype.card Completion = 512 := by decide

/-- Exact multiplicity of the optimal K=8 completions. -/
theorem slope8_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 8).card) = 64 := by
  decide

theorem slope10_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 10).card) = 128 := by
  decide

theorem slope12_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 12).card) = 128 := by
  decide

theorem slope14_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 14).card) = 128 := by
  decide

theorem slope16_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 16).card) = 64 := by
  decide

/-- The full exact spectrum, replacing the source repository's floating-point
512-LP multiplicity check. -/
theorem completion_spectrum :
    ((Finset.univ.filter fun c : Completion => c.slope = 8).card,
     (Finset.univ.filter fun c : Completion => c.slope = 10).card,
     (Finset.univ.filter fun c : Completion => c.slope = 12).card,
     (Finset.univ.filter fun c : Completion => c.slope = 14).card,
     (Finset.univ.filter fun c : Completion => c.slope = 16).card) =
      (64, 128, 128, 128, 64) := by
  rw [slope8_count, slope10_count, slope12_count, slope14_count, slope16_count]

private def abSign (o : Outcome) : ℝ :=
  if (o.val / 8 + o.val / 4 % 2) % 2 = 0 then 1 else -1

private def abdSign (o : Outcome) : ℝ :=
  if (o.val / 8 + o.val / 4 % 2 + o.val % 2) % 2 = 0 then 1 else -1

private def cdSign (o : Outcome) : ℝ :=
  if (o.val / 2 % 2 + o.val % 2) % 2 = 0 then 1 else -1

private def acdSign (o : Outcome) : ℝ :=
  if (o.val / 8 + o.val / 2 % 2 + o.val % 2) % 2 = 0 then 1 else -1

/-- S4 evaluated at one explicit completion. -/
noncomputable def completedScore (c : Completion) (p : Behavior interface) : ℝ :=
  mean p ⟨c.w1.toNat, by cases c.w1 <;> simp⟩
      ⟨2 * 0 + c.z1.toNat, by cases c.z1 <;> simp⟩ abSign +
  mean p ⟨c.w2.toNat, by cases c.w2 <;> simp⟩
      ⟨2 + c.z2.toNat, by cases c.z2 <;> simp⟩ abSign +
  mean p ⟨2, by omega⟩
      ⟨c.z3.toNat, by cases c.z3 <;> simp⟩ abdSign -
  mean p ⟨2, by omega⟩
      ⟨2 + c.z4.toNat, by cases c.z4 <;> simp⟩ abdSign +
  2 * mean p ⟨2 * c.x5.toNat, by cases c.x5 <;> simp⟩
      ⟨2 * c.y5.toNat, by cases c.y5 <;> simp⟩ cdSign +
  2 * mean p ⟨1, by omega⟩
      ⟨2 * c.y6.toNat + 1, by cases c.y6 <;> simp⟩ acdSign

def completedScoreCoeff (c : Completion) (j : Atom) : ℤ :=
  (if early j = ⟨c.w1.toNat, by cases c.w1 <;> simp⟩ then
      parity 0 (output j ⟨c.z1.toNat, by cases c.z1 <;> simp⟩) else 0) +
  (if early j = ⟨c.w2.toNat, by cases c.w2 <;> simp⟩ then
      parity 1 (output j ⟨2 + c.z2.toNat, by cases c.z2 <;> simp⟩) else 0) +
  (if early j = (2 : Early) then
      parity 2 (output j ⟨c.z3.toNat, by cases c.z3 <;> simp⟩) else 0) -
  (if early j = (2 : Early) then
      parity 3 (output j ⟨2 + c.z4.toNat, by cases c.z4 <;> simp⟩) else 0) +
  2 * (if early j = ⟨2 * c.x5.toNat, by cases c.x5 <;> simp⟩ then
      parity 4 (output j ⟨2 * c.y5.toNat, by cases c.y5 <;> simp⟩) else 0) +
  2 * (if early j = (1 : Early) then
      parity 5 (output j ⟨2 * c.y6.toNat + 1, by cases c.y6 <;> simp⟩) else 0)

/-- Every completed score is a linear functional of the physical response
weights, with coefficients defined independently from the LP certificate. -/
theorem completedScore_eq (m : Model) (c : Completion) :
    completedScore c m.behavior =
      ∑ j, (completedScoreCoeff c j : ℝ) * m.weight j := by
  unfold completedScore
  simp only [mean_eq, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [completedScoreCoeff, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat, Int.cast_ite, Int.cast_zero]
  simp [abSign, abdSign, cdSign, acdSign, parity, sign]
  ring

/-- The named optimal completion is exactly the fixed score already certified. -/
theorem completedScore_optimal (p : Behavior interface) :
    completedScore optimalCompletion p = score p := by
  unfold completedScore optimalCompletion score
  norm_num [abSign, abdSign, cdSign, acdSign, termEarly, termLate, termWeight, parity,
    sign]
  ring


private def abRecipientSign (r : Recipient) : ℝ :=
  if (r.val / 4 + r.val / 2 % 2) % 2 = 0 then 1 else -1

private def cdRecipientSign (r : Recipient) : ℝ :=
  if (r.val / 2 % 2 + r.val % 2) % 2 = 0 then 1 else -1

set_option maxRecDepth 100000 in
private theorem abSign_factors : ∀ o : Outcome,
    abSign o = abRecipientSign (recipientD o) := by decide

set_option maxRecDepth 100000 in
private theorem cdSign_factors : ∀ o : Outcome,
    cdSign o = cdRecipientSign (recipientA o) := by decide

private theorem abRecipientSign_abs (r : Recipient) :
    |abRecipientSign r| ≤ 1 := by
  unfold abRecipientSign
  split <;> norm_num

private theorem cdRecipientSign_abs (r : Recipient) :
    |cdRecipientSign r| ≤ 1 := by
  unfold cdRecipientSign
  split <;> norm_num

/-- If an observable factors through a recipient projection, its mean is the
expectation of that observable under the corresponding recipient marginal. -/
theorem mean_eq_marginal_sum (p : Behavior interface) (e : Early) (l : Late)
    (proj : Outcome → Recipient) (g : Recipient → ℝ) :
    mean p e l (fun o => g (proj o)) =
      ∑ r, marginal p e l proj r * g r := by
  unfold mean marginal
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp [mul_assoc]

/-- A bounded recipient observable changes by at most twice the recipient TV
under the early-setting flip represented by one signaling context. -/
theorem context_mean_change_abs_le_two_tv
    (p : Behavior interface) (c : Context) (g : Recipient → ℝ)
    (hg : ∀ r, |g r| ≤ 1) :
    |mean p (contextEarly c false) (contextLate c) (fun o => g (project c o)) -
      mean p (contextEarly c true) (contextLate c) (fun o => g (project c o))|
      ≤ 2 * tv p c := by
  rw [mean_eq_marginal_sum, mean_eq_marginal_sum]
  have hrewrite :
      (∑ r, marginal p (contextEarly c false) (contextLate c) (project c) r * g r) -
        ∑ r, marginal p (contextEarly c true) (contextLate c) (project c) r * g r =
      ∑ r, difference p c r * g r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    unfold difference
    ring
  rw [hrewrite]
  calc
    |∑ r, difference p c r * g r| ≤
        ∑ r, |difference p c r * g r| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset Recipient))
              (f := fun r => difference p c r * g r))
    _ = ∑ r, |difference p c r| * |g r| := by
          apply Finset.sum_congr rfl
          intro r _
          rw [abs_mul]
    _ ≤ ∑ r, |difference p c r| := by
          apply Finset.sum_le_sum
          intro r _
          simpa using
            (mul_le_of_le_one_right (abs_nonneg (difference p c r)) (hg r))
    _ = 2 * tv p c := by
          unfold tv
          ring

private def wContext (y : Bool) : Context :=
  ⟨8 + 2 * y.toNat, by cases y <;> simp <;> omega⟩

private theorem wContext_early_false (y : Bool) :
    contextEarly (wContext y) false = ⟨0, by omega⟩ := by
  apply Fin.ext
  cases y <;> decide

private theorem wContext_early_true (y : Bool) :
    contextEarly (wContext y) true = ⟨1, by omega⟩ := by
  apply Fin.ext
  cases y <;> decide

private theorem wContext_late (y : Bool) :
    contextLate (wContext y) = ⟨2 * y.toNat, by cases y <;> simp⟩ := by
  apply Fin.ext
  cases y <;> decide

private theorem wContext_project (y : Bool) :
    project (wContext y) = recipientD := by
  funext o
  cases y <;> rfl

/-- Changing D's early setting can move either AB term by at most 2 delta. -/
theorem ab_w0_le_w1_add_two_delta (m : Model) (delta : ℝ)
    (budget : Within m.behavior delta) (y : Bool) :
    mean m.behavior ⟨0, by omega⟩ ⟨2 * y.toNat, by cases y <;> simp⟩ abSign
      ≤ mean m.behavior ⟨1, by omega⟩ ⟨2 * y.toNat, by cases y <;> simp⟩ abSign +
        2 * delta := by
  have h := context_mean_change_abs_le_two_tv m.behavior (wContext y)
    abRecipientSign abRecipientSign_abs
  rw [wContext_early_false, wContext_early_true, wContext_late, wContext_project] at h
  simp_rw [← abSign_factors] at h
  have htv := budget (wContext y)
  have hone :
      mean m.behavior ⟨0, by omega⟩ ⟨2 * y.toNat, by cases y <;> simp⟩ abSign -
        mean m.behavior ⟨1, by omega⟩ ⟨2 * y.toNat, by cases y <;> simp⟩ abSign
        ≤ 2 * delta := by
    exact le_trans (le_abs_self _) (le_trans h (mul_le_mul_of_nonneg_left htv (by norm_num)))
  linarith

private def xCDContext : Context := 0

private theorem xCD_context_data :
    contextEarly xCDContext false = ⟨0, by omega⟩ ∧
    contextEarly xCDContext true = ⟨2, by omega⟩ ∧
    contextLate xCDContext = ⟨0, by omega⟩ ∧
    project xCDContext = recipientA := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Changing A's early setting can move the CD correlator by at most 2 delta;
the S4 coefficient 2 therefore contributes at most 4 delta. -/
theorem cd_x0_le_x1_add_two_delta (m : Model) (delta : ℝ)
    (budget : Within m.behavior delta) :
    mean m.behavior ⟨0, by omega⟩ ⟨0, by omega⟩ cdSign
      ≤ mean m.behavior ⟨2, by omega⟩ ⟨0, by omega⟩ cdSign + 2 * delta := by
  have h := context_mean_change_abs_le_two_tv m.behavior xCDContext
    cdRecipientSign cdRecipientSign_abs
  rcases xCD_context_data with ⟨h0,h1,hl,hp⟩
  rw [h0,h1,hl,hp] at h
  simp_rw [← cdSign_factors] at h
  have htv := budget xCDContext
  have hone :
      mean m.behavior ⟨0, by omega⟩ ⟨0, by omega⟩ cdSign -
        mean m.behavior ⟨2, by omega⟩ ⟨0, by omega⟩ cdSign
        ≤ 2 * delta := by
    exact le_trans (le_abs_self _) (le_trans h (mul_le_mul_of_nonneg_left htv (by norm_num)))
  linarith

set_option maxRecDepth 100000 in
private theorem ab_late_z_irrelevant : ∀ (j : Atom) (y z : Bool),
    abSign (output j ⟨2 * y.toNat + z.toNat, by
      have hy := Bool.toNat_le y; have hz := Bool.toNat_le z; omega⟩) =
    abSign (output j ⟨2 * y.toNat, by
      have hy := Bool.toNat_le y; omega⟩) := by decide

set_option maxRecDepth 100000 in
private theorem abd_late_z_irrelevant : ∀ (j : Atom) (y z : Bool),
    abdSign (output j ⟨2 * y.toNat + z.toNat, by
      have hy := Bool.toNat_le y; have hz := Bool.toNat_le z; omega⟩) =
    abdSign (output j ⟨2 * y.toNat, by
      have hy := Bool.toNat_le y; omega⟩) := by decide

set_option maxRecDepth 100000 in
private theorem cd_late_y_irrelevant : ∀ (j : Atom) (y : Bool),
    cdSign (output j ⟨2 * y.toNat, by
      have hy := Bool.toNat_le y; omega⟩) =
    cdSign (output j 0) := by decide

set_option maxRecDepth 100000 in
private theorem acd_late_y_irrelevant : ∀ (j : Atom) (y : Bool),
    acdSign (output j ⟨2 * y.toNat + 1, by
      have hy := Bool.toNat_le y; omega⟩) =
    acdSign (output j 1) := by decide

theorem mean_ab_z_irrelevant (m : Model) (e : Early) (y z : Bool) :
    mean m.behavior e
        ⟨2 * y.toNat + z.toNat, by
          have hy := Bool.toNat_le y; have hz := Bool.toNat_le z; omega⟩ abSign =
      mean m.behavior e ⟨2 * y.toNat, by
        have hy := Bool.toNat_le y; omega⟩ abSign := by
  rw [mean_eq, mean_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [ab_late_z_irrelevant]

theorem mean_abd_z_irrelevant (m : Model) (e : Early) (y z : Bool) :
    mean m.behavior e
        ⟨2 * y.toNat + z.toNat, by
          have hy := Bool.toNat_le y; have hz := Bool.toNat_le z; omega⟩ abdSign =
      mean m.behavior e ⟨2 * y.toNat, by
        have hy := Bool.toNat_le y; omega⟩ abdSign := by
  rw [mean_eq, mean_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [abd_late_z_irrelevant]

theorem mean_cd_y_irrelevant (m : Model) (e : Early) (y : Bool) :
    mean m.behavior e ⟨2 * y.toNat, by
        have hy := Bool.toNat_le y; omega⟩ cdSign =
      mean m.behavior e 0 cdSign := by
  rw [mean_eq, mean_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [cd_late_y_irrelevant]

theorem mean_acd_y_irrelevant (m : Model) (e : Early) (y : Bool) :
    mean m.behavior e ⟨2 * y.toNat + 1, by
        have hy := Bool.toNat_le y; omega⟩ acdSign =
      mean m.behavior e 1 acdSign := by
  rw [mean_eq, mean_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [acd_late_y_irrelevant]

/-- All six unused late-setting choices are genuinely irrelevant in the
conditional-local response model. -/
theorem completedScore_late_irrelevant (m : Model) (c : Completion) :
    completedScore c m.behavior =
      completedScore
        { c with z1 := false, z2 := false, z3 := false, z4 := false,
                 y5 := false, y6 := false } m.behavior := by
  rcases c with ⟨z1,w1,z2,w2,z3,z4,x5,y5,y6⟩
  simp only [completedScore]
  rw [mean_ab_z_irrelevant m _ false z1,
      mean_ab_z_irrelevant m _ true z2,
      mean_abd_z_irrelevant m _ false z3,
      mean_abd_z_irrelevant m _ true z4,
      mean_cd_y_irrelevant m _ y5,
      mean_acd_y_irrelevant m _ y6]

/-- Universal completion-dependent tradeoff. The fixed K=8 certificate plus
three early-setting substitution costs gives the full exact upper spectrum. -/
theorem completedScore_bound (m : Model) (c : Completion) (delta : ℝ)
    (budget : Within m.behavior delta) :
    completedScore c m.behavior ≤ 6 + (c.slope : ℝ) * delta := by
  have hdelta : 0 ≤ delta := by
    exact le_trans (show 0 ≤ tv m.behavior 0 by unfold tv; positivity) (budget 0)
  rw [completedScore_late_irrelevant]
  have hbase := score_bound m delta budget
  have h0 := ab_w0_le_w1_add_two_delta m delta budget false
  have h1 := ab_w0_le_w1_add_two_delta m delta budget true
  have hcd := cd_x0_le_x1_add_two_delta m delta budget
  rcases c with ⟨z1,w1,z2,w2,z3,z4,x5,y5,y6⟩
  cases w1 <;> cases w2 <;> cases x5 <;>
    simp [completedScore, Completion.slope, optimalCompletion, completedScore_optimal] at * <;>
    linarith

/-- In signaling form, every completion has a certified slope in
{8,10,12,14,16}. -/
theorem completedScore_signaling_bound (m : Model) (c : Completion) :
    completedScore c m.behavior ≤ 6 + (c.slope : ℝ) * m.signaling := by
  exact completedScore_bound m c m.signaling
    ((signaling_le_iff m m.signaling).mp le_rfl)

end
end OntologySeparation.HiddenInfluence
