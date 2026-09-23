import OntologySeparation.Core.Channels
import OntologySeparation.Core.Claim
import Mathlib.Tactic

/-! A fixed-horizon all-successes test on a normalized finite joint distribution.
Trial dependence is allowed. The null premise bounds continuation probability
along every surviving prefix, without division on zero-probability histories. -/
namespace OntologySeparation.FiniteShot
noncomputable section
abbrev Outcomes (n : ℕ) := Fin n → Bool
abbrev Trials (n : ℕ) := FiniteDistribution (Outcomes n)

def survives {n : ℕ} (k : ℕ) (x : Outcomes n) : Prop :=
  ∀ i, i.val < k → x i = true

instance {n k : ℕ} (x : Outcomes n) : Decidable (survives k x) :=
  inferInstanceAs (Decidable (∀ i : Fin n, i.val < k → x i = true))

/-- Actual event probability in the supplied whole-block distribution. -/
def prefixMass {n : ℕ} (p : Trials n) (k : ℕ) : ℝ :=
  ∑ x, p.mass x * (if survives k x then 1 else 0)

@[simp] theorem prefix_zero {n : ℕ} (p : Trials n) : prefixMass p 0 = 1 := by
  simp [prefixMass, survives, p.total]

theorem prefix_nonneg {n : ℕ} (p : Trials n) (k : ℕ) : 0 ≤ prefixMass p k := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (p.nonneg x) (by split_ifs <;> norm_num)

/-- A physical/calibration assumption on this joint distribution. Unconditional
single-trial marginals alone are not sufficient. -/
def NullBound {n : ℕ} (p : Trials n) (q : ℝ) : Prop :=
  ∀ k, k < n → prefixMass p (k+1) ≤ q * prefixMass p k

/-- A separately justified alternative-model premise, used only for power. -/
def AlternativeBound {n : ℕ} (p : Trials n) (a : ℝ) : Prop :=
  ∀ k, k < n → a * prefixMass p k ≤ prefixMass p (k+1)

theorem prefix_bound {n : ℕ} (p : Trials n) (q : ℝ) (hq : 0 ≤ q)
    (h : NullBound p q) (k : ℕ) (hk : k ≤ n) : prefixMass p k ≤ q^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      prefixMass p (k+1) ≤ q * prefixMass p k := h k (by omega)
      _ ≤ q * q^k := mul_le_mul_of_nonneg_left (ih (by omega)) hq
      _ = q^(k+1) := by rw [pow_succ]; ring

/-- False rejection probability of this fixed-block rule, not a posterior
probability that the null is true. -/
theorem false_rejection_bound {n : ℕ} (p : Trials n) (q : ℝ) (hq : 0 ≤ q)
    (h : NullBound p q) : prefixMass p n ≤ q^n :=
  prefix_bound p q hq h n le_rfl

theorem power_bound {n : ℕ} (p : Trials n) (a : ℝ) (ha : 0 ≤ a)
    (h : AlternativeBound p a) : a^n ≤ prefixMass p n := by
  have aux (k : ℕ) (hk : k ≤ n) : a^k ≤ prefixMass p k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        a^(k+1) = a * a^k := by rw [pow_succ]; ring
        _ ≤ a * prefixMass p k := mul_le_mul_of_nonneg_left (ih (by omega)) ha
        _ ≤ prefixMass p (k+1) := h k (by omega)
  exact aux n le_rfl

/-- A normalized deterministic block, reused from the existing finite channel. -/
def point {n : ℕ} (x : Outcomes n) : Trials n :=
  Channel.deterministic (fun _ : Unit => x) ()

@[simp] theorem prefix_point {n : ℕ} (x : Outcomes n) (k : ℕ) :
    prefixMass (point x) k = if survives k x then 1 else 0 := by
  classical
  unfold prefixMass point Channel.deterministic
  simp only [ite_mul, one_mul, zero_mul]
  simp

/-- Establish non-vacuity of the null class for every nonnegative q. -/
theorem always_failure_null (n : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    NullBound (point (fun _ : Fin n => false)) q := by
  intro k hk
  have hf : ¬ survives (k+1) (fun _ : Fin n => false) := by
    intro h
    have hh := h ⟨k,hk⟩ (Nat.lt_succ_self k)
    contradiction
  rw [prefix_point, if_neg hf]
  exact mul_nonneg hq (prefix_nonneg _ _)

/-- The stated alternative class is nonempty as well. -/
theorem always_success_alternative (n : ℕ) (a : ℝ) (ha : a ≤ 1) :
    AlternativeBound (point (fun _ : Fin n => true)) a := by
  intro k _
  simpa [survives] using ha

/-- Exact predeclared design. Calibration and power premises remain external
physical statements; arithmetic feasibility is checked here. -/
structure Plan where
  shots : ℕ
  positiveShots : 0 < shots
  nullCeiling : ℚ
  nullNonneg : 0 ≤ nullCeiling
  nullLeOne : nullCeiling ≤ 1
  alpha : ℚ
  alphaPositive : 0 < alpha
  alphaLessOne : alpha < 1
  adequate : nullCeiling^shots ≤ alpha

inductive Decision where | rejectNull | inconclusive
  deriving DecidableEq, Repr

/-- Fixed-length input prevents missing or extra shots from silently passing. -/
def Plan.decision (p : Plan) (observed : Outcomes p.shots) : Decision :=
  if survives p.shots observed then .rejectNull else .inconclusive

theorem Plan.rejects_iff (p : Plan) (observed : Outcomes p.shots) :
    p.decision observed = .rejectNull ↔ ∀ i, observed i = true := by
  simp [Plan.decision, survives]

theorem Plan.valid (p : Plan) (trials : Trials p.shots)
    (h : NullBound trials (p.nullCeiling : ℝ)) : prefixMass trials p.shots ≤ p.alpha := by
  apply (false_rejection_bound trials _ (by exact_mod_cast p.nullNonneg) h).trans
  exact_mod_cast p.adequate

/-- Probability of the actual decision rule under the supplied block law. -/
def Plan.rejectionProbability (p : Plan) (trials : Trials p.shots) : ℝ :=
  ∑ x, trials.mass x * (if p.decision x = .rejectNull then 1 else 0)

theorem Plan.rejectionProbability_eq (p : Plan) (trials : Trials p.shots) :
    p.rejectionProbability trials = prefixMass trials p.shots := by
  simp [Plan.rejectionProbability, Plan.decision, prefixMass]

theorem Plan.false_rejection_control (p : Plan) (trials : Trials p.shots)
    (h : NullBound trials (p.nullCeiling : ℝ)) :
    p.rejectionProbability trials ≤ (p.alpha : ℝ) := by
  rw [p.rejectionProbability_eq]
  exact p.valid trials h

/-- The class bound carries a normalized satisfying model. -/
def Plan.riskClaim (p : Plan) : Claim :=
  .realizedBound (fun trials : Trials p.shots => NullBound trials (p.nullCeiling : ℝ))
    (fun trials => prefixMass trials p.shots) (p.nullCeiling^p.shots)
    (fun trials h => by
      have hh := false_rejection_bound trials (p.nullCeiling : ℝ)
        (by exact_mod_cast p.nullNonneg) h
      exact_mod_cast hh)
    (point (fun _ : Fin p.shots => false))
    (always_failure_null p.shots _ (by exact_mod_cast p.nullNonneg))
end
end OntologySeparation.FiniteShot
