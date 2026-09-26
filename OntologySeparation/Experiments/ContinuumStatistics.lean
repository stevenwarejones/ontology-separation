import OntologySeparation.Experiments.ContinuumApproximation
import OntologySeparation.Core.Extensions

/-! Complete finite joint-law bounds for independent repetitions. TV is half L1.
These statements are not adaptive/channel or optional-stopping guarantees. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset

variable {A B : Type} [Fintype A] [Fintype B]

def l1 (p q : FiniteDistribution A) : ℝ := ∑ a, |p.mass a-q.mass a|
def tv (p q : FiniteDistribution A) : ℝ := l1 p q / 2

def distributionProduct (p : FiniteDistribution A) (q : FiniteDistribution B) :
    FiniteDistribution (A × B) where
  mass x := p.mass x.1*q.mass x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, q.total, mul_one]
    exact p.total

theorem product_l1 (p r : FiniteDistribution A) (q s : FiniteDistribution B) :
    l1 (distributionProduct p q) (distributionProduct r s) ≤ l1 p r+l1 q s := by
  unfold l1
  rw [Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b, |p.mass a*q.mass b-r.mass a*s.mass b|) ≤
      ∑ a, ∑ b, (|p.mass a-r.mass a|*q.mass b+r.mass a*|q.mass b-s.mass b|) := by
        apply sum_le_sum
        intro a _
        apply sum_le_sum
        intro b _
        have eq : p.mass a*q.mass b-r.mass a*s.mass b =
            (p.mass a-r.mass a)*q.mass b+r.mass a*(q.mass b-s.mass b) := by ring
        rw [eq]
        calc
          _ ≤ |(p.mass a-r.mass a)*q.mass b|+|r.mass a*(q.mass b-s.mass b)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (q.nonneg b),
            abs_of_nonneg (r.nonneg a)]
    _ = (∑ a, |p.mass a-r.mass a|)+(∑ b, |q.mass b-s.mass b|) := by
      simp_rw [sum_add_distrib, ← Finset.mul_sum, q.total, mul_one]
      rw [← Finset.sum_mul, r.total, one_mul]

theorem product_tv (p r : FiniteDistribution A) (q s : FiniteDistribution B) :
    tv (distributionProduct p q) (distributionProduct r s) ≤ tv p r+tv q s := by
  have := product_l1 p r q s
  unfold tv
  linarith

theorem tv_le_one (p q : FiniteDistribution A) : tv p q ≤ 1 := by
  have hb : l1 p q ≤ 2 := by
    calc
      l1 p q ≤ ∑ a, (p.mass a+q.mass a) := by
        apply sum_le_sum
        intro a _
        exact abs_sub_le_iff.mpr ⟨by linarith [q.nonneg a], by linarith [p.nonneg a]⟩
      _ = 2 := by rw [sum_add_distrib, p.total, q.total]; norm_num
  unfold tv
  linarith

/-- Randomized test acceptance is bounded in the TV convention used in the design. -/
theorem test_mean_bound (p q : FiniteDistribution A) (f : A → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    |q.mean f-p.mean f| ≤ tv p q := by
  have center : q.mean f-p.mean f = ∑ a, (f a-1/2)*(q.mass a-p.mass a) := by
    unfold FiniteDistribution.mean
    calc
      _ = (∑ a, (f a-1/2)*(q.mass a-p.mass a)) + (1/2)*((∑ a,q.mass a)-(∑ a,p.mass a)) := by
        simp only [mul_sub, sub_mul, sum_sub_distrib, ← Finset.mul_sum]
        simp_rw [mul_comm (q.mass _), mul_comm (p.mass _)]
        ring
      _ = _ := by rw [q.total,p.total]; ring
  rw [center]
  calc
    |∑ a, (f a-1/2)*(q.mass a-p.mass a)| ≤
        ∑ a, |(f a-1/2)*(q.mass a-p.mass a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (1/2)*|p.mass a-q.mass a| := by
      apply sum_le_sum
      intro a _
      rw [abs_mul, abs_sub_comm (q.mass a)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [hf0 a],by linarith [hf1 a]⟩
    _ = tv p q := by unfold tv l1; rw [← Finset.mul_sum]; ring

theorem test_error (p q : FiniteDistribution A) (f : A → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    1-tv p q ≤ p.mean f+(1-q.mean f) :=
  test_error_of_event_bound _ _ _ (test_mean_bound p q f hf0 hf1)

def Samples (A : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => A × Samples A n

def samplesFintype (A : Type) [Fintype A] : (n : ℕ) → Fintype (Samples A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
      letI := samplesFintype A n
      exact inferInstanceAs (Fintype (A × Samples A n))

instance (A : Type) [Fintype A] (n : ℕ) : Fintype (Samples A n) := samplesFintype A n

def iid (p : FiniteDistribution A) : (n : ℕ) → FiniteDistribution (Samples A n)
  | 0 => { mass := fun _ => 1, nonneg := by intro; norm_num, total := by simp [Samples] }
  | n+1 => distributionProduct p (iid p n)

theorem iid_tv (p q : FiniteDistribution A) (n : ℕ) :
    tv (iid p n) (iid q n) ≤ n*tv p q := by
  induction n with
  | zero => simp [iid,tv,l1]
  | succ n ih =>
    have hp := product_tv p q (iid p n) (iid q n)
    change tv (distributionProduct p (iid p n)) (distributionProduct q (iid q n)) ≤ _
    push_cast
    nlinarith

theorem iid_tv_capped (p q : FiniteDistribution A) (n : ℕ) :
    tv (iid p n) (iid q n) ≤ min 1 (n*tv p q) :=
  le_min (tv_le_one _ _) (iid_tv p q n)

end
end OntologySeparation.ContinuumFinite
