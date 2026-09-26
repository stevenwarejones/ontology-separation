import OntologySeparation.Core.FiniteModels
import Mathlib.Tactic.FinCases

/-! Finite ontic form of Kunjwal–Lostaglio–Pusey (2019), Lemma 5 / Theorem 3.
The response and transition premises below are ontological representations of
operational equivalences, not consequences of small calibration residuals. -/
namespace OntologySeparation.PathContextuality
noncomputable section

abbrev jointInterface : Interface := { Setting := Unit, Outcome := Bool × Bool }

/-- `false` is the negative pointer; `true` is successful final readout.
No deterministic path or deterministic final response is assumed. -/
structure Model (Λ : Type) [Fintype Λ] where
  preparation : FiniteDistribution Λ
  probe : Λ → FiniteDistribution (Bool × Λ)
  final : Λ → Behavior binaryInterface

namespace Model
variable {Λ : Type} [Fintype Λ]
def observed (m : Model Λ) : Behavior jointInterface where
  prob _ o := ∑ l, m.preparation.mass l *
    ∑ j, (m.probe l).mass (o.1, j) * (m.final j).prob () o.2
  nonneg _ o := Finset.sum_nonneg fun l _ => mul_nonneg (m.preparation.nonneg l)
    (Finset.sum_nonneg fun j _ => mul_nonneg ((m.probe l).nonneg _) ((m.final j).nonneg _ _))
  normalized _ := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Fintype.sum_prod_type]
    have h (l : Λ) : (∑ b : Bool, ∑ f : Bool, ∑ j : Λ,
        (m.probe l).mass (b,j) * (m.final j).prob () f) = 1 := by
      have inner (b : Bool) : (∑ f : Bool, ∑ j : Λ,
          (m.probe l).mass (b,j) * (m.final j).prob () f) =
          ∑ j : Λ, (m.probe l).mass (b,j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum, (m.final j).normalized ()]
        exact mul_one _
      simp_rw [inner]
      simpa [Fintype.sum_prod_type] using (m.probe l).total
    simp_rw [h, mul_one]
    exact m.preparation.total

def pF (m : Model Λ) : ℝ := m.preparation.mean (fun l => (m.final l).prob () true)
def pMinus (m : Model Λ) : ℝ := m.observed.prob () (false,true)
def negative (m : Model Λ) (l : Λ) : ℝ := ∑ j, (m.probe l).mass (false,j)

def ResponseCap (m : Model Λ) (q : ℝ) : Prop := ∀ l, m.negative l ≤ q

/-- The identity representation is the diagonal kernel. This is an explicit
premise, as in KLP's proof; operational channel equality alone is not this field. -/
def Disturbance (m : Model Λ) (d : ℝ) : Prop := by
  classical
  exact ∃ D : Λ → FiniteDistribution Λ, ∀ l j,
    (m.probe l).mass (false,j) + (m.probe l).mass (true,j) =
      (1-d) * (if j = l then 1 else 0) + d * (D l).mass j

/-- Measurement noncontextuality plus the noisy binary measurement equivalence
implies the cap. `e` may be stochastic: definite occupancy is unnecessary. -/
theorem cap_of_measurement_equivalence (m : Model Λ) (pm : ℝ) (hpm : 0 ≤ pm)
    (e : Λ → ℝ) (he : ∀ l, e l ≤ 1)
    (h : ∀ l, m.negative l = (1-pm)/2 + pm * e l) :
    m.ResponseCap ((1+pm)/2) := by
  intro l
  rw [h l]
  nlinarith [mul_le_mul_of_nonneg_left (he l) hpm]

/-- Arbitrary finite ontic cardinality, arbitrary stochastic final readout.
This proof does not enumerate deterministic ontologies. -/
theorem bound (m : Model Λ) (q d : ℝ) (hd : 0 ≤ d)
    (hq : m.ResponseCap q) (hD : m.Disturbance d) :
    m.pMinus ≤ q*m.pF + d*(1-m.pF) := by
  classical
  obtain ⟨D, hD⟩ := hD
  have row (l : Λ) : (∑ j, (m.probe l).mass (false,j) * (m.final j).prob () true) ≤
      q * (m.final l).prob () true + d * (1-(m.final l).prob () true) := by
    have point (j : Λ) : (m.probe l).mass (false,j) * (m.final j).prob () true ≤
        (m.probe l).mass (false,j) * (m.final l).prob () true +
          d * (D l).mass j * (1-(m.final l).prob () true) := by
      have r0 := (m.final l).nonneg () true
      have r1 := (m.final l).prob_le_one () true
      have s1 := (m.final j).prob_le_one () true
      have k0 := (m.probe l).nonneg (false,j)
      have t0 := (m.probe l).nonneg (true,j)
      have z0 := mul_nonneg hd ((D l).nonneg j)
      by_cases hj : j = l
      · subst j
        nlinarith
      · have hk := hD l j
        simp only [if_neg hj, mul_zero, zero_add] at hk
        have hkd : (m.probe l).mass (false,j) ≤ d * (D l).mass j := by linarith
        have hmul := mul_le_mul_of_nonneg_right hkd (sub_nonneg.mpr r1)
        nlinarith [mul_le_mul_of_nonneg_left s1 k0]
    calc
      _ ≤ ∑ j, ((m.probe l).mass (false,j) * (m.final l).prob () true +
          d * (D l).mass j * (1-(m.final l).prob () true)) :=
        Finset.sum_le_sum fun j _ => point j
      _ = m.negative l * (m.final l).prob () true + d * (1-(m.final l).prob () true) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
          ← Finset.mul_sum, (D l).total]
        simp [negative]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hq l)
        ((m.final l).nonneg () true)) le_rfl
  calc
    m.pMinus ≤ ∑ l, m.preparation.mass l *
        (q * (m.final l).prob () true + d * (1-(m.final l).prob () true)) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (row l) (m.preparation.nonneg l)
    _ = q*m.pF + d*(1-m.pF) := by
      simp only [pF, FiniteDistribution.mean]
      simp_rw [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [mul_left_comm (m.preparation.mass _) q,
        mul_left_comm (m.preparation.mass _) d, ← Finset.mul_sum]
      rw [← Finset.sum_mul, m.preparation.total]
      ring

theorem trivial_bound (m : Model Λ) (q : ℝ) (hq : m.ResponseCap q) : m.pMinus ≤ q := by
  apply m.preparation.mean_le
  intro l
  calc
    _ ≤ ∑ j, (m.probe l).mass (false,j) := Finset.sum_le_sum fun j _ => by
      simpa using mul_le_mul_of_nonneg_left ((m.final j).prob_le_one () true)
        ((m.probe l).nonneg (false,j))
    _ ≤ q := hq l

theorem full_bound (m : Model Λ) (q d : ℝ) (hd : 0 ≤ d)
    (hq : m.ResponseCap q) (hD : m.Disturbance d) :
    m.pMinus ≤ min q (q*m.pF+d*(1-m.pF)) :=
  le_min (m.trivial_bound q hq) (m.bound q d hd hq hD)

/-- Robustness to explicitly bounded probability discrepancies. These are
observable closeness to a model satisfying the representation premises, NOT an
inference from operational closeness to ontic closeness. -/
theorem robust_bound (m : Model Λ) (q d epsA epsF a f : ℝ)
    (hd : 0 ≤ d) (hq : m.ResponseCap q) (hD : m.Disturbance d)
    (ha : |a-m.pMinus| ≤ epsA) (hf : |f-m.pF| ≤ epsF) :
    a ≤ q*f+d*(1-f)+epsA+|q-d| * epsF := by
  have hb := m.bound q d hd hq hD
  have he := (abs_le.mp ha).2
  have hprod : |(q-d)*(m.pF-f)| ≤ |q-d| * epsF := by
    rw [abs_mul, abs_sub_comm m.pF f]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg _)
  have hu := (abs_le.mp hprod).2
  nlinarith
end Model

/-- One-state null: fair pointer, no disturbance, arbitrary stochastic readout. -/
def nullModel : Model Unit where
  preparation := ⟨fun _ => 1, by intro x; norm_num, by simp⟩
  probe _ := ⟨fun _ => 1/2, by intro x; norm_num, by simp⟩
  final _ := coin (1/4) (by norm_num) (by norm_num)

theorem null_nonempty : nullModel.ResponseCap (1/2) ∧ nullModel.Disturbance 0 ∧
    nullModel.pF = 1/4 ∧ nullModel.pMinus = 1/8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l; simp [Model.negative, nullModel]
  · refine ⟨fun _ => ⟨fun _ => 1, by intro x; norm_num, by simp⟩, ?_⟩
    intro l j; norm_num [nullModel]
  · norm_num [Model.pF, FiniteDistribution.mean, nullModel, coin]
  · norm_num [Model.pMinus, Model.observed, nullModel, coin]
/-- The reduced null remains inhabited at the violating example's q, d and
bypass probability. Its probe is fair and its hidden disturbance is identity. -/
def referenceNull : Model Unit where
  preparation := nullModel.preparation
  probe := nullModel.probe
  final _ := coin (49/625) (by norm_num) (by norm_num)

theorem reference_null_nonempty : referenceNull.ResponseCap (16/25) ∧
    referenceNull.Disturbance (1/50) ∧ referenceNull.pF = 49/625 ∧
    referenceNull.pMinus = 49/1250 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l; norm_num [Model.negative, referenceNull, nullModel]
  · refine ⟨fun _ => ⟨fun _ => 1, by intro x; norm_num, by simp⟩, ?_⟩
    intro l j
    have hj : j = l := Subsingleton.elim _ _
    norm_num [referenceNull, nullModel, hj]
  · norm_num [Model.pF, FiniteDistribution.mean, referenceNull, nullModel, coin]
  · norm_num [Model.pMinus, Model.observed, referenceNull, nullModel, coin]

end
end OntologySeparation.PathContextuality
