import OntologySeparation.Runtime.Research
import OntologySeparation.Core.Extensions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Complex.Basic

/-! Restricted experiments for the seven formerly empty research directions.
Theorems specify their scope; none asserts a new post-LF no-go theorem. -/
namespace OntologySeparation.Research

/-- P01: three jointly assigned bits cannot disagree on all three edges. -/
theorem triangle_bound (v : Triple) : triangle v ≤ 2 := by
  obtain ⟨a,b,c⟩ := v
  cases a <;> cases b <;> cases c <;> norm_num [triangle, mismatch]

/-- The deterministic bound also holds for every finite distribution of records. -/
theorem triangle_mixture_bound (d : FiniteDistribution Triple) :
    d.mean (fun v => (triangle v : ℝ)) ≤ 2 := by
  apply d.mean_le
  intro v
  exact_mod_cast triangle_bound v

/-- Pairwise contexts are individually normalized and have the same fair marginal. -/
theorem pairwise_consistent :
    (∀ a, pairwise a false + pairwise a true = 1/2) ∧
    (∀ b, pairwise false b + pairwise true b = 1/2) ∧
    pairwise false true + pairwise true false = 1 := by
  constructor
  · intro a; cases a <;> norm_num [pairwise]
  constructor
  · intro b; cases b <;> norm_num [pairwise]
  · norm_num [pairwise]

/-- If each edge is perfectly anticorrelated, there is no joint record distribution. -/
theorem no_global_triangle :
    ¬ ∃ d : FiniteDistribution Triple, d.mean (fun v => (triangle v : ℝ)) = 3 := by
  rintro ⟨d, hd⟩
  have h := triangle_mixture_bound d
  linarith

/-- A gluing distribution must reproduce all three pairwise tables, not merely
one selected statistic. -/
def GluesPairwise (d : FiniteDistribution Triple) : Prop :=
  (∀ a b, (∑ c : Bool, d.mass (a,b,c)) = (pairwise a b : ℝ)) ∧
  (∀ b c, (∑ a : Bool, d.mass (a,b,c)) = (pairwise b c : ℝ)) ∧
  (∀ a c, (∑ b : Bool, d.mass (a,b,c)) = (pairwise a c : ℝ))

theorem no_pairwise_gluing : ¬ ∃ d : FiniteDistribution Triple, GluesPairwise d := by
  rintro ⟨d, hab, hbc, hac⟩
  have ab0 := hab false false
  have ab1 := hab true true
  have bc0 := hbc false false
  have bc1 := hbc true true
  have ac0 := hac false false
  have ac1 := hac true true
  have h000 := d.nonneg (false,false,false)
  have h001 := d.nonneg (false,false,true)
  have h010 := d.nonneg (false,true,false)
  have h011 := d.nonneg (false,true,true)
  have h100 := d.nonneg (true,false,false)
  have h101 := d.nonneg (true,false,true)
  have h110 := d.nonneg (true,true,false)
  have h111 := d.nonneg (true,true,true)
  have ht := d.total
  simp [pairwise, Fintype.sum_prod_type] at ab0 ab1 bc0 bc1 ac0 ac1 ht
  linarith

/-- P05/P08: any randomized response to one classical bit guesses parity with 1/2.
The theorem includes all valid stochastic responses (and algebraically more). -/
theorem restricted_recovery (d : Bool → Rat) : oneBitRecovery d = 1/2 := by
  simp [oneBitRecovery, success, Bool.xor]
  ring

theorem joint_recovery : jointRecovery xor = 1 := by
  norm_num [jointRecovery, Bool.xor]

/-- Arbitrary real stochastic decoder responses obey the same parity obstruction.
This is the expansion of the four equally likely input cases. -/
theorem real_randomized_recovery (d : Bool → ℝ) :
    ((1-d false) + d false + d true + (1-d true))/4 = 1/2 := by ring

/-- A passive bijective relabeling, when undone by the decoder, changes no event. -/
theorem passive_relabel (f g : Bool → Bool) (h : ∀ b, g (f b) = b) (a b : Bool) :
    xor (g (f a)) (g (f b)) = xor a b := by rw [h, h]

/-- A randomized choice of queried bit also gives 1/2. Second-bit access is reduced
by symmetry of parity; this is not a coherent quantum-query lower bound. -/
theorem random_query_bound (q : Rat) (d e : Bool → Rat) :
    q * oneBitRecovery d + (1-q) * oneBitRecovery e = 1/2 := by
  rw [restricted_recovery, restricted_recovery]
  ring

/-- P06: XZ = -ZX; this is an order-interference calibration only. -/
theorem order_anticommutes (v : Vector) (b : Bool) :
    xGate (zGate v) b = -zGate (xGate v) b := by
  cases b <;> simp [xGate, zGate]

theorem order_probability (v : Vector) : orderMinus v = normSq v := by
  simp [orderMinus, normSq, xGate, zGate]
  ring

theorem dephased_order_probability (v : Vector) : orderDephased v = normSq v / 2 := by
  simp [orderDephased, normSq, xGate, zGate]
  ring

theorem noisy_order_probability (p : Rat) (v : Vector) (h : normSq v = 1) :
    noisyOrder p v = 1-p/2 := by
  rw [noisyOrder, order_probability, dephased_order_probability, h]
  ring

/-- P07: a pure product amplitude always has zero determinant. -/
theorem product_determinant (a b : Vector) : determinant (product a b) = 0 := by
  simp [determinant, product]
  ring

theorem phase_state_normalized :
    phaseState false false ^ 2 + phaseState false true ^ 2 +
    phaseState true false ^ 2 + phaseState true true ^ 2 = 1 := by
  norm_num [phaseState]

theorem phase_state_entangled : ¬ ∃ a b : Vector, product a b = phaseState := by
  rintro ⟨a,b,h⟩
  have hz := product_determinant a b
  rw [h] at hz
  norm_num [determinant, phaseState] at hz

/-- The product obstruction also excludes COMPLEX product amplitudes, not just
rational or real factors. Nonzero determinant is enough; no optimizer is used. -/
theorem phase_state_not_complex_product :
    ¬ ∃ a b : Bool → ℂ, ∀ i j, a i * b j = (phaseState i j : ℂ) := by
  rintro ⟨a,b,h⟩
  have hd : (phaseState false false : ℂ) * (phaseState true true : ℂ) -
      (phaseState false true : ℂ) * (phaseState true false : ℂ) = 0 := by
    rw [← h false false, ← h true true, ← h false true, ← h true false]
    ring
  norm_num [phaseState] at hd

/-- P10: public joint records obey the triangle inequality for disagreement. -/
theorem disagreement_triangle (a b c : Bool) :
    mismatch a c ≤ mismatch a b + mismatch b c := by
  cases a <;> cases b <;> cases c <;> norm_num [mismatch]

theorem public_error_bound (d : FiniteDistribution Triple) :
    d.mean (fun v => (mismatch v.1 v.2.2 : ℝ)) ≤
    d.mean (fun v => (mismatch v.1 v.2.1 : ℝ)) +
    d.mean (fun v => (mismatch v.2.1 v.2.2 : ℝ)) := by
  unfold FiniteDistribution.mean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (d.nonneg v)
  dsimp only
  exact_mod_cast disagreement_triangle v.1 v.2.1 v.2.2

/-- Generic contamination tradeoff. A separate adapter supplies the good/bad ceilings. -/
theorem contamination_bound (epsilon good bad L U : Rat)
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hg : good ≤ L) (hb : bad ≤ U) :
    contaminatedScore epsilon good bad ≤ (1-epsilon)*L + epsilon*U := by
  unfold contaminatedScore
  exact add_le_add (mul_le_mul_of_nonneg_left hg (by linarith))
    (mul_le_mul_of_nonneg_left hb he)

end OntologySeparation.Research
