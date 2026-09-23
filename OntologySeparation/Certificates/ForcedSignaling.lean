import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
A feasibility port of the K=8 rational dual from stevenwarejones/forced-signaling,
commit bae83b865ea60b1fbc4b808e66dc9bbaf7da2d4b (MIT).

This proves the bound for the explicitly reconstructed finite linear program.
It does not yet prove the physical conditional-locality → LP representation,
the matching lower certificate, or the cluster-state signaling optimum.
-/
namespace OntologySeparation.ForcedSignaling
open scoped BigOperators

/-- 256 hidden-response weights, followed by 128 absolute-difference auxiliaries. -/
abbrev Column := Fin 384
abbrev Row := Fin 272

private def sign (n : ℕ) : ℤ := if n % 2 = 0 then 1 else -1
private def response (fn setting : ℕ) : ℕ := fn / (2 ^ setting) % 2

/-- Coefficients of the specified operational completion of S₄.
Weight index order: `(x,w,a,d,fB,fC)` with radices `(2,2,2,2,4,4)`. -/
def objective (j : Column) : ℤ :=
  let x := j.val / 128
  let w := j.val / 64 % 2
  let a := j.val / 32 % 2
  let d := j.val / 16 % 2
  let b := j.val / 4 % 4
  let c := j.val % 4
  if j.val ≥ 256 then 0
  else if x = 0 ∧ w = 1 then
    sign (a + response b 0) + sign (a + response b 1) +
      2 * sign (a + response c 1 + d)
  else if x = 1 ∧ w = 0 then
    sign (a + response b 0 + d) - sign (a + response b 1 + d) +
      2 * sign (response c 0 + d)
  else 0

/-- The first 256 rows bound each signed recipient-probability difference
by its auxiliary. The final 16 rows bound each sum of eight auxiliaries by 2Δ.
Contexts 0..7 change x and fix (w,y,z); 8..15 change w and fix (x,y,z).
Recipient output order is (b,c,d), respectively (a,b,c). -/
def constraint (i : Row) (j : Column) : ℤ :=
  if i.val ≥ 256 then
    if j.val ≥ 256 ∧ (j.val - 256) / 8 = i.val - 256 then 1 else 0
  else
    let ctx := i.val / 16
    let out := i.val / 2 % 8
    if j.val ≥ 256 then
      if j.val = 256 + ctx * 8 + out then -1 else 0
    else
      let x := j.val / 128
      let w := j.val / 64 % 2
      let a := j.val / 32 % 2
      let d := j.val / 16 % 2
      let b := response (j.val / 4 % 4) (ctx / 2 % 2)
      let c := response (j.val % 4) (ctx % 2)
      let direction := if i.val % 2 = 0 then (1 : ℤ) else -1
      if ctx < 8 then
        if w = ctx / 4 ∧ b = out / 4 ∧ c = out / 2 % 2 ∧ d = out % 2
        then direction * sign x else 0
      else
        if x = (ctx - 8) / 4 ∧ a = out / 4 ∧ b = out / 2 % 2 ∧ c = out % 2
        then direction * sign w else 0

/-- The four per-(x,w) normalization rows. -/
def normalization (k : Fin 4) (j : Column) : ℤ :=
  if j.val < 256 ∧ j.val / 64 = k.val then 1 else 0

def normalizationDual (k : Fin 4) : ℤ := if k.val = 0 then 0 else 2

/-- Exactly the 36 unit-weight nonzero entries in K8_certificate.json. -/
def support (k : Fin 36) : Row :=
  let entries : Array Row := #[
  80,83,85,86,89,90,92,95,112,115,117,118,121,122,124,127,
  192,195,197,198,201,202,204,207,225,226,228,231,232,235,237,238,
  261,263,268,270]
  entries[k.val]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact columnwise dual feasibility, checked by the Lean kernel. -/
theorem dual_feasible : ∀ j : Column,
    objective j ≤ (∑ k : Fin 4, normalizationDual k * normalization k j) +
      ∑ k : Fin 36, constraint (support k) j := by decide

noncomputable def pairing (a : Column → ℤ) (z : Column → ℝ) : ℝ :=
  ∑ j, (a j : ℝ) * z j

/-- A normalized point of this finite LP. These are explicit mathematical
constraints, not an assertion that a physical apparatus satisfies them. -/
structure Feasible (delta : ℝ) where
  weights : Column → ℝ
  nonnegative : ∀ j, 0 ≤ weights j
  normalized : ∀ k, pairing (normalization k) weights = 1
  bounded : ∀ i, pairing (constraint i) weights ≤ if i.val < 256 then 0 else 2 * delta

/-- K=8 upper certificate, for all real feasible points and real budgets.
The conclusion is conditional on the entire stated LP, not just normalization. -/
theorem bound (delta : ℝ) (m : Feasible delta) :
    pairing objective m.weights ≤ 6 + 8 * delta := by
  have hcol (j : Column) : (objective j : ℝ) ≤
      (∑ k : Fin 4, (normalizationDual k : ℝ) * (normalization k j : ℝ)) +
        ∑ k : Fin 36, (constraint (support k) j : ℝ) := by
    exact_mod_cast dual_feasible j
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hcol j) (m.nonnegative j))
  have hn : (∑ k : Fin 4, (normalizationDual k : ℝ) *
      pairing (normalization k) m.weights) = 6 := by
    norm_num [m.normalized, normalizationDual, Fin.sum_univ_succ]
  have hr : (∑ k : Fin 36, pairing (constraint (support k)) m.weights) ≤ 8 * delta := by
    calc
      _ ≤ ∑ k : Fin 36, (if (support k).val < 256 then (0 : ℝ) else 2 * delta) :=
        Finset.sum_le_sum fun k _ => m.bounded (support k)
      _ = _ := by norm_num [support, Fin.sum_univ_succ]; ring
  have heq : (∑ j : Column,
      ((∑ k : Fin 4, (normalizationDual k : ℝ) * (normalization k j : ℝ)) +
        ∑ k : Fin 36, (constraint (support k) j : ℝ)) * m.weights j) =
      (∑ k : Fin 4, (normalizationDual k : ℝ) * pairing (normalization k) m.weights) +
        ∑ k : Fin 36, pairing (constraint (support k)) m.weights := by
    simp only [pairing, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    congr 1 <;> rw [Finset.sum_comm]
  change pairing objective m.weights ≤ _ at h
  rw [heq, hn] at h
  linarith

/-- A deterministic all-zero-output LP point, one weight in each setting block. -/
def zeroOutputs (j : Column) : ℝ :=
  (if j = 0 then 1 else 0) + (if j = 64 then 1 else 0) +
    (if j = 128 then 1 else 0) + (if j = 192 then 1 else 0)

private theorem zeroOutputs_pairing (a : Column → ℤ) :
    pairing a zeroOutputs = (a 0 : ℝ) + a 64 + a 128 + a 192 := by
  simp [pairing, zeroOutputs, mul_add, Finset.sum_add_distrib, mul_ite]

set_option maxRecDepth 100000 in
private theorem zeroOutputs_rows : ∀ i : Row,
    constraint i 0 + constraint i 64 + constraint i 128 + constraint i 192 ≤ 0 := by
  decide

/-- The zero-budget domain is inhabited; the intercept 6 is attained. This is
not a proof that the penalty slope 8 is optimal. -/
noncomputable def zeroBudget : Feasible 0 where
  weights := zeroOutputs
  nonnegative j := by
    unfold zeroOutputs
    positivity
  normalized k := by
    rw [zeroOutputs_pairing]
    fin_cases k <;> norm_num [normalization]
  bounded i := by
    rw [zeroOutputs_pairing]
    have h : (constraint i 0 : ℝ) + constraint i 64 + constraint i 128 +
        constraint i 192 ≤ 0 := by exact_mod_cast zeroOutputs_rows i
    simpa using h

theorem zeroBudget_score : pairing objective zeroBudget.weights = 6 := by
  change pairing objective zeroOutputs = 6
  rw [zeroOutputs_pairing]
  norm_num [objective, sign, response]

end OntologySeparation.ForcedSignaling
