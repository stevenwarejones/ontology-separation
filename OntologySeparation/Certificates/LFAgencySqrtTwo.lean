import OntologySeparation.Experiments.LFAgencyRelaxationSqrtTwo

namespace OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate
noncomputable section
open scoped BigOperators

abbrev Column := Fin 160
abbrev EqRow := Fin 75
abbrev IneqRow := Fin 32

def fixedZeroIndex (k : Fin 7) : Fin 144 :=
  (#[8, 9, 11, 34, 38, 100, 108] : Array (Fin 144))[k.val]

def objective (j : Column) : ℤ := if j.val < 144 then 0 else 1

def eqCoeff (i : EqRow) (j : Column) : ℤ :=
  if hq : j.val < 144 then
    let q := j.val
    let x := q / 48
    let y := q / 16 % 3
    let r := q / 4 % 4
    let a := q / 2 % 2
    let b := q % 2
    if hp : i.val < 36 then
      let ix := i.val / 12
      let iy := i.val / 4 % 3
      let ia := i.val / 2 % 2
      let ib := i.val % 2
      if x = ix ∧ y = iy ∧ a = ia ∧ b = ib then 1 else 0
    else if hr : i.val < 68 then
      let k := i.val - 36
      let flat := k / 4 + 1
      let ix := flat / 3
      let iy := flat % 3
      let ir := k % 4
      if x = ix ∧ y = iy ∧ r = ir then 1
      else if x = 0 ∧ y = 0 ∧ r = ir then -1 else 0
    else
      if q = (fixedZeroIndex ⟨i.val - 68, by omega⟩).val then 1 else 0
  else 0

def ineqCoeff (i : IneqRow) (j : Column) : ℤ :=
  let k := i.val / 2
  let direction : ℤ := if i.val % 2 = 0 then 1 else -1
  if hq : j.val < 144 then
    let q := j.val
    let x := q / 48
    let y := q / 16 % 3
    let r := q / 4 % 4
    let a := q / 2 % 2
    let b := q % 2
    if hk : k < 8 then
      let kr := k / 2
      let ka := k % 2
      if r = kr ∧ a = ka then
        if x = 2 ∧ y = 0 then direction
        else if x = 2 ∧ y = 2 then -direction else 0
      else 0
    else
      let kk := k - 8
      let kr := kk / 2
      let kb := kk % 2
      if r = kr ∧ b = kb then
        if x = 0 ∧ y = 2 then direction
        else if x = 2 ∧ y = 2 then -direction else 0
      else 0
  else
    if j.val - 144 = k then -1 else 0

def eqDual (i : EqRow) : ℤ :=
  if i.val = 2 then -4
  else if i.val = 8 then -2
  else if i.val = 10 then 2
  else if i.val = 24 then 2
  else if i.val = 25 then -2
  else if i.val = 33 then -2
  else if i.val = 34 then -2
  else if i.val = 40 then 1
  else if i.val = 42 then -2
  else if i.val = 43 then -1
  else if i.val = 56 then -1
  else if i.val = 58 then -2
  else if i.val = 59 then 1
  else if i.val = 68 then -4
  else if i.val = 69 then -4
  else if i.val = 70 then -4
  else if i.val = 71 then -4
  else if i.val = 72 then -2
  else if i.val = 73 then -2
  else if i.val = 74 then -4
  else 0

def ineqDual (i : IneqRow) : ℤ :=
  if i.val = 0 ∨ i.val = 3 ∨ i.val = 13 ∨ i.val = 14 ∨
     i.val = 17 ∨ i.val = 18 ∨ i.val = 28 ∨ i.val = 31 then -1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dual_feasible : ∀ j : Column,
    (∑ i : EqRow, eqDual i * eqCoeff i j) +
      ∑ i : IneqRow, ineqDual i * ineqCoeff i j ≤ objective j := by
  native_decide

set_option maxRecDepth 100000 in
theorem ineqDual_nonpos : ∀ i : IneqRow, ineqDual i ≤ 0 := by
  native_decide

noncomputable def rhs (i : EqRow) : ℝ :=
  if h : i.val < 36 then
    let x : Fin 3 := ⟨i.val / 12, by omega⟩
    let y : Fin 3 := ⟨i.val / 4 % 3, by omega⟩
    let a : Bool := if i.val / 2 % 2 = 0 then false else true
    let b : Bool := if i.val % 2 = 0 then false else true
    sqrtTwoBehavior.prob (x,y) (a,b)
  else 0

noncomputable def pairing (a : Column → ℤ) (w : Column → ℝ) : ℝ :=
  ∑ j, (a j : ℝ) * w j

structure Feasible where
  weight : Column → ℝ
  nonnegative : ∀ j, 0 ≤ weight j
  equations : ∀ i, pairing (eqCoeff i) weight = rhs i
  inequalities : ∀ i, pairing (ineqCoeff i) weight ≤ 0

set_option maxRecDepth 100000 in
theorem dual_value :
    (∑ i : EqRow, (eqDual i : ℝ) * rhs i) = 2 * (Real.sqrt 2 - 1) := by
  simp only [eqDual, rhs, sqrtTwoBehavior, sqrtTwoProb, sqrtTwoCorr, rootHalf,
    RealQuantum.sign]
  norm_num [Fin.sum_univ_succ]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound (m : Feasible) :
    2 * (Real.sqrt 2 - 1) ≤ pairing objective m.weight := by
  have hcol (j : Column) :
      ((∑ i : EqRow, (eqDual i : ℝ) * (eqCoeff i j : ℝ)) +
        ∑ i : IneqRow, (ineqDual i : ℝ) * (ineqCoeff i j : ℝ)) ≤
          (objective j : ℝ) := by
    exact_mod_cast dual_feasible j
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hcol j) (m.nonnegative j))
  have hrearrange :
      (∑ j : Column,
        (((∑ i : EqRow, (eqDual i : ℝ) * (eqCoeff i j : ℝ)) +
          ∑ i : IneqRow, (ineqDual i : ℝ) * (ineqCoeff i j : ℝ)) * m.weight j)) =
      (∑ i : EqRow, (eqDual i : ℝ) * pairing (eqCoeff i) m.weight) +
        ∑ i : IneqRow, (ineqDual i : ℝ) * pairing (ineqCoeff i) m.weight := by
    simp only [pairing, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    congr 1 <;> rw [Finset.sum_comm]
  have hineq : 0 ≤ ∑ i : IneqRow,
      (ineqDual i : ℝ) * pairing (ineqCoeff i) m.weight := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg_of_nonpos_of_nonpos
      (by exact_mod_cast ineqDual_nonpos i) (m.inequalities i)
  have heq :
      (∑ i : EqRow, (eqDual i : ℝ) * pairing (eqCoeff i) m.weight) =
        2 * (Real.sqrt 2 - 1) := by
    simp_rw [m.equations]
    exact dual_value
  change (∑ j : Column,
    (((∑ i : EqRow, (eqDual i : ℝ) * (eqCoeff i j : ℝ)) +
      ∑ i : IneqRow, (ineqDual i : ℝ) * (ineqCoeff i j : ℝ)) * m.weight j)) ≤
        pairing objective m.weight at hsum
  rw [hrearrange, heq] at hsum
  linarith

end
end OntologySeparation.LFAgencyRelaxation.SqrtTwoCertificate
