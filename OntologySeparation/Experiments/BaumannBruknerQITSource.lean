import OntologySeparation.Experiments.BaumannBruknerProtocol
import QIT.Measurements.Projective

/-!
# Baumann--Brukner Sec. 3: explicit QIT source and Bob measurements

This file replaces the hand-entered branch-weight triples in
`BaumannBruknerProtocol` by an explicit two-qubit QIT state and two
projective measurements on Bob's qubit.

The logical left qubit represents the two friend/system branches after the
friend premeasurement.  The source is the Bell-type state
(|0,1⟩ + |1,0⟩)/√2.

For each Bob outcome we form the unnormalized conditional friend block
  σ_fg = Σ_{u,v} ρ_(f,u),(g,v) E_b(v,u),
where E_b is Bob's projective effect.  Lean proves these blocks have exactly
the diagonal weights and cross terms used by the concrete Sec. 3 bridge.
-/

namespace OntologySeparation.BaumannBruknerQITSource
noncomputable section
open scoped ComplexOrder MatrixOrder

abbrev Registers := Bool × Bool

def s : ℝ := Real.sqrt 2 / 2

theorem s_sq : s ^ 2 = 1/2 := by
  unfold s
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

def source : QIT.PureVector Registers where
  amp i := if i.1 = i.2 then 0 else (s : ℂ)
  trace_rankOne_eq_one := by
    apply Complex.ext <;>
      norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
        Fintype.sum_prod_type, Fintype.sum_bool, s] <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

def state : QIT.State Registers := source.state

def computationalEffect (o i j : Bool) : ℂ :=
  if i = j ∧ i = o then 1 else 0

def computational : QIT.ProjectiveMeasurement Bool Bool where
  effects o := fun i j => computationalEffect o i j
  isHermitian := by
    intro o
    ext i j
    cases o <;> cases i <;> cases j <;>
      simp [computationalEffect, Matrix.conjTranspose_apply]
  idempotent := by
    intro o
    ext i j
    cases o <;> cases i <;> cases j <;>
      norm_num [computationalEffect, Matrix.mul_apply, Fintype.sum_bool]
  orthogonal := by
    intro i j hij
    ext r c
    cases i <;> cases j <;> cases r <;> cases c <;>
      norm_num [computationalEffect, Matrix.mul_apply, Fintype.sum_bool] at hij ⊢
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;>
      norm_num [computationalEffect, Matrix.one_apply, Fintype.sum_bool]

def r : ℝ := BaumannBruknerProtocol.sqrtTwo

def rotatedEffect (o i j : Bool) : ℂ :=
  match o, i, j with
  | false, false, false => 1/3
  | false, false, true  => r/3
  | false, true, false  => r/3
  | false, true, true   => 2/3
  | true,  false, false => 2/3
  | true,  false, true  => -r/3
  | true,  true, false  => -r/3
  | true,  true, true   => 1/3

def rotated : QIT.ProjectiveMeasurement Bool Bool where
  effects o := fun i j => rotatedEffect o i j
  isHermitian := by
    intro o
    ext i j
    cases o <;> cases i <;> cases j <;>
      simp [rotatedEffect, Matrix.conjTranspose_apply, r,
        BaumannBruknerProtocol.sqrtTwo]
  idempotent := by
    intro o
    ext i j
    cases o <;> cases i <;> cases j <;>
      norm_num [rotatedEffect, Matrix.mul_apply, Fintype.sum_bool, r] <;>
      nlinarith [BaumannBruknerProtocol.sqrtTwo_sq]
  orthogonal := by
    intro i j hij
    ext a b
    cases i <;> cases j <;> cases a <;> cases b <;>
      norm_num [rotatedEffect, Matrix.mul_apply, Fintype.sum_bool, r] at hij ⊢ <;>
      nlinarith [BaumannBruknerProtocol.sqrtTwo_sq]
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;>
      norm_num [rotatedEffect, Matrix.one_apply, Fintype.sum_bool]

/-- Unnormalized friend density block after selecting Bob's outcome. -/
def conditionalFriend
    (M : QIT.ProjectiveMeasurement Bool Bool) (b f g : Bool) : ℂ :=
  ∑ u : Bool, ∑ v : Bool,
    state.matrix (f,u) (g,v) * M.effects b v u

theorem computational_conditional (b f g : Bool) :
    conditionalFriend computational b f g =
      match b, f, g with
      | false, true,  true  => 1/2
      | true,  false, false => 1/2
      | _, _, _ => 0 := by
  cases b <;> cases f <;> cases g <;>
    norm_num [conditionalFriend, computational, computationalEffect,
      state, source, QIT.PureVector.state, QIT.rankOneMatrix,
      Matrix.vecMulVec, Fintype.sum_bool, s] <;>
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem rotated_conditional (b f g : Bool) :
    conditionalFriend rotated b f g =
      match b, f, g with
      | false, false, false => 1/3
      | false, true,  true  => 1/6
      | false, false, true  => (r : ℂ)/6
      | false, true,  false => (r : ℂ)/6
      | true,  false, false => 1/6
      | true,  true,  true  => 1/3
      | true,  false, true  => -(r : ℂ)/6
      | true,  true,  false => -(r : ℂ)/6 := by
  cases b <;> cases f <;> cases g <;>
    norm_num [conditionalFriend, rotated, rotatedEffect,
      state, source, QIT.PureVector.state, QIT.rankOneMatrix,
      Matrix.vecMulVec, Fintype.sum_bool, s, r] <;>
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      BaumannBruknerProtocol.sqrtTwo_sq]

/-- The diagonal and real cross terms are exactly the branch data used in #65. -/
theorem computational_branch_data (b : Bool) :
    ( (conditionalFriend computational b false false).re,
      (conditionalFriend computational b true true).re,
      (conditionalFriend computational b false true).re ) =
    let d := BaumannBruknerProtocol.computationalBranch b
    (d.x2, d.y2, d.xy) := by
  cases b <;>
    norm_num [BaumannBruknerProtocol.computationalBranch,
      computational_conditional]

theorem rotated_branch_data (b : Bool) :
    ( (conditionalFriend rotated b false false).re,
      (conditionalFriend rotated b true true).re,
      (conditionalFriend rotated b false true).re ) =
    let d := BaumannBruknerProtocol.rotatedBranch b
    (d.x2, d.y2, d.xy) := by
  cases b <;>
    simp [BaumannBruknerProtocol.rotatedBranch, rotated_conditional, r,
      BaumannBruknerProtocol.sqrtTwo]

end
end OntologySeparation.BaumannBruknerQITSource
