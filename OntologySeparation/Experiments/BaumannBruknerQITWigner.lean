import OntologySeparation.Experiments.BaumannBruknerQITSource

/-!
# Baumann--Brukner Sec. 3: explicit QIT Wigner pinching channel

Part 2 of the physical bridge.

Wigner's unread measurement is represented as a two-outcome projective
measurement on the logical friend/system branch qubit.  The corresponding QIT
`ProjectiveMeasurement.pinchingMap` is then applied directly to the
unnormalized conditional friend blocks obtained in
`BaumannBruknerQITSource`.

Lean proves that the resulting diagonal friend probabilities are exactly the
post-Wigner tables used in the concrete Sec. 3 derivation.
-/

namespace OntologySeparation.BaumannBruknerQITWigner
noncomputable section
open scoped ComplexOrder MatrixOrder

open BaumannBruknerQITSource
open BaumannBruknerProtocol

def r : ℝ := BaumannBruknerProtocol.sqrtTwo

/-- Projectors onto the ±π/8 Wigner basis, written directly as matrices so no
nested square roots enter the trusted arithmetic. -/
def wignerEffect (o i j : Bool) : ℂ :=
  match o, i, j with
  | false, false, false => (2 + r)/4
  | false, false, true  => -r/4
  | false, true, false  => -r/4
  | false, true, true   => (2 - r)/4
  | true,  false, false => (2 - r)/4
  | true,  false, true  => r/4
  | true,  true, false  => r/4
  | true,  true, true   => (2 + r)/4

def wigner : QIT.ProjectiveMeasurement Bool Bool where
  effects o := fun i j => wignerEffect o i j
  isHermitian := by
    intro o
    ext i j
    cases o <;> cases i <;> cases j <;>
      simp [wignerEffect, Matrix.conjTranspose_apply, r,
        BaumannBruknerProtocol.sqrtTwo]
  idempotent := by
    intro o
    ext i j
    apply Complex.ext <;>
      cases o <;> cases i <;> cases j <;>
      norm_num [wignerEffect, Matrix.mul_apply, Fintype.sum_bool, r, BaumannBruknerProtocol.sqrtTwo] <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  orthogonal := by
    intro i j hij
    ext a b
    apply Complex.ext <;>
      cases i <;> cases j <;> cases a <;> cases b <;>
      norm_num [wignerEffect, Matrix.mul_apply, Fintype.sum_bool, r, BaumannBruknerProtocol.sqrtTwo] at * <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  sum_eq_one := by
    ext i j
    cases i <;> cases j <;>
      norm_num [wignerEffect, Matrix.one_apply, Fintype.sum_bool] <;> ring

def conditionalMatrix
    (M : QIT.ProjectiveMeasurement Bool Bool) (b : Bool) :
    Matrix Bool Bool ℂ :=
  fun f g => BaumannBruknerQITSource.conditionalFriend M b f g

def pinchedFriendProb
    (M : QIT.ProjectiveMeasurement Bool Bool) (b f : Bool) : ℝ :=
  ((wigner.pinchingMap (conditionalMatrix M b)) f f).re

/-- Wigner's QIT pinching reproduces the computational-Bob post-measurement
friend/Bob table. -/
theorem computational_after_qit (f b : Bool) :
    pinchedFriendProb BaumannBruknerQITSource.computational b f =
      BaumannBruknerProtocol.computationalAfter f b := by
  cases f <;> cases b <;>
    simp [pinchedFriendProb, conditionalMatrix,
      QIT.ProjectiveMeasurement.pinchingMap_apply, wigner, wignerEffect,
      BaumannBruknerQITSource.computational_conditional,
      BaumannBruknerProtocol.computationalAfter, r,
      Matrix.mul_apply, Fintype.sum_bool] <;>
    norm_num <;>
    nlinarith [BaumannBruknerProtocol.sqrtTwo_sq,
      congrArg (fun x : ℝ => BaumannBruknerProtocol.sqrtTwo * x)
        BaumannBruknerProtocol.sqrtTwo_sq]

/-- Wigner's QIT pinching reproduces the rotated-Bob post-measurement table. -/
theorem rotated_after_qit (f b : Bool) :
    pinchedFriendProb BaumannBruknerQITSource.rotated b f =
      BaumannBruknerProtocol.rotatedAfter f b := by
  cases f <;> cases b <;>
    simp [pinchedFriendProb, conditionalMatrix,
      QIT.ProjectiveMeasurement.pinchingMap_apply, wigner, wignerEffect,
      BaumannBruknerQITSource.rotated_conditional,
      BaumannBruknerProtocol.rotatedAfter, r,
      Matrix.mul_apply, Fintype.sum_bool,
      BaumannBruknerQITSource.r] <;>
    ring_nf <;>
    nlinarith [BaumannBruknerProtocol.sqrtTwo_sq,
      congrArg (fun x : ℝ => BaumannBruknerProtocol.sqrtTwo * x)
        BaumannBruknerProtocol.sqrtTwo_sq]

/-- The full concrete Sec. 3 setting dependence is now chained to explicit QIT
source, Bob projectors, and Wigner pinching dynamics. -/
theorem qit_setting_dependence :
    BaumannBruknerProtocol.qComputational < 1/2 ∧
    1/2 < BaumannBruknerProtocol.qRotated ∧
    BaumannBruknerProtocol.qRotated ≤ 1 :=
  BaumannBruknerProtocol.exact_setting_dependence

end
end OntologySeparation.BaumannBruknerQITWigner
