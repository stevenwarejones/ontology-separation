import OntologySeparation.Experiments.LFAgencyRelaxationDiagnostics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NativeDecide

/-!
# Exact sqrt(2) Local-Agency relaxation bound

This module proves the explicit-angle result deferred by PR #46.  It does not
claim global optimality over measurement angles.

The target public table is the singlet table for the pi/8-grid choice

* Alice: 0, -pi/4, pi/4
* Bob: -3pi/8, pi/4, -pi/8

written directly in exact correlation coordinates.  For every AOE joint
extension with exact friend readout and setting-independent friend records, at
least one of two record-revealed remote-setting comparisons has total variation
at least (sqrt 2 - 1)/2.
-/

namespace OntologySeparation.LFAgencyRelaxation
noncomputable section
open LFJoint

def rootHalf : ℝ := Real.sqrt 2 / 2

def sqrtTwoCorr (x y : Fin 3) : ℝ :=
  (#[rootHalf, 0, -rootHalf,
     -rootHalf, 1, -rootHalf,
     rootHalf, -1, rootHalf] : Array ℝ)[3*x.val + y.val]

def sqrtTwoProb (xy : Fin 3 × Fin 3) (ab : Bool × Bool) : ℝ :=
  (1 + RealQuantum.sign ab.1 * RealQuantum.sign ab.2 *
    sqrtTwoCorr xy.1 xy.2) / 4

private theorem sqrt_two_bounds : (0 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 := by
  constructor
  · exact Real.sqrt_nonneg 2
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg 2
    nlinarith

private theorem rootHalf_bounds : (-1 : ℝ) ≤ rootHalf ∧ rootHalf ≤ 1 := by
  rcases sqrt_two_bounds with ⟨h0,h2⟩
  unfold rootHalf
  constructor <;> linarith

theorem sqrtTwoProb_nonneg (xy : Fin 3 × Fin 3) (ab : Bool × Bool) :
    0 ≤ sqrtTwoProb xy ab := by
  rcases xy with ⟨x,y⟩
  rcases ab with ⟨a,b⟩
  fin_cases x <;> fin_cases y <;> cases a <;> cases b <;>
    simp [sqrtTwoProb, sqrtTwoCorr, rootHalf, RealQuantum.sign] <;>
    rcases rootHalf_bounds with ⟨h0,h1⟩ <;> linarith

def sqrtTwoBehavior : Behavior LF.interface where
  prob := sqrtTwoProb
  nonneg := sqrtTwoProb_nonneg
  normalized xy := by
    rcases xy with ⟨x,y⟩
    fin_cases x <;> fin_cases y <;>
      simp [sqrtTwoProb, sqrtTwoCorr, RealQuantum.sign, Fintype.sum_prod_type] <;> ring

theorem sqrtTwoBehavior_public_noSignaling : Shared.NoSignaling sqrtTwoBehavior := by
  constructor
  · intro x y y' a
    cases a <;> fin_cases x <;> fin_cases y <;> fin_cases y' <;>
      simp [sqrtTwoBehavior, sqrtTwoProb, sqrtTwoCorr, RealQuantum.sign]
  · intro x x' y b
    cases b <;> fin_cases x <;> fin_cases x' <;> fin_cases y <;>
      simp [sqrtTwoBehavior, sqrtTwoProb, sqrtTwoCorr, RealQuantum.sign]

def sqrtTwoDelta : ℝ := (Real.sqrt 2 - 1) / 2

theorem sqrtTwoDelta_positive : 0 < sqrtTwoDelta := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  unfold sqrtTwoDelta
  nlinarith

end
end OntologySeparation.LFAgencyRelaxation
