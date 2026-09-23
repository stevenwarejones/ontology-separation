import OntologySeparation.Experiments.LFAgencyRelaxationDiagnostics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

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


def rootPlus : ℝ := Real.sqrt (2 + Real.sqrt 2)
def rootMinus : ℝ := Real.sqrt (2 - Real.sqrt 2)

private theorem root_identities :
    (Real.sqrt 2)^2 = 2 ∧ rootPlus^2 = 2 + Real.sqrt 2 ∧
      rootMinus^2 = 2 - Real.sqrt 2 ∧ rootPlus * rootMinus = Real.sqrt 2 := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsle : Real.sqrt 2 ≤ 2 := sqrt_two_bounds.2
  have hp0 : (0 : ℝ) ≤ rootPlus := by unfold rootPlus; positivity
  have hm0 : (0 : ℝ) ≤ rootMinus := by unfold rootMinus; positivity
  have hp2 : rootPlus^2 = 2 + Real.sqrt 2 := by
    unfold rootPlus
    rw [Real.sq_sqrt]
    linarith
  have hm2 : rootMinus^2 = 2 - Real.sqrt 2 := by
    unfold rootMinus
    rw [Real.sq_sqrt]
    linarith
  have hprod2 : (rootPlus * rootMinus)^2 = 2 := by
    calc
      (rootPlus * rootMinus)^2 = rootPlus^2 * rootMinus^2 := by ring
      _ = (2 + Real.sqrt 2) * (2 - Real.sqrt 2) := by rw [hp2, hm2]
      _ = 2 := by nlinarith
  have hprod0 : 0 ≤ rootPlus * rootMinus := mul_nonneg hp0 hm0
  have hprod : rootPlus * rootMinus = Real.sqrt 2 := by
    nlinarith
  exact ⟨hs2, hp2, hm2, hprod⟩

def explicitAlice (x : Fin 3) : RealQuantum.Basis :=
  match x.val with
  | 0 => RealQuantum.zBasis
  | 1 => ⟨rootHalf, -rootHalf, by
      have hs := root_identities.1
      unfold rootHalf
      nlinarith⟩
  | _ => ⟨rootHalf, rootHalf, by
      have hs := root_identities.1
      unfold rootHalf
      nlinarith⟩

def explicitBob (y : Fin 3) : RealQuantum.Basis :=
  match y.val with
  | 0 => ⟨rootMinus / 2, -rootPlus / 2, by
      rcases root_identities with ⟨hs,hp,hm,hpm⟩
      nlinarith⟩
  | 1 => ⟨rootHalf, rootHalf, by
      have hs := root_identities.1
      unfold rootHalf
      nlinarith⟩
  | _ => ⟨rootPlus / 2, -rootMinus / 2, by
      rcases root_identities with ⟨hs,hp,hm,hpm⟩
      nlinarith⟩

theorem explicit_quantum_matches :
    RealQuantum.behavior explicitAlice explicitBob = sqrtTwoBehavior := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hp0 : (0 : ℝ) ≤ rootPlus := by unfold rootPlus; positivity
  have hm0 : (0 : ℝ) ≤ rootMinus := by unfold rootMinus; positivity
  rcases root_identities with ⟨hs,hp,hm,hpm⟩
  have he :
      (RealQuantum.behavior explicitAlice explicitBob).prob = sqrtTwoBehavior.prob := by
    funext xy ab
    rcases xy with ⟨x,y⟩
    rcases ab with ⟨a,b⟩
    fin_cases x <;> fin_cases y <;> cases a <;> cases b <;>
      simp [RealQuantum.behavior, RealQuantum.probability, RealQuantum.Basis.vector,
        explicitAlice, explicitBob, sqrtTwoBehavior, sqrtTwoProb, sqrtTwoCorr,
        rootHalf, RealQuantum.zBasis, RealQuantum.sign] <;>
      ring_nf <;> nlinarith
  cases ha : RealQuantum.behavior explicitAlice explicitBob
  cases hb : sqrtTwoBehavior
  simp only [ha, hb] at he
  cases he
  rfl

theorem explicit_quantum_realized : RealQuantum.singletTheory 3 sqrtTwoBehavior :=
  ⟨explicitAlice, explicitBob, explicit_quantum_matches⟩

def sqrtTwoDelta : ℝ := (Real.sqrt 2 - 1) / 2

theorem sqrtTwoDelta_positive : 0 < sqrtTwoDelta := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  unfold sqrtTwoDelta
  nlinarith

end
end OntologySeparation.LFAgencyRelaxation
