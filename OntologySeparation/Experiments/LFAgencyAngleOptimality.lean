import OntologySeparation.Experiments.LFAgencyRelaxationSqrtTwo
import Mathlib.Tactic

/-!
# Global angle bound for the readout-anchored witness

The LP certificate used by the explicit-angle theorem has public part

  (E₀₀ - E₀y + Eₓ₀ + Eₓy - 2) / 4.

This module proves, for arbitrary real projective qubit bases, that the
four-correlator CHSH numerator is at most 2*sqrt(2).  Consequently no choice of
measurement angles can make this witness exceed (sqrt(2)-1)/2.  The explicit
pi/8-grid bases attain equality.

This is an analytic angle optimization of the witness itself; no numerical
optimizer is trusted.
-/

namespace OntologySeparation.LFAgencyRelaxation.AngleOptimality
noncomputable section

def blochX (a : RealQuantum.Basis) : ℝ := a.c^2 - a.s^2
def blochY (a : RealQuantum.Basis) : ℝ := 2*a.c*a.s

theorem bloch_unit (a : RealQuantum.Basis) :
    blochX a ^ 2 + blochY a ^ 2 = 1 := by
  unfold blochX blochY
  have h := a.unit
  nlinarith [sq_nonneg (a.c^2 - a.s^2)]

def basisCorr (a b : RealQuantum.Basis) : ℝ :=
  ∑ o : Bool × Bool,
    RealQuantum.sign o.1 * RealQuantum.sign o.2 *
      RealQuantum.probability a b o.1 o.2

theorem basisCorr_formula (a b : RealQuantum.Basis) :
    basisCorr a b = -(blochX a * blochX b + blochY a * blochY b) := by
  simp [basisCorr, RealQuantum.probability, RealQuantum.Basis.vector,
    RealQuantum.sign, Fintype.sum_prod_type, blochX, blochY]
  ring

theorem correlator_behavior (A B : Fin 3 → RealQuantum.Basis) (x y : Fin 3) :
    RealQuantum.correlator (RealQuantum.behavior A B) x y = basisCorr (A x) (B y) := by
  rfl

def chshNumerator (a0 a1 b0 b1 : RealQuantum.Basis) : ℝ :=
  basisCorr a0 b0 - basisCorr a0 b1 + basisCorr a1 b0 + basisCorr a1 b1

/-- Elementary Tsirelson bound specialized to the real qubit bases used here.
The proof is the sum of four squares
  (sqrt(2) p - q)^2 >= 0,
plus the four Bloch-vector unit identities. -/
theorem chshNumerator_le (a0 a1 b0 b1 : RealQuantum.Basis) :
    chshNumerator a0 a1 b0 b1 ≤ 2 * Real.sqrt 2 := by
  let s : ℝ := Real.sqrt 2
  let a0x := blochX a0
  let a0y := blochY a0
  let a1x := blochX a1
  let a1y := blochY a1
  let b0x := blochX b0
  let b0y := blochY b0
  let b1x := blochX b1
  let b1y := blochY b1
  have hs0 : 0 ≤ s := by dsimp [s]; exact Real.sqrt_nonneg 2
  have hs2 : s^2 = 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have ha0 : a0x^2 + a0y^2 = 1 := by simpa [a0x, a0y] using bloch_unit a0
  have ha1 : a1x^2 + a1y^2 = 1 := by simpa [a1x, a1y] using bloch_unit a1
  have hb0 : b0x^2 + b0y^2 = 1 := by simpa [b0x, b0y] using bloch_unit b0
  have hb1 : b1x^2 + b1y^2 = 1 := by simpa [b1x, b1y] using bloch_unit b1
  have h1 := sq_nonneg (s*a0x - (b1x-b0x))
  have h2 := sq_nonneg (s*a0y - (b1y-b0y))
  have h3 := sq_nonneg (s*a1x + (b0x+b1x))
  have h4 := sq_nonneg (s*a1y + (b0y+b1y))
  have hc :
      chshNumerator a0 a1 b0 b1 =
        a0x*(b1x-b0x) + a0y*(b1y-b0y) -
        a1x*(b0x+b1x) - a1y*(b0y+b1y) := by
    simp [chshNumerator, basisCorr_formula, a0x, a0y, a1x, a1y,
      b0x, b0y, b1x, b1y]
    ring
  rw [hc]
  nlinarith

def anchoredWitness (a0 a1 b0 b1 : RealQuantum.Basis) : ℝ :=
  (chshNumerator a0 a1 b0 b1 - 2) / 4

theorem anchoredWitness_le_sqrtTwoDelta (a0 a1 b0 b1 : RealQuantum.Basis) :
    anchoredWitness a0 a1 b0 b1 ≤ sqrtTwoDelta := by
  have h := chshNumerator_le a0 a1 b0 b1
  unfold anchoredWitness sqrtTwoDelta
  linarith

theorem explicit_chshNumerator :
    chshNumerator (explicitAlice 0) (explicitAlice 2)
      (explicitBob 0) (explicitBob 2) = 2 * Real.sqrt 2 := by
  rw [show explicitAlice 0 = RealQuantum.zBasis by rfl]
  simp [chshNumerator, basisCorr_formula, explicitAlice, explicitBob,
    blochX, blochY, rootHalf, RealQuantum.zBasis]
  rcases root_identities with ⟨hs,hp,hm,hpm⟩
  ring_nf
  nlinarith

theorem explicit_anchoredWitness :
    anchoredWitness (explicitAlice 0) (explicitAlice 2)
      (explicitBob 0) (explicitBob 2) = sqrtTwoDelta := by
  rw [anchoredWitness, explicit_chshNumerator]
  unfold sqrtTwoDelta
  ring

/-- Exact global optimization of the readout-anchored witness over all real
projective measurement angles, with the pi/8-grid construction attaining it. -/
theorem anchoredWitness_global_optimum :
    (∀ a0 a1 b0 b1 : RealQuantum.Basis,
      anchoredWitness a0 a1 b0 b1 ≤ sqrtTwoDelta) ∧
    ∃ a0 a1 b0 b1 : RealQuantum.Basis,
      anchoredWitness a0 a1 b0 b1 = sqrtTwoDelta := by
  refine ⟨anchoredWitness_le_sqrtTwoDelta, ?_⟩
  exact ⟨explicitAlice 0, explicitAlice 2, explicitBob 0, explicitBob 2,
    explicit_anchoredWitness⟩

end
end OntologySeparation.LFAgencyRelaxation.AngleOptimality
