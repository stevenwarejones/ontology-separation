import OntologySeparation.Experiments.LFAgencyRelaxationSqrtTwo
import Mathlib.Tactic

/-!
# Global angle bound for the readout-anchored witness

The LP certificate used by the explicit-angle theorem has public part

  (E₀₀ - E₀y + Eₓ₀ + Eₓy - 2) / 4.

For arbitrary real projective qubit bases, the four-correlator numerator is at
most 2*sqrt(2).  The proof is elementary: four nonnegative squares plus the
four Bloch-vector unit identities.  The explicit pi/8-grid bases attain the
bound exactly.

This proves global angle optimality of the exact witness used by the certificate.
It does not claim a complete facet characterization of the broader
multi-comparison LP.
-/

namespace OntologySeparation.LFAgencyRelaxation.AngleOptimality
noncomputable section

abbrev blochX := Correlation.blochX
abbrev blochY := Correlation.blochY
abbrev basisCorr := Correlation.basisCorr

theorem bloch_unit (a : RealQuantum.Basis) :
    blochX a ^ 2 + blochY a ^ 2 = 1 :=
  Correlation.bloch_unit a

theorem basisCorr_formula (a b : RealQuantum.Basis) :
    basisCorr a b = -(blochX a * blochX b + blochY a * blochY b) :=
  Correlation.basisCorr_formula a b

theorem correlator_behavior (A B : Fin 3 → RealQuantum.Basis) (x y : Fin 3) :
    RealQuantum.correlator (RealQuantum.behavior A B) x y = basisCorr (A x) (B y) :=
  Correlation.correlator_behavior A B x y

def chshNumerator (a0 a1 b0 b1 : RealQuantum.Basis) : ℝ :=
  basisCorr a0 b0 - basisCorr a0 b1 + basisCorr a1 b0 + basisCorr a1 b1

/-- Elementary Tsirelson bound specialized to the exact real qubit model. -/
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
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg 2
  have hs2 : s^2 = 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have ha0 : a0x^2 + a0y^2 = 1 := by
    simpa [a0x, a0y] using bloch_unit a0
  have ha1 : a1x^2 + a1y^2 = 1 := by
    simpa [a1x, a1y] using bloch_unit a1
  have hb0 : b0x^2 + b0y^2 = 1 := by
    simpa [b0x, b0y] using bloch_unit b0
  have hb1 : b1x^2 + b1y^2 = 1 := by
    simpa [b1x, b1y] using bloch_unit b1
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
  unfold chshNumerator basisCorr
  rw [explicit_pair_corr 0 0, explicit_pair_corr 0 2,
    explicit_pair_corr 2 0, explicit_pair_corr 2 2]
  simp [sqrtTwoCorr, rootHalf]
  ring

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
