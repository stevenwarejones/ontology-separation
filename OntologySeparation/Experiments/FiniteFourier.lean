import OntologySeparation.Experiments.ContinuumLimit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Normalized finite Fourier synthesis and its intertwining with the cyclic
kinetic generator. Fourier coefficients are a genuine finite representation of
N-site states; the orthogonality proof supplies norm preservation. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset
variable {N : ℕ} [NeZero N]

def modeVector (j : ZMod N) : EuclideanSpace ℂ (ZMod N) :=
  WithLp.toLp 2 (normalizedFourierMode j)

theorem modeVector_orthonormal : Orthonormal ℂ (modeVector (N := N)) := by
  constructor
  · intro j
    have h : ‖modeVector j‖^2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact normalizedFourierMode_mass j
    nlinarith [norm_nonneg (modeVector j)]
  · intro j k hjk
    have h := character_orthogonality j k
    rw [if_neg hjk] at h
    calc
      inner ℂ (modeVector j) (modeVector k) =
          (Real.sqrt (N : ℝ) : ℂ)⁻¹^2 *
            ∑ n : ZMod N, star (fourierCharacter j n)*fourierCharacter k n := by
        rw [PiLp.inner_apply,Finset.mul_sum]
        apply sum_congr rfl
        intro n _
        change inner ℂ ((Real.sqrt (N : ℝ) : ℂ)⁻¹*fourierCharacter j n)
          ((Real.sqrt (N : ℝ) : ℂ)⁻¹*fourierCharacter k n) = _
        rw [RCLike.inner_apply']
        simp [Complex.star_def, map_mul]
        <;> ring
      _ = 0 := by rw [h,mul_zero]

def fourierSynthesis (c : ZMod N → ℂ) : EuclideanSpace ℂ (ZMod N) :=
  ∑ j, c j • modeVector j

theorem fourierSynthesis_mass (c : ZMod N → ℂ) :
    ‖fourierSynthesis c‖^2 = ∑ j, ‖c j‖^2 := by
  have h := modeVector_orthonormal.inner_sum c c univ
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] at h
  have hr := congrArg Complex.re h
  simpa [fourierSynthesis, Complex.re_sum] using hr

@[simp] theorem fourierSynthesis_apply (c : ZMod N → ℂ) (n : ZMod N) :
    fourierSynthesis c n = ∑ j, c j*normalizedFourierMode j n := by
  simp [fourierSynthesis,modeVector]

/-- Finite evolution in the actual N-site position representation. -/
def siteEvolve (w : ZMod N → ℝ) (t : ℝ) (c : ZMod N → ℂ) : EuclideanSpace ℂ (ZMod N) :=
  fourierSynthesis (fun j => phase (-t*w j)*c j)

theorem siteEvolve_mass (w : ZMod N → ℝ) (t : ℝ) (c : ZMod N → ℂ) :
    ‖siteEvolve w t c‖^2 = ∑ j, ‖c j‖^2 := by
  rw [siteEvolve,fourierSynthesis_mass]
  simp only [norm_mul,phase_norm,one_mul]

/-- Synthesis transports the diagonal generator to the periodic nearest-neighbor
operator. This is an operator identity on every finite coefficient vector. -/
theorem fourierSynthesis_cyclic (c : ZMod N → ℂ) (n : ZMod N) :
    cyclicDifference (fun n => fourierSynthesis c n) n =
      fourierSynthesis (fun j => (2-ZMod.stdAddChar j-ZMod.stdAddChar (-j))*c j) n := by
  simp only [cyclicDifference,fourierSynthesis_apply,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := cyclic_character_eigenvalue j n
  unfold cyclicDifference at h
  unfold normalizedFourierMode
  linear_combination c j*(Real.sqrt (N : ℝ) : ℂ)⁻¹*h

/-- The physical scaling carries the derived dimensionless generator spectrum. -/
theorem fourierSynthesis_kinetic (r : Circle) (c : ZMod N → ℂ) (n : ZMod N) :
    cyclicKinetic r N (fun n => fourierSynthesis c n) n =
      ((r.hbar^2/(2*r.mass*(r.length/N)^2) : ℝ) : ℂ)*
        fourierSynthesis (fun j => (2-ZMod.stdAddChar j-ZMod.stdAddChar (-j))*c j) n := by
  rw [cyclicKinetic,fourierSynthesis_cyclic]

end
end OntologySeparation.ContinuumFinite
