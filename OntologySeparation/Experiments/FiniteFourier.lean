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
  simpa [fourierSynthesis, Complex.re_sum, ← Complex.ofReal_pow] using hr

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

/-- The integer cutoff used in strong convergence has a faithful N-site image. -/
theorem band_modes_orthonormal (s : Finset ℤ) (J : ℕ) (hN : 2*J < N)
    (hs : ∀ j ∈ s, j.natAbs ≤ J) :
    Orthonormal ℂ (fun j : s => modeVector (j.val : ZMod N)) := by
  apply modeVector_orthonormal.comp (fun j : s => (j.val : ZMod N))
  intro j k h
  apply Subtype.ext
  exact no_alias J hN j.val k.val (hs j.val j.property) (hs k.val k.property) h

def bandSynthesis (s : Finset ℤ) (u : SpectralHilbert) : EuclideanSpace ℂ (ZMod N) :=
  ∑ j : s, u j • modeVector (j.val : ZMod N)

theorem bandSynthesis_mass (s : Finset ℤ) (J : ℕ) (hN : 2*J < N)
    (hs : ∀ j ∈ s, j.natAbs ≤ J) (u : SpectralHilbert) :
    ‖bandSynthesis (N := N) s u‖^2 = ∑ j : s, ‖u j‖^2 := by
  have h := (band_modes_orthonormal s J hN hs).inner_sum
    (fun j : s => u j) (fun j : s => u j) univ
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] at h
  have hr := congrArg Complex.re h
  simpa [bandSynthesis, Complex.re_sum, ← Complex.ofReal_pow] using hr

/-- Applying the finite kinetic Hamiltonian to the embedded cutoff is exactly
multiplication by the same lattice energies used in the approximation theorem. -/
theorem bandSynthesis_kinetic (r : Circle) (s : Finset ℤ) (u : SpectralHilbert)
    (n : ZMod N) :
    cyclicKinetic r N (fun n => bandSynthesis (N := N) s u n) n =
      ∑ j : s, u j * ((r.hbar*ringLatticeFrequency r (r.length/N) j : ℝ) : ℂ) *
        normalizedFourierMode (j.val : ZMod N) n := by
  have heig (j : s) := cyclicKinetic_spectrum r N j.val n
  have happly (m : ZMod N) : bandSynthesis (N := N) s u m =
      ∑ j : s, u j * normalizedFourierMode (j.val : ZMod N) m := by
    simp [bandSynthesis,modeVector]
  simp only [cyclicKinetic,cyclicDifference,happly,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := heig j
  dsimp [cyclicKinetic,cyclicDifference] at h
  dsimp [normalizedFourierMode,ringLatticeFrequency]
  linear_combination u j*(Real.sqrt (N : ℝ) : ℂ)⁻¹*h

/-- The approximating evolution in the common Hilbert space is mapped to the
actual site wavefunction, with the derived kinetic phases on every retained mode. -/
theorem bandSynthesis_evolve (r : Circle) (s : Finset ℤ) (u : SpectralHilbert)
    (t : ℝ) (n : ZMod N) :
    bandSynthesis (N := N) s
      (hilbertEvolve (ringLatticeFrequency r (r.length/N)) t u) n =
      ∑ j : s, (phase (-t*ringLatticeFrequency r (r.length/N) j)*u j)*
        normalizedFourierMode (j.val : ZMod N) n := by
  simp [bandSynthesis,modeVector]

end
end OntologySeparation.ContinuumFinite
