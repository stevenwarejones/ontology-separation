import OntologySeparation.Experiments.FiniteFourier
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The periodic finite-difference Hamiltonian and its unique real-time
Schrödinger propagator, constructed from the complete finite Fourier basis. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset
variable {N : ℕ} [NeZero N]

/-- Orthogonality and matching dimension supply spanning, not just normalized columns. -/
def fourierBasis : OrthonormalBasis (ZMod N) ℂ (EuclideanSpace ℂ (ZMod N)) :=
  (basisOfOrthonormalOfCardEqFinrank (modeVector_orthonormal (N := N)) (by simp)).toOrthonormalBasis
    (by simpa using (modeVector_orthonormal (N := N)))

@[simp] theorem fourierBasis_apply (j : ZMod N) : fourierBasis j = modeVector j := by
  simp [fourierBasis]

def fourierAnalysis (u : EuclideanSpace ℂ (ZMod N)) : ZMod N → ℂ :=
  fun j => (fourierBasis.repr u) j

theorem fourier_inversion (u : EuclideanSpace ℂ (ZMod N)) :
    fourierSynthesis (fourierAnalysis u) = u := by
  simpa [fourierSynthesis, fourierAnalysis] using fourierBasis.sum_repr u

theorem fourierSynthesis_eq_repr (c : ZMod N → ℂ) :
    fourierSynthesis c = fourierBasis.repr.symm (WithLp.toLp 2 c) := by
  simpa [fourierSynthesis] using fourierBasis.sum_repr_symm (WithLp.toLp 2 c)

@[simp] theorem fourierAnalysis_synthesis (c : ZMod N → ℂ) :
    fourierAnalysis (fourierSynthesis c) = c := by
  ext j
  simp [fourierAnalysis, fourierSynthesis_eq_repr]

/-- The physical frequency on every finite Fourier label, including N=1 and N=2. -/
def siteFrequency (r : Circle) (j : ZMod N) : ℝ :=
  ringLatticeFrequency r (r.length/N) (j.val : ℤ)

/-- The two directed shifts are retained, including when they coincide at N=2. -/
def cyclicHamiltonian (r : Circle) : EuclideanSpace ℂ (ZMod N) →L[ℂ] EuclideanSpace ℂ (ZMod N) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun u => WithLp.toLp 2 (cyclicKinetic r N u)
    map_add' := by
      intro u v; ext n
      change cyclicKinetic r N (u+v) n = cyclicKinetic r N u n+cyclicKinetic r N v n
      simp only [cyclicKinetic, cyclicDifference, Pi.add_apply, PiLp.add_apply]
      ring
    map_smul' := by
      intro c u; ext n
      change cyclicKinetic r N (c • u) n = c*cyclicKinetic r N u n
      simp only [cyclicKinetic, cyclicDifference, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
      ring }

@[simp] theorem cyclicHamiltonian_apply (r : Circle) (u : EuclideanSpace ℂ (ZMod N))
    (n : ZMod N) : cyclicHamiltonian r u n = cyclicKinetic r N u n := rfl

theorem cyclicHamiltonian_mode (r : Circle) (j : ZMod N) :
    cyclicHamiltonian r (modeVector j) = ((r.hbar*siteFrequency r j : ℝ) : ℂ) • modeVector j := by
  ext n
  have h := cyclicKinetic_spectrum r N (j.val : ℤ) n
  have hj : ((j.val : ℤ) : ZMod N) = j := by simp
  rw [hj] at h
  change cyclicKinetic r N (normalizedFourierMode j) n =
    ((r.hbar*siteFrequency r j : ℝ) : ℂ)*normalizedFourierMode j n
  dsimp [cyclicKinetic, cyclicDifference] at h ⊢
  dsimp [normalizedFourierMode, siteFrequency, ringLatticeFrequency]
  linear_combination (Real.sqrt (N : ℝ) : ℂ)⁻¹*h

theorem cyclicHamiltonian_synthesis (r : Circle) (c : ZMod N → ℂ) :
    cyclicHamiltonian r (fourierSynthesis c) =
      fourierSynthesis (fun j => ((r.hbar*siteFrequency r j : ℝ) : ℂ)*c j) := by
  simp only [fourierSynthesis, map_sum, map_smul, cyclicHamiltonian_mode]
  apply sum_congr rfl
  intro j _
  simp only [smul_smul]
  congr 1
  ring

/-- The real-time derivative of the phase, with the negative Schrödinger sign. -/
theorem phase_time_derivative (w t : ℝ) :
    HasDerivAt (fun t : ℝ => phase (-t*w)) ((-Complex.I*(w : ℂ))*phase (-t*w)) t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (-Complex.I*(w : ℂ))).cexp
  convert h using 1 <;> simp [phase, Complex.ofReal_mul, Complex.ofReal_neg] <;> congr 1 <;> ring

/-- Finite synthesis permits termwise vector-valued differentiation. -/
theorem siteEvolve_derivative (w : ZMod N → ℝ) (c : ZMod N → ℂ) (t : ℝ) :
    HasDerivAt (fun t => siteEvolve w t c)
      (fourierSynthesis (fun j => (-Complex.I*(w j : ℂ))*(phase (-t*w j)*c j))) t := by
  have h := HasDerivAt.sum (u := (univ : Finset (ZMod N)))
    (fun j _ => ((phase_time_derivative (w j) t).mul_const (c j)).smul_const (modeVector j))
  convert h using 1
  · rfl
  · unfold fourierSynthesis
    apply sum_congr rfl
    intro j _
    rw [mul_assoc]

/-- Real-time vector field of the physical Schrödinger equation. -/
def schrodingerGenerator (r : Circle) :
    EuclideanSpace ℂ (ZMod N) →L[ℂ] EuclideanSpace ℂ (ZMod N) :=
  (-Complex.I/(r.hbar : ℂ)) • cyclicHamiltonian r

theorem schrodingerGenerator_synthesis (r : Circle) (c : ZMod N → ℂ) :
    schrodingerGenerator r (fourierSynthesis c) =
      fourierSynthesis (fun j => (-Complex.I*(siteFrequency r j : ℂ))*c j) := by
  have hh : (r.hbar : ℂ) ≠ 0 := by exact_mod_cast r.hbar_pos.ne'
  simp only [schrodingerGenerator, ContinuousLinearMap.smul_apply, cyclicHamiltonian_synthesis,
    fourierSynthesis, smul_sum, smul_smul]
  apply sum_congr rfl
  intro j _
  congr 1
  push_cast
  field_simp
  <;> ring

/-- Propagator for arbitrary initial site data, through verified Fourier inversion. -/
def sitePropagator (r : Circle) (t : ℝ) (u : EuclideanSpace ℂ (ZMod N)) :
    EuclideanSpace ℂ (ZMod N) := siteEvolve (siteFrequency r) t (fourierAnalysis u)

@[simp] theorem sitePropagator_zero (r : Circle) (u : EuclideanSpace ℂ (ZMod N)) :
    sitePropagator r 0 u = u := by
  simpa [sitePropagator, siteEvolve] using fourier_inversion u

theorem sitePropagator_derivative (r : Circle) (u : EuclideanSpace ℂ (ZMod N)) (t : ℝ) :
    HasDerivAt (fun t => sitePropagator r t u)
      (schrodingerGenerator r (sitePropagator r t u)) t := by
  simpa only [sitePropagator, siteEvolve, schrodingerGenerator_synthesis] using
    siteEvolve_derivative (siteFrequency r) (fourierAnalysis u) t

/-- The physical equation i*hbar*psi' = H psi, not an assumed ODE predicate. -/
theorem sitePropagator_schrodinger (r : Circle) (u : EuclideanSpace ℂ (ZMod N)) (t : ℝ) :
    (Complex.I*(r.hbar : ℂ)) • deriv (fun t => sitePropagator r t u) t =
      cyclicHamiltonian r (sitePropagator r t u) := by
  rw [(sitePropagator_derivative r u t).deriv]
  simp only [schrodingerGenerator, ContinuousLinearMap.smul_apply, smul_smul]
  have hh : (r.hbar : ℂ) ≠ 0 := by exact_mod_cast r.hbar_pos.ne'
  have hc : Complex.I*(r.hbar : ℂ)*(-Complex.I/(r.hbar : ℂ)) = 1 := by
    field_simp
    simp [Complex.I_sq]
  rw [hc, one_smul]

/-- Uniqueness identifies this Fourier construction as the finite Hamiltonian
propagator. No regularity claim is made about an unbounded infinite generator. -/
theorem sitePropagator_unique (r : Circle) (u : EuclideanSpace ℂ (ZMod N))
    (f : ℝ → EuclideanSpace ℂ (ZMod N)) (h0 : f 0 = u)
    (hf : ∀ t, HasDerivAt f (schrodingerGenerator r (f t)) t) :
    f = fun t => sitePropagator r t u := by
  apply ODE_solution_unique_univ (v := fun _ => schrodingerGenerator r)
    (s := fun _ => Set.univ) (t₀ := 0)
    (fun _ => (schrodingerGenerator r).lipschitz.lipschitzOnWith)
    (fun t => ⟨hf t, Set.mem_univ _⟩)
    (fun t => ⟨sitePropagator_derivative r u t, Set.mem_univ _⟩)
  simpa using h0

theorem sitePropagator_synthesis (r : Circle) (c : ZMod N → ℂ) (t : ℝ) :
    sitePropagator r t (fourierSynthesis c) = siteEvolve (siteFrequency r) t c := by
  simp [sitePropagator]

end
end OntologySeparation.ContinuumFinite
