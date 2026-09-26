import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-! Square-summable Fourier coefficients on the circle. Position-space Fourier
identification is external. No convergence or detector error claim is assumed. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section

/-- The full countably infinite spectral state space, not a finite cutoff. -/
structure SpectralVector where
  coefficient : ℤ → ℂ
  summable : Summable (fun j => ‖coefficient j‖ ^ 2)

@[ext] theorem SpectralVector.ext {u v : SpectralVector}
    (h : ∀ j, u.coefficient j = v.coefficient j) : u = v := by
  cases u with | mk u hu =>
    cases v with | mk v hv =>
      have : u = v := funext h
      subst v
      rfl

def mass (c : SpectralVector) : ℝ := ∑' j, ‖c.coefficient j‖ ^ 2

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Frequency is E/hbar; arbitrary real frequencies also give norm preservation. -/
def evolve (frequency : ℤ → ℝ) (t : ℝ) (c : SpectralVector) : SpectralVector where
  coefficient j := phase (-t * frequency j) * c.coefficient j
  summable := by simpa only [norm_mul, phase_norm, one_mul] using c.summable

@[simp] theorem evolve_mass (w : ℤ → ℝ) (t : ℝ) (c : SpectralVector) :
    mass (evolve w t c) = mass c := by
  simp only [mass, evolve, norm_mul, phase_norm, one_mul]

@[simp] theorem evolve_zero (w : ℤ → ℝ) (c : SpectralVector) : evolve w 0 c = c := by
  ext j
  simp [evolve]

theorem evolve_add (w : ℤ → ℝ) (s t : ℝ) (c : SpectralVector) :
    evolve w (s+t) c = evolve w s (evolve w t c) := by
  ext j
  change phase (-(s+t)*w j) * c.coefficient j =
    phase (-s*w j) * (phase (-t*w j)*c.coefficient j)
  rw [show -(s+t)*w j = -s*w j + -t*w j by ring, phase_add, mul_assoc]

@[simp] theorem evolve_inverse (w : ℤ → ℝ) (t : ℝ) (c : SpectralVector) :
    evolve w (-t) (evolve w t c) = c := by
  rw [← evolve_add]
  simp

/-- Every coefficient distance is preserved, hence so is the l² distance. -/
theorem evolve_distance (w : ℤ → ℝ) (t : ℝ) (u v : SpectralVector) :
    (∑' j, ‖(evolve w t u).coefficient j - (evolve w t v).coefficient j‖ ^ 2) =
    ∑' j, ‖u.coefficient j - v.coefficient j‖ ^ 2 := by
  apply tsum_congr
  intro j
  simp only [evolve, ← mul_sub, norm_mul, phase_norm, one_mul]

structure Circle where
  length : ℝ
  mass : ℝ
  hbar : ℝ
  length_pos : 0 < length
  mass_pos : 0 < mass
  hbar_pos : 0 < hbar

def waveNumber (r : Circle) (j : ℤ) : ℝ := 2 * Real.pi * j / r.length

def frequency (r : Circle) (j : ℤ) : ℝ := r.hbar * waveNumber r j ^ 2 / (2*r.mass)

/-- A finite accessible support, explicitly a condition on an infinite vector. -/
def Supported (s : Finset ℤ) (c : SpectralVector) : Prop :=
  ∀ j, j ∉ s → c.coefficient j = 0

theorem evolve_supported (s : Finset ℤ) (c : SpectralVector) (h : Supported s c)
    (w : ℤ → ℝ) (t : ℝ) : Supported s (evolve w t c) := by
  intro j hj
  simp [evolve, h j hj]

/-- Exact access-restricted equivalence, for any two agreeing spectra. -/
theorem finite_spectral_exact (s : Finset ℤ) (c : SpectralVector)
    (hc : Supported s c) (w v : ℤ → ℝ) (h : ∀ j ∈ s, w j = v j) (t : ℝ) :
    evolve w t c = evolve v t c := by
  ext j
  by_cases hj : j ∈ s
  · simp [evolve, h j hj]
  · simp [evolve, hc j hj]

/-- Complete normalized detector, encompassing any shared POVM on unit vectors.
No Lipschitz/trace-distance property is assumed by this exact-equality interface. -/
structure Detector (Outcome : Type) [Fintype Outcome] where
  probability : SpectralVector → Outcome → ℝ
  nonneg : ∀ c, mass c = 1 → ∀ o, 0 ≤ probability c o
  total : ∀ c, mass c = 1 → ∑ o, probability c o = 1

theorem complete_detector_exact {O : Type} [Fintype O] (d : Detector O)
    (s : Finset ℤ) (c : SpectralVector) (hc : Supported s c)
    (w v : ℤ → ℝ) (h : ∀ j ∈ s, w j = v j) (t : ℝ) (o : O) :
    d.probability (evolve w t c) o = d.probability (evolve v t c) o := by
  rw [finite_spectral_exact s c hc w v h t]

/-- An explicit finitely supported energy table extended by zero. -/
def spectralFinite (s : Finset ℤ) (w : ℤ → ℝ) (j : ℤ) : ℝ :=
  if j ∈ s then w j else 0

theorem spectralFinite_exact (s : Finset ℤ) (c : SpectralVector)
    (hc : Supported s c) (w : ℤ → ℝ) (t : ℝ) :
    evolve w t c = evolve (spectralFinite s w) t c := by
  apply finite_spectral_exact s c hc
  intro j hj
  simp [spectralFinite, hj]

end
end OntologySeparation.ContinuumFinite
