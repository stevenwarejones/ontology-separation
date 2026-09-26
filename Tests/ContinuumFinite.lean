import OntologySeparation.Experiments.ContinuumWitness
import OntologySeparation.Experiments.ContinuumLimit
import OntologySeparation.Experiments.FiniteDispersion
open OntologySeparation.ContinuumFinite

example (w : ℤ → ℝ) (t : ℝ) (c : SpectralVector) (h : mass c = 1) :
    mass (evolve w t c) = 1 := by rw [evolve_mass]; exact h

example (s : Finset ℤ) (c : SpectralVector) (hc : Supported s c)
    (w : ℤ → ℝ) (t : ℝ) : evolve w t c = evolve (spectralFinite s w) t c :=
  spectralFinite_exact s c hc w t

example (theta : ℝ) : plus 0 1 theta = plus 0 1 0 := by simp [plus]

example : plus 1 1 Real.pi < plus 1 1 0 :=
  strict_cosine_separation 1 1 Real.pi (by norm_num) (by norm_num) (by simp)

