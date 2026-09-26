import OntologySeparation.Experiments.ContinuumSiteTransport
import OntologySeparation.Experiments.ContinuumScale
import OntologySeparation.Experiments.ContinuumMenu
import OntologySeparation.Experiments.FiniteHamiltonian
import OntologySeparation.Experiments.ContinuumTransport
import OntologySeparation.Experiments.ContinuumWitness
import OntologySeparation.Experiments.FiniteFourier
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


example (x : ℝ) : 0 ≤ x^2/2-(1-Real.cos x) ∧ x^2/2-(1-Real.cos x) ≤ x^4/24 :=
  cosine_remainder_global x

example (r : OntologySeparation.ContinuumFinite.Circle) (a t : ℝ) (j : ℤ) :
    relativePhase (frequency r) (-j) j t = 0 :=
  (symmetric_mode_negative_control r a t j).1

example (u : SpectralHilbert) (hu : ‖u‖ = 1) (T epsilon : ℝ)
    (hT : 0 ≤ T) (he : 0 < epsilon) :=
  finite_resource_test_error witnessCircle u hu T epsilon hT he 100

-- The omitted orthogonal complement must be a failure outcome.
example (q : ℝ) (u : SpectralHilbert) :
    (∑ o, ‖(transportedInterferometer (twoModeEmbedding 0 1 (by norm_num)) q).operator o u‖^2) = ‖u‖^2 :=
  (transportedInterferometer _ q).complete u

-- The physical equation includes the small rings, without dropping a directed shift.
example (u : EuclideanSpace ℂ (ZMod 2)) (t : ℝ) :
    (Complex.I*(witnessCircle.hbar : ℂ)) • deriv (fun t => sitePropagator witnessCircle t u) t =
      cyclicHamiltonian witnessCircle (sitePropagator witnessCircle t u) :=
  sitePropagator_schrodinger witnessCircle u t

example (r : OntologySeparation.ContinuumFinite.Circle) (sc sa : ℝ) (hc : 0 < sc) (ha : 0 < sa) :
    ¬(sc*frequency r 1 = sa*ringLatticeFrequency r (r.length/5) 1 ∧
      sc*frequency r 2 = sa*ringLatticeFrequency r (r.length/5) 2) :=
  shared_scale_two_modes_impossible r 5 (by norm_num) sc sa hc ha

example (O : Fin 2 → Type) [∀ i, Fintype (O i)]
    (p q : ∀ i, OntologySeparation.FiniteDistribution (O i)) :
    tv (menuLaw O (fun _ => 0) p []) (menuLaw O (fun _ => 0) q []) = 0 := by
  simp [menuLaw,tv,l1]
