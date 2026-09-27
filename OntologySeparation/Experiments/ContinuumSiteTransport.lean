import OntologySeparation.Experiments.ContinuumTransport
import OntologySeparation.Experiments.FiniteHamiltonian

/-! The common spectral cutoff and the two-mode operational readout are
transported to the unique propagator on actual cyclic site states. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset
variable {N : ℕ} [NeZero N]

theorem siteFrequency_intCast (r : Circle) (j : ℤ) :
    siteFrequency r (j : ZMod N) = ringLatticeFrequency r (r.length/N) j := by
  have h := cyclicKinetic_spectrum r N j (0 : ZMod N)
  have hv := cyclicKinetic_spectrum r N (((j : ZMod N).val : ℕ) : ℤ) (0 : ZMod N)
  have hj : ((((j : ZMod N).val : ℕ) : ℤ) : ZMod N) = (j : ZMod N) := by simp
  rw [hj] at hv
  have he : ((r.hbar*siteFrequency r (j : ZMod N) : ℝ) : ℂ) =
      ((r.hbar*ringLatticeFrequency r (r.length/N) j : ℝ) : ℂ) := by
    have hc := hv.symm.trans h
    simpa [siteFrequency,ringLatticeFrequency,fourierCharacter] using hc
  exact mul_left_cancel₀ r.hbar_pos.ne' (Complex.ofReal_injective he)

/-- The constructed propagator is complex-linear for each fixed time. -/
def sitePropagatorCLM (r : Circle) (t : ℝ) :
    EuclideanSpace ℂ (ZMod N) →L[ℂ] EuclideanSpace ℂ (ZMod N) :=
  LinearMap.toContinuousLinearMap {
    toFun := sitePropagator r t
    map_add' := by
      intro u v
      simp [sitePropagator,siteEvolve,fourierSynthesis,fourierAnalysis,
        mul_add,add_smul,Finset.sum_add_distrib]
    map_smul' := by
      intro c u
      simp [sitePropagator,siteEvolve,fourierSynthesis,fourierAnalysis,
        mul_smul,smul_sum,mul_comm,mul_left_comm,mul_assoc] }

@[simp] theorem sitePropagatorCLM_apply (r : Circle) (t : ℝ)
    (u : EuclideanSpace ℂ (ZMod N)) : sitePropagatorCLM r t u = sitePropagator r t u := rfl

theorem fourierAnalysis_mode (j k : ZMod N) :
    fourierAnalysis (modeVector j) k = if k = j then 1 else 0 := by
  have h := congrArg (fun x : EuclideanSpace ℂ (ZMod N) => x k) (fourierBasis.repr_self j)
  simpa [fourierAnalysis,PiLp.single_apply,eq_comm] using h

theorem sitePropagator_mode (r : Circle) (t : ℝ) (j : ZMod N) :
    sitePropagator r t (modeVector j) = phase (-t*siteFrequency r j) • modeVector j := by
  simp [sitePropagator,siteEvolve,fourierSynthesis,fourierAnalysis_mode]

/-- The lattice approximation in l² maps to the unique site Schrödinger solution.
This strengthens the earlier unfolded phase formula to a propagator identity. -/
theorem sitePropagator_bandSynthesis (r : Circle) (t : ℝ) (s : Finset ℤ) (u : SpectralHilbert) :
    sitePropagator r t (bandSynthesis (N := N) s u) =
      bandSynthesis (N := N) s (hilbertEvolve (ringLatticeFrequency r (r.length/N)) t u) := by
  change sitePropagatorCLM r t (∑ j : s, u j • modeVector (j.val : ZMod N)) = _
  simp only [map_sum,map_smul,sitePropagatorCLM_apply,sitePropagator_mode,
    siteFrequency_intCast,bandSynthesis,hilbertEvolve_apply,smul_smul]
  apply sum_congr rfl
  intro j _
  congr 1
  ring

/-- The same distinct accessible modes form an isometric site preparation. -/
def sitePairEmbedding (j₀ j₁ : ℤ) (h : (j₀ : ZMod N) ≠ (j₁ : ZMod N)) :
    TwoMode →ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod N) :=
  pairIsometry (fun i : Fin 2 => modeVector (if i = 0 then (j₀ : ZMod N) else (j₁ : ZMod N)))
    (by
      apply modeVector_orthonormal.comp
      intro i k hik
      fin_cases i <;> fin_cases k <;> simp_all)

theorem sitePairEmbedding_no_alias (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) (J : ℕ)
    (h0 : j₀.natAbs ≤ J) (h1 : j₁.natAbs ≤ J) (hN : 2*J < N) :
    (j₀ : ZMod N) ≠ (j₁ : ZMod N) := fun he => h (no_alias J hN j₀ j₁ h0 h1 he)

theorem sitePairEmbedding_band (j₀ j₁ : ℤ) (h : j₀ ≠ j₁)
    (ha : (j₀ : ZMod N) ≠ (j₁ : ZMod N)) (u : TwoMode) :
    bandSynthesis (N := N) {j₀,j₁} (twoModeEmbedding j₀ j₁ h u) = sitePairEmbedding j₀ j₁ ha u := by
  calc
    _ = ∑ j ∈ ({j₀,j₁} : Finset ℤ), twoModeEmbedding j₀ j₁ h u j • modeVector (j : ZMod N) :=
      Finset.sum_coe_sort _ _
    _ = _ := by simp [sitePairEmbedding,pairIsometry,Fin.sum_univ_two,h,h.symm]

theorem sitePairEmbedding_intertwines (r : Circle) (t : ℝ) (j₀ j₁ : ℤ)
    (h : j₀ ≠ j₁) (ha : (j₀ : ZMod N) ≠ (j₁ : ZMod N)) (u : TwoMode) :
    sitePropagator r t (sitePairEmbedding j₀ j₁ ha u) = sitePairEmbedding j₀ j₁ ha
      (twoModeEvolve (ringLatticeFrequency r (r.length/N) j₀)
        (ringLatticeFrequency r (r.length/N) j₁) t u) := by
  rw [← sitePairEmbedding_band j₀ j₁ h ha u,sitePropagator_bandSynthesis,
    twoModeEmbedding_intertwines,sitePairEmbedding_band]

/-- Transported site measurement implements exactly the declared operational
readout on accessible modes; its complement is still a complete failure outcome. -/
theorem site_readout_agrees (j₀ j₁ : ℤ) (ha : (j₀ : ZMod N) ≠ (j₁ : ZMod N))
    (q : ℝ) (u : TwoMode) (hu : ‖u‖ = 1) (o : Fin 3) :
    ((transportedInterferometer (sitePairEmbedding j₀ j₁ ha) q).distribution
      (sitePairEmbedding j₀ j₁ ha u) (by simpa using hu)).mass o =
      ((interferometer q).distribution u hu).mass o :=
  transportedInterferometer_agrees _ q u hu o

/-- Full noisy operational law after evolution by the actual site Hamiltonian. -/
theorem site_noisy_readout (r : Circle) (t : ℝ) (j₀ j₁ : ℤ) (h : j₀ ≠ j₁)
    (ha : (j₀ : ZMod N) ≠ (j₁ : ZMod N)) (eta v q : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (u : TwoMode) (hu : ‖u‖ = 1) (o : Fin 3) :
    let e := sitePairEmbedding j₀ j₁ ha
    let z := sitePropagator r t (e u)
    (noisyPostprocess eta v he0 he1 hv0 hv1
      ((transportedInterferometer e q).distribution z (by
        dsimp [z,e]
        rw [sitePairEmbedding_intertwines r t j₀ j₁ h ha]
        simp [hu]))).mass o =
    (noisyReadout eta v q he0 he1 hv0 hv1
      (twoModeEvolve (ringLatticeFrequency r (r.length/N) j₀)
        (ringLatticeFrequency r (r.length/N) j₁) t u) (by simp [hu])).mass o := by
  dsimp only
  simp_rw [sitePairEmbedding_intertwines r t j₀ j₁ h ha]
  exact transportedNoisyReadout_agrees _ eta v q he0 he1 hv0 hv1 _ _ o

end
end OntologySeparation.ContinuumFinite
