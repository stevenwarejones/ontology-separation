import OntologySeparation.Experiments.ContinuumWitness
import OntologySeparation.Experiments.FiniteFourier
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Isometric two-mode preparations and complete readouts. The orthogonal
complement is a genuine failure outcome on the entire ambient Hilbert space. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset

section Pair
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def pairIsometry (e : Fin 2 → H) (he : Orthonormal ℂ e) : TwoMode →ₗᵢ[ℂ] H where
  toFun u := ∑ i, u i • e i
  map_add' u v := by simp [add_smul, sum_add_distrib]
  map_smul' c u := by simp [mul_smul, smul_sum]
  norm_map' u := by
    change ‖∑ i, u i • e i‖ = ‖u‖
    have h := he.inner_sum (fun i => u i) (fun i => u i) univ
    rw [inner_self_eq_norm_sq_to_K] at h
    simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq] at h
    have hr := congrArg Complex.re h
    have hs : ‖∑ i, u i • e i‖^2 = ‖u‖^2 := by
      simpa [EuclideanSpace.norm_sq_eq, Complex.re_sum, ← Complex.ofReal_pow] using hr
    nlinarith [norm_nonneg u, norm_nonneg (∑ i, u i • e i)]

@[simp] theorem pairIsometry_single (e : Fin 2 → H) (he : Orthonormal ℂ e) (i : Fin 2) :
    pairIsometry e he (EuclideanSpace.single i 1) = e i := by
  fin_cases i <;> simp [pairIsometry, PiLp.single_apply]
end Pair

def spectralPair (j₀ j₁ : ℤ) (i : Fin 2) : SpectralHilbert :=
  lp.single 2 (if i = 0 then j₀ else j₁) 1

theorem spectralPair_orthonormal (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) :
    Orthonormal ℂ (spectralPair j₀ j₁) := by
  rw [orthonormal_iff_ite]
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp [spectralPair, lp.inner_single_left, lp.single_apply, h, h.symm]

/-- Duplicate labels are excluded explicitly. -/
def twoModeEmbedding (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) : TwoMode →ₗᵢ[ℂ] SpectralHilbert :=
  pairIsometry (spectralPair j₀ j₁) (spectralPair_orthonormal j₀ j₁ h)

@[simp] theorem twoModeEmbedding_apply (j₀ j₁ : ℤ) (h : j₀ ≠ j₁)
    (u : TwoMode) (j : ℤ) :
    twoModeEmbedding j₀ j₁ h u j =
      (if j = j₀ then u 0 else 0) + (if j = j₁ then u 1 else 0) := by
  change (∑ i : Fin 2, u i • spectralPair j₀ j₁ i) j = _
  rw [Fin.sum_univ_two]
  change u 0 * (lp.single 2 j₀ (1 : ℂ) : SpectralHilbert) j + u 1 * (lp.single 2 j₁ (1 : ℂ) : SpectralHilbert) j = _
  by_cases h0 : j = j₀ <;> by_cases h1 : j = j₁ <;>
    simp [lp.single_apply, h0, h1, eq_comm]

@[simp] theorem twoModeEmbedding_norm (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) (u : TwoMode) :
    ‖twoModeEmbedding j₀ j₁ h u‖ = ‖u‖ := (twoModeEmbedding j₀ j₁ h).norm_map u

theorem twoModeEmbedding_inner (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) (u v : TwoMode) :
    inner ℂ (twoModeEmbedding j₀ j₁ h u) (twoModeEmbedding j₀ j₁ h v) = inner ℂ u v :=
  (twoModeEmbedding j₀ j₁ h).inner_map_map u v

theorem twoModeEmbedding_injective (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) :
    Function.Injective (twoModeEmbedding j₀ j₁ h) := (twoModeEmbedding j₀ j₁ h).injective

theorem twoModeEmbedding_support (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) (u : TwoMode)
    (j : ℤ) (hj : j ∉ ({j₀,j₁} : Finset ℤ)) : twoModeEmbedding j₀ j₁ h u j = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  simp [hj.1, hj.2]

/-- Actual infinite spectral dynamics intertwine with the existing two-mode map. -/
theorem twoModeEmbedding_intertwines (j₀ j₁ : ℤ) (h : j₀ ≠ j₁)
    (w : ℤ → ℝ) (t : ℝ) (u : TwoMode) :
    hilbertEvolve w t (twoModeEmbedding j₀ j₁ h u) =
      twoModeEmbedding j₀ j₁ h (twoModeEvolve (w j₀) (w j₁) t u) := by
  ext j
  by_cases h0 : j = j₀
  · subst j; simp [h, h.symm, twoModeEvolve]
  · by_cases h1 : j = j₁
    · subst j; simp [h, h.symm, twoModeEvolve]
    · simp [h0, h1]

section Transport
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded extraction is the adjoint of the declared preparation. -/
def pairExtraction (e : TwoMode →ₗᵢ[ℂ] H) : H →L[ℂ] TwoMode :=
  e.toContinuousLinearMap.adjoint

@[simp] theorem pairExtraction_embedding (e : TwoMode →ₗᵢ[ℂ] H) (u : TwoMode) :
    pairExtraction e (e u) = u := by
  exact DFunLike.congr_fun e.adjoint_comp_self u

def pairProjection (e : TwoMode →ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  e.toContinuousLinearMap.comp (pairExtraction e)

@[simp] theorem pairProjection_idempotent (e : TwoMode →ₗᵢ[ℂ] H) (x : H) :
    pairProjection e (pairProjection e x) = pairProjection e x := by
  simp [pairProjection]

theorem pairProjection_orthogonal (e : TwoMode →ₗᵢ[ℂ] H) (u : TwoMode) (x : H) :
    inner ℂ (e u) (x-pairProjection e x) = 0 := by
  rw [inner_sub_right]
  change inner ℂ (e u) x-inner ℂ (e u) (e (pairExtraction e x)) = 0
  rw [e.inner_map_map]
  apply sub_eq_zero.mpr
  exact (e.toContinuousLinearMap.adjoint_inner_right u x).symm

theorem pairProjection_pythagoras (e : TwoMode →ₗᵢ[ℂ] H) (x : H) :
    ‖pairExtraction e x‖^2 + ‖x-pairProjection e x‖^2 = ‖x‖^2 := by
  have hi := e.toContinuousLinearMap.adjoint_inner_left (pairExtraction e x) x
  change inner ℂ (pairExtraction e x) (pairExtraction e x) =
    inner ℂ x (e (pairExtraction e x)) at hi
  have hr : RCLike.re (inner ℂ x (pairProjection e x)) = ‖pairExtraction e x‖^2 := by
    change RCLike.re (inner ℂ x (e (pairExtraction e x))) = _
    rw [← hi]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (pairExtraction e x)
  rw [norm_sub_sq (𝕜 := ℂ), hr]
  change ‖pairExtraction e x‖^2 +
    (‖x‖^2-2*‖pairExtraction e x‖^2+‖e (pairExtraction e x)‖^2) = _
  rw [e.norm_map]
  ring

/-- The two click operators are transported recombiners. Failure projects onto
all inaccessible modes, so the instrument is complete for every ambient state. -/
def transportedInterferometer (e : TwoMode →ₗᵢ[ℂ] H) (q : ℝ) : BornInstrument H (Fin 3) where
  operator o := if o = 2 then ContinuousLinearMap.id ℂ H-pairProjection e else
    e.toContinuousLinearMap.comp ((interferometerOperator q o).comp (pairExtraction e))
  complete x := by
    have ht := (interferometer q).complete (pairExtraction e x)
    change (∑ o, ‖interferometerOperator q o (pairExtraction e x)‖^2) = _ at ht
    rw [Fin.sum_univ_three, interferometer_failure] at ht
    simp only [Fin.sum_univ_three]
    norm_num [Fin.ext_iff, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, e.norm_map]
    have hp := pairProjection_pythagoras e x
    linarith

theorem transportedInterferometer_agrees (e : TwoMode →ₗᵢ[ℂ] H) (q : ℝ)
    (u : TwoMode) (hu : ‖u‖ = 1) (o : Fin 3) :
    ((transportedInterferometer e q).distribution (e u) (by simpa using hu)).mass o =
      ((interferometer q).distribution u hu).mass o := by
  change ‖(transportedInterferometer e q).operator o (e u)‖^2 =
    ‖interferometerOperator q o u‖^2
  fin_cases o <;>
    simp [transportedInterferometer, pairProjection, e.norm_map, interferometer_failure]
end Transport

/-- Stochastic loss/bin randomization retaining pre-existing failure mass. -/
def noisyPostprocess (eta v : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (p : FiniteDistribution (Fin 3)) :
    FiniteDistribution (Fin 3) where
  mass o := if o = 0 then eta*((1+v)/2*p.mass 0+(1-v)/2*p.mass 1)
    else if o = 1 then eta*((1-v)/2*p.mass 0+(1+v)/2*p.mass 1)
    else p.mass 2+(1-eta)*(p.mass 0+p.mass 1)
  nonneg o := by
    have h0 := p.nonneg 0; have h1 := p.nonneg 1; have h2 := p.nonneg 2
    have hv : 0 ≤ 1-v := sub_nonneg.mpr hv1
    have he : 0 ≤ 1-eta := sub_nonneg.mpr he1
    fin_cases o <;> norm_num <;> positivity
  total := by
    have ht := p.total
    rw [Fin.sum_univ_three] at ht
    rw [Fin.sum_univ_three]
    change eta*((1+v)/2*p.mass 0+(1-v)/2*p.mass 1) +
      eta*((1-v)/2*p.mass 0+(1+v)/2*p.mass 1) +
      (p.mass 2+(1-eta)*(p.mass 0+p.mass 1)) = 1
    linear_combination ht

theorem noisyPostprocess_interferometer (eta v q : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (u : TwoMode) (hu : ‖u‖ = 1) (o : Fin 3) :
    (noisyPostprocess eta v he0 he1 hv0 hv1 ((interferometer q).distribution u hu)).mass o =
      (noisyReadout eta v q he0 he1 hv0 hv1 u hu).mass o := by
  have ht := (interferometer q).complete u
  change (∑ o, ‖interferometerOperator q o u‖^2) = _ at ht
  rw [Fin.sum_univ_three, interferometer_failure, hu] at ht
  have hs : ‖interferometerOperator q 0 u‖^2+‖interferometerOperator q 1 u‖^2 = 1 := by linarith
  fin_cases o <;> simp [noisyPostprocess, noisyReadout, BornInstrument.distribution,
    interferometer, interferometer_failure, hs]

/-- Complete operational law after the actual infinite-space evolution. -/
def spectralReadout (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) (w : ℤ → ℝ)
    (t eta v q : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (u : TwoMode) (hu : ‖u‖ = 1) : FiniteDistribution (Fin 3) :=
  noisyPostprocess eta v he0 he1 hv0 hv1
    ((transportedInterferometer (twoModeEmbedding j₀ j₁ h) q).distribution
      (hilbertEvolve w t (twoModeEmbedding j₀ j₁ h u)) (by simp [hu]))

theorem spectralReadout_agrees (j₀ j₁ : ℤ) (h : j₀ ≠ j₁) (w : ℤ → ℝ)
    (t eta v q : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (u : TwoMode) (hu : ‖u‖ = 1) (o : Fin 3) :
    (spectralReadout j₀ j₁ h w t eta v q he0 he1 hv0 hv1 u hu).mass o =
      (noisyReadout eta v q he0 he1 hv0 hv1 (twoModeEvolve (w j₀) (w j₁) t u)
        (by simp [hu])).mass o := by
  unfold spectralReadout
  simp_rw [twoModeEmbedding_intertwines]
  have hm (k : Fin 3) := transportedInterferometer_agrees (twoModeEmbedding j₀ j₁ h) q
    (twoModeEvolve (w j₀) (w j₁) t u) (by simp [hu]) k
  calc
    _ = (noisyPostprocess eta v he0 he1 hv0 hv1
      ((interferometer q).distribution (twoModeEvolve (w j₀) (w j₁) t u) (by simp [hu]))).mass o := by
        simp only [noisyPostprocess, hm]
    _ = _ := noisyPostprocess_interferometer eta v q he0 he1 hv0 hv1 _ _ o

/-- The N=4 witness starts with the same normalized vector in infinite l²,
uses each declared evolution, and measures both through the complete instrument. -/
theorem spectral_noisy_witness (eta v : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let t := Real.pi/witnessGap
    let p := spectralReadout 0 1 (by norm_num) (frequency witnessCircle) t eta v (t/2)
      he0 he1 hv0 hv1 (twoModeState 0) (twoModeState_normalized 0)
    let q := spectralReadout 0 1 (by norm_num)
      (ringLatticeFrequency witnessCircle (witnessCircle.length/4)) t eta v (t/2)
      he0 he1 hv0 hv1 (twoModeState 0) (twoModeState_normalized 0)
    p.mass 0 = eta*(1+v)/2 ∧ p.mass 1 = eta*(1-v)/2 ∧ p.mass 2 = 1-eta ∧
    q.mass 0 = eta*(1-v)/2 ∧ q.mass 1 = eta*(1+v)/2 ∧ q.mass 2 = 1-eta ∧ tv p q = eta*v := by
  dsimp only
  have ht := lattice_noisy_witness eta v he0 he1 hv0 hv1
  dsimp only at ht
  have hp : (spectralReadout 0 1 (by norm_num) (frequency witnessCircle) (Real.pi/witnessGap)
      eta v (Real.pi/witnessGap/2) he0 he1 hv0 hv1 (twoModeState 0) (twoModeState_normalized 0)).mass 0 =
      eta*(1+v)/2 := by rw [spectralReadout_agrees]; exact ht.1
  have htable :
      let p := spectralReadout 0 1 (by norm_num) (frequency witnessCircle) (Real.pi/witnessGap)
        eta v (Real.pi/witnessGap/2) he0 he1 hv0 hv1 (twoModeState 0) (twoModeState_normalized 0)
      let q := spectralReadout 0 1 (by norm_num)
        (ringLatticeFrequency witnessCircle (witnessCircle.length/4)) (Real.pi/witnessGap)
        eta v (Real.pi/witnessGap/2) he0 he1 hv0 hv1 (twoModeState 0) (twoModeState_normalized 0)
      (p.mass 0 = eta*(1+v)/2 ∧ p.mass 1 = eta*(1-v)/2 ∧ p.mass 2 = 1-eta) ∧
      (q.mass 0 = eta*(1-v)/2 ∧ q.mass 1 = eta*(1+v)/2 ∧ q.mass 2 = 1-eta) := by
    dsimp only
    simp_rw [spectralReadout_agrees]
    exact ⟨⟨ht.1, ht.2.1, ht.2.2.1⟩, ht.2.2.2⟩
  exact ⟨htable.1.1, htable.1.2.1, htable.1.2.2, htable.2.1,
    htable.2.2.1, htable.2.2.2, (noisy_witness_tv _ _ eta v he0 hv0 htable.1 htable.2).2.2.2⟩

end
end OntologySeparation.ContinuumFinite
