import OntologySeparation.Experiments.ContinuumTruncation
import OntologySeparation.Experiments.FiniteDispersion

/-! The finite-band and tail estimates are composed in one common Hilbert space.
The global 1/24 dispersion coefficient is proved independently of the
older local 5/96 estimate. The normalized tail estimate is conservative. All measurements below are complete Born instruments. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset Filter
open scoped Topology

def fromHilbert (u : SpectralHilbert) : SpectralVector where
  coefficient := u
  summable := by simpa using (u.property.summable (by norm_num : 0 < (2 : ENNReal).toReal))

def hilbertEvolve (w : ℤ → ℝ) (t : ℝ) (u : SpectralHilbert) : SpectralHilbert :=
  (evolve w t (fromHilbert u)).toHilbert

@[simp] theorem hilbertEvolve_apply (w : ℤ → ℝ) (t : ℝ) (u : SpectralHilbert) (j : ℤ) :
    hilbertEvolve w t u j = phase (-t*w j)*u j := rfl

@[simp] theorem hilbertEvolve_norm (w : ℤ → ℝ) (t : ℝ) (u : SpectralHilbert) :
    ‖hilbertEvolve w t u‖ = ‖u‖ := by
  have hs : ‖hilbertEvolve w t u‖^2 = ‖u‖^2 := by
    simp only [hilbert_norm_sq,hilbertEvolve_apply,norm_mul,phase_norm,one_mul]
  nlinarith [norm_nonneg u,norm_nonneg (hilbertEvolve w t u)]

theorem hilbertEvolve_distance (w : ℤ → ℝ) (t : ℝ) (u v : SpectralHilbert) :
    ‖hilbertEvolve w t u-hilbertEvolve w t v‖ = ‖u-v‖ := by
  have hs : ‖hilbertEvolve w t u-hilbertEvolve w t v‖^2 = ‖u-v‖^2 := by
    simp only [hilbert_norm_sq,lp.coeFn_sub,Pi.sub_apply,hilbertEvolve_apply,
      ← mul_sub,norm_mul,phase_norm,one_mul]
  nlinarith [norm_nonneg (u-v),norm_nonneg (hilbertEvolve w t u-hilbertEvolve w t v)]

/-- The physical kinetic generator is the scaled cyclic finite difference. -/
def cyclicKinetic (r : Circle) (N : ℕ) (f : ZMod N → ℂ) (n : ZMod N) : ℂ :=
  ((r.hbar^2/(2*r.mass*(r.length/N)^2) : ℝ) : ℂ)*cyclicDifference f n

theorem cyclicKinetic_spectrum (r : Circle) (N : ℕ) [NeZero N] (j : ℤ) (n : ZMod N) :
    cyclicKinetic r N (fourierCharacter (j : ZMod N)) n =
      ((r.hbar*latticeFrequency r.hbar r.mass (r.length/N) (waveNumber r j) : ℝ) : ℂ)*
        fourierCharacter (j : ZMod N) n := by
  have hL := ne_of_gt r.length_pos
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hk : waveNumber r j*(r.length/N) = 2*Real.pi*j/N := by
    unfold waveNumber; field_simp <;> ring
  rw [cyclicKinetic,cyclic_cosine_eigenvalue]
  unfold latticeFrequency
  rw [hk,← mul_assoc,← Complex.ofReal_mul]
  congr 2
  field_simp
  <;> ring

/-- Uniform global dispersion bound in physical wave number and spacing. -/
theorem frequency_error_band (r : Circle) (a K k : ℝ) (ha : 0 < a)
    (hk : |k| ≤ K) :
    |continuumFrequency r.hbar r.mass k-latticeFrequency r.hbar r.mass a k| ≤
      r.hbar*a^2*K^4/(24*r.mass) := by
  have hh := r.hbar_pos
  have hm := r.mass_pos
  have h := frequency_error_global r.hbar r.mass a k hh.le hm ha.ne'
  rw [abs_of_nonneg h.1]
  have hk4 : k^4 ≤ K^4 := by
    have := pow_le_pow_left₀ (abs_nonneg k) hk 4
    simpa only [pow_abs,abs_of_nonneg (by positivity : 0 ≤ k^4)] using this
  calc
    _ ≤ r.hbar*a^2*k^4/(24*r.mass) := h.2
    _ ≤ _ := by gcongr

/-- Finite-band norm estimate before any measurement or repetition. -/
theorem hilbert_band_error (s : Finset ℤ) (u : SpectralHilbert) (hu : ‖u‖ = 1)
    (hs : ∀ j, j ∉ s → u j = 0) (w v : ℤ → ℝ) (t epsilon : ℝ)
    (he : 0 ≤ epsilon) (h : ∀ j ∈ s, |(-t*w j)-(-t*v j)| ≤ epsilon) :
    ‖hilbertEvolve w t u-hilbertEvolve v t u‖ ≤ epsilon := by
  classical
  have hc : (∑ j : s, ‖u j‖^2) = 1 := by
    have hn := hilbert_norm_sq u
    rw [tsum_eq_sum (s := s) (fun j hj => by simp [hs j hj]),hu] at hn
    calc
      _ = ∑ j ∈ s, ‖u j‖^2 := Finset.sum_coe_sort _ _
      _ = 1 := by simpa using hn.symm
  have hf := finite_phase_error_sq (fun j : s => u j) (fun j => -t*w j) (fun j => -t*v j)
    epsilon he hc (fun j => h j j.property)
  have hd : ‖hilbertEvolve w t u-hilbertEvolve v t u‖^2 ≤ epsilon^2 := by
    rw [hilbert_norm_sq]
    simp only [lp.coeFn_sub,Pi.sub_apply,hilbertEvolve_apply]
    rw [tsum_eq_sum (s := s) (fun j hj => by simp [hs j hj])]
    rw [← Finset.sum_coe_sort]
    exact hf
  nlinarith [norm_nonneg (hilbertEvolve w t u-hilbertEvolve v t u)]

def ringLatticeFrequency (r : Circle) (a : ℝ) (j : ℤ) : ℝ :=
  latticeFrequency r.hbar r.mass a (waveNumber r j)

/-- Normalized lattice approximation of an arbitrary infinite state, with the
actual tail contribution and a uniform bounded-time constant. -/
theorem lattice_tail_error (r : Circle) (s : Finset ℤ) (u : SpectralHilbert)
    (hu : ‖u‖ = 1) (hp : projection s u ≠ 0) (a K T t : ℝ)
    (ha : 0 < a) (hT : 0 ≤ T) (ht : |t| ≤ T)
    (hK : ∀ j ∈ s, |waveNumber r j| ≤ K) (hKa : K*a ≤ 1) :
    ‖hilbertEvolve (frequency r) t u-
      hilbertEvolve (ringLatticeFrequency r a) t (normalizedProjection s u)‖ ≤
      2*Real.sqrt (tail s u)+T*(r.hbar*a^2*K^4/(24*r.mass)) := by
  have he : 0 ≤ T*(r.hbar*a^2*K^4/(24*r.mass)) := by
    have hh := r.hbar_pos; have hm := r.mass_pos
    positivity
  have hb := hilbert_band_error s (normalizedProjection s u) (normalizedProjection_norm s u hp)
    (fun j hj => by simp [normalizedProjection,lp.coeFn_smul,projection_apply,hj])
    (frequency r) (ringLatticeFrequency r a) t _ he (by
      intro j hj
      have hfreq := frequency_error_band r a K (waveNumber r j) ha (hK j hj)
      have hfac : |(-t*frequency r j)-(-t*ringLatticeFrequency r a j)| =
          |t| *|continuumFrequency r.hbar r.mass (waveNumber r j)-
            latticeFrequency r.hbar r.mass a (waveNumber r j)| := by
        rw [show (-t*frequency r j)-(-t*ringLatticeFrequency r a j) =
          -t*(continuumFrequency r.hbar r.mass (waveNumber r j)-
            latticeFrequency r.hbar r.mass a (waveNumber r j)) by
            unfold frequency ringLatticeFrequency continuumFrequency; ring]
        rw [abs_mul,abs_neg]
      rw [hfac]
      exact mul_le_mul ht hfreq (abs_nonneg _) hT)
  calc
    _ ≤ ‖hilbertEvolve (frequency r) t u-hilbertEvolve (frequency r) t (normalizedProjection s u)‖+
      ‖hilbertEvolve (frequency r) t (normalizedProjection s u)-
        hilbertEvolve (ringLatticeFrequency r a) t (normalizedProjection s u)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (hilbertEvolve (frequency r) t u)
          (hilbertEvolve (frequency r) t (normalizedProjection s u))
          (hilbertEvolve (ringLatticeFrequency r a) t (normalizedProjection s u))
    _ ≤ _ := by rw [hilbertEvolve_distance]; exact add_le_add (normalizedProjection_error s u hu hp) hb

/-- Fixed-state, bounded-time strong convergence with an explicit finite cutoff
and a site threshold. Every larger N excludes aliases on the retained band. -/
theorem lattice_strong_convergence (r : Circle) (u : SpectralHilbert) (hu : ‖u‖ = 1)
    (T epsilon : ℝ) (hT : 0 ≤ T) (he : 0 < epsilon) :
    ∃ s : Finset ℤ, ∃ J N₀ : ℕ,
      projection s u ≠ 0 ∧ (∀ j ∈ s, j.natAbs ≤ J) ∧
      ∀ N : ℕ, N₀ ≤ N → 2*J < N ∧ 0 < N ∧
        ∀ t : ℝ, |t| ≤ T →
          ‖hilbertEvolve (frequency r) t u-
            hilbertEvolve (ringLatticeFrequency r (r.length/N)) t (normalizedProjection s u)‖ < epsilon := by
  classical
  have he' : 0 < min (epsilon/4) (1/2) := lt_min (by positivity) (by norm_num)
  have hc := (Metric.tendsto_nhds.mp (projection_tendsto u)) _ he'
  obtain ⟨s,hs⟩ := eventually_atTop.mp hc
  have hd : ‖u-projection s u‖ < min (epsilon/4) (1/2) := by
    simpa [dist_eq_norm,norm_sub_rev] using hs s le_rfl
  have hp : projection s u ≠ 0 := by
    intro hz
    have := hd.trans_le (min_le_right _ _)
    norm_num [hz,hu] at this
  let K : ℝ := ∑ j ∈ s, |waveNumber r j|
  have hK : ∀ j ∈ s, |waveNumber r j| ≤ K := by
    intro j hj
    exact single_le_sum (fun i _ => abs_nonneg (waveNumber r i)) hj
  have ha : Tendsto (fun N : ℕ => r.length/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat r.length
  have hka : Tendsto (fun N : ℕ => K*(r.length/N)) atTop (𝓝 0) := by
    simpa using ha.const_mul K
  have herr : Tendsto (fun N : ℕ => T*(r.hbar*(r.length/N)^2*K^4/(24*r.mass)))
      atTop (𝓝 0) := by
    convert (((ha.pow 2).const_mul (r.hbar)).mul_const (K^4)).div_const (24*r.mass) |>.const_mul T using 1 <;> simp
  let J := s.sup Int.natAbs
  have hJ : ∀ j ∈ s, j.natAbs ≤ J := fun j hj => le_sup hj
  have ev := (hka.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).and
    ((herr.eventually_lt_const (by positivity : (0 : ℝ) < epsilon/2)).and
      (eventually_ge_atTop (2*J+1)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ev
  refine ⟨s,J,N₀,hp,hJ,fun N hN => ?_⟩
  obtain ⟨hka',herr',hlarge⟩ := hN₀ N hN
  have hn : 0 < N := by omega
  refine ⟨by omega,hn,fun t ht => ?_⟩
  have hb := lattice_tail_error r s u hu hp (r.length/N) K T t
    (div_pos r.length_pos (by exact_mod_cast hn)) hT ht hK hka'.le
  rw [tail,Real.sqrt_sq (norm_nonneg _)] at hb
  have hd' := hd.trans_le (min_le_left _ _)
  linarith

/-- No uniformly positive discrimination margin survives refinement at fixed
resources. This concerns the full independent joint data and every finite Born
instrument, uniformly for |t|≤T; it does not assert equality at a fixed N. -/
theorem finite_resource_nonseparation (r : Circle) (u : SpectralHilbert) (hu : ‖u‖ = 1)
    (T margin : ℝ) (hT : 0 ≤ T) (hm : 0 < margin) (n : ℕ) :
    ∃ s : Finset ℤ, ∃ J N₀ : ℕ,
      projection s u ≠ 0 ∧ (∀ j ∈ s, j.natAbs ≤ J) ∧
      ∀ N : ℕ, N₀ ≤ N → 2*J < N ∧ ∀ t : ℝ, |t| ≤ T →
      ∀ (O : Type) [Fintype O] (d : BornInstrument SpectralHilbert O),
      ∀ (h₁ : ‖hilbertEvolve (frequency r) t u‖ = 1)
        (h₂ : ‖hilbertEvolve (ringLatticeFrequency r (r.length/N)) t (normalizedProjection s u)‖ = 1),
      tv (iid (d.distribution (hilbertEvolve (frequency r) t u) h₁) n)
         (iid (d.distribution (hilbertEvolve (ringLatticeFrequency r (r.length/N)) t
           (normalizedProjection s u)) h₂) n) < margin := by
  have he : 0 < margin/((n : ℝ)+1) := by positivity
  obtain ⟨s,J,N₀,hp,hJ,hbound⟩ := lattice_strong_convergence r u hu T _ hT he
  refine ⟨s,J,N₀,hp,hJ,fun N hN => ?_⟩
  obtain ⟨ha,_,hb⟩ := hbound N hN
  refine ⟨ha,fun t ht O _ d h₁ h₂ => ?_⟩
  have hv := (born_iid_tv d _ _ h₁ h₂ n).trans (min_le_right _ _)
  have hd := hb t ht
  have hnon := norm_nonneg (hilbertEvolve (frequency r) t u-
    hilbertEvolve (ringLatticeFrequency r (r.length/N)) t (normalizedProjection s u))
  have hmul := (lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+1)).mp hd
  nlinarith

/-- The operational test-error conclusion with normalization supplied by the
constructed dynamics, rather than postulated event probabilities. -/
theorem finite_resource_test_error (r : Circle) (u : SpectralHilbert) (hu : ‖u‖ = 1)
    (T margin : ℝ) (hT : 0 ≤ T) (hm : 0 < margin) (n : ℕ) :
    ∃ s : Finset ℤ, ∃ J N₀ : ℕ,
      ∃ hp : projection s u ≠ 0, (∀ j ∈ s, j.natAbs ≤ J) ∧
      ∀ N : ℕ, N₀ ≤ N → 2*J < N ∧ ∀ t : ℝ, |t| ≤ T →
      ∀ (O : Type) [Fintype O] (d : BornInstrument SpectralHilbert O),
      let p := d.distribution (hilbertEvolve (frequency r) t u) (by simpa using hu)
      let q := d.distribution (hilbertEvolve (ringLatticeFrequency r (r.length/N)) t (normalizedProjection s u))
        (by simpa using normalizedProjection_norm s u hp)
      ∀ f : Samples O n → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
        1-margin < (iid p n).mean f+(1-(iid q n).mean f) := by
  obtain ⟨s,J,N₀,hp,hJ,h⟩ := finite_resource_nonseparation r u hu T margin hT hm n
  refine ⟨s,J,N₀,hp,hJ,fun N hN => ?_⟩
  obtain ⟨ha,hb⟩ := h N hN
  refine ⟨ha,fun t ht O _ d f hf0 hf1 => ?_⟩
  have hv := hb t ht O d (by simpa using hu) (by simpa using normalizedProjection_norm s u hp)
  have he := test_error
    (iid (d.distribution (hilbertEvolve (frequency r) t u) (by simpa using hu)) n)
    (iid (d.distribution (hilbertEvolve (ringLatticeFrequency r (r.length/N)) t
      (normalizedProjection s u)) (by simpa using normalizedProjection_norm s u hp)) n)
    f hf0 hf1
  linarith

end
end OntologySeparation.ContinuumFinite
