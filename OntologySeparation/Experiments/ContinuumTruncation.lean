import OntologySeparation.Experiments.ContinuumBorn

/-! Normalized finite projections in the infinite Hilbert space. The explicit
bound is conservative (twice the square root of the tail), including a separate
zero-retained-mass statement. Finite sets are directed by inclusion. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset Filter
open scoped Topology

abbrev SpectralHilbert := lp (fun _ : ℤ => ℂ) 2

def projection (s : Finset ℤ) (u : SpectralHilbert) : SpectralHilbert :=
  ∑ j ∈ s, lp.single 2 j (u j)

def tail (s : Finset ℤ) (u : SpectralHilbert) : ℝ :=
  ‖u-projection s u‖^2

def normalizedProjection (s : Finset ℤ) (u : SpectralHilbert) : SpectralHilbert :=
  (‖projection s u‖⁻¹ : ℝ) • projection s u

@[simp] theorem projection_apply (s : Finset ℤ) (u : SpectralHilbert) (j : ℤ) :
    projection s u j = if j ∈ s then u j else 0 := by
  classical
  simp only [projection,lp.coeFn_sum,lp.coeFn_single,Finset.sum_apply,Finset.sum_pi_single]

theorem projection_norm_sq (s : Finset ℤ) (u : SpectralHilbert) :
    ‖projection s u‖^2 = ∑ j ∈ s, ‖u j‖^2 := by
  simpa [projection] using lp.norm_sum_single (p := (2 : ENNReal)) (by norm_num) (fun j => u j) s

theorem tail_identity (s : Finset ℤ) (u : SpectralHilbert) :
    tail s u = ‖u‖^2-‖projection s u‖^2 := by
  rw [projection_norm_sq]
  simpa [tail,projection] using lp.norm_compl_sum_single (p := (2 : ENNReal)) (by norm_num) u s

theorem tail_sum (s : Finset ℤ) (u : SpectralHilbert) :
    tail s u = ∑' j : {j : ℤ // j ∉ s}, ‖u j‖^2 := by
  have hu : Summable (fun j : ℤ => ‖u j‖^2) := by
    simpa using u.property.summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hsplit := hu.sum_add_tsum_subtype_compl s
  rw [← hilbert_norm_sq] at hsplit
  rw [tail_identity,projection_norm_sq]
  linarith

theorem normalizedProjection_norm (s : Finset ℤ) (u : SpectralHilbert)
    (h : projection s u ≠ 0) : ‖normalizedProjection s u‖ = 1 := by
  rw [normalizedProjection,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem projection_normalization_distance (s : Finset ℤ) (u : SpectralHilbert)
    (h : projection s u ≠ 0) :
    ‖projection s u-normalizedProjection s u‖ = |‖projection s u‖-1| := by
  have hn := norm_ne_zero_iff.mpr h
  have eq : projection s u-normalizedProjection s u =
      (1-‖projection s u‖⁻¹ : ℝ) • projection s u := by
    simp [normalizedProjection,sub_smul]
  rw [eq,norm_smul,Real.norm_eq_abs]
  calc
    _ = |(1-‖projection s u‖⁻¹)*‖projection s u‖| := by
      rw [abs_mul,abs_of_nonneg (norm_nonneg _)]
    _ = _ := by congr 1; field_simp

/-- Derived truncation error; no continuity assumption on a detector is used. -/
theorem normalizedProjection_error (s : Finset ℤ) (u : SpectralHilbert)
    (hu : ‖u‖ = 1) (h : projection s u ≠ 0) :
    ‖u-normalizedProjection s u‖ ≤ 2*Real.sqrt (tail s u) := by
  have hn : |‖projection s u‖-1| ≤ ‖u-projection s u‖ := by
    simpa [hu,norm_sub_rev] using abs_norm_sub_norm_le (projection s u) u
  calc
    ‖u-normalizedProjection s u‖ ≤ ‖u-projection s u‖+‖projection s u-normalizedProjection s u‖ :=
      by simpa only [dist_eq_norm] using dist_triangle u (projection s u) (normalizedProjection s u)
    _ ≤ 2*‖u-projection s u‖ := by rw [projection_normalization_distance s u h]; linarith
    _ = 2*Real.sqrt (tail s u) := by rw [tail,Real.sqrt_sq (norm_nonneg _)]

/-- All mass is discarded exactly when the retained vector vanishes. -/
theorem zero_retained_iff_tail_one (s : Finset ℤ) (u : SpectralHilbert) (hu : ‖u‖ = 1) :
    projection s u = 0 ↔ tail s u = 1 := by
  rw [tail_identity,hu]
  constructor
  · intro h; simp [h]
  · intro h
    have : ‖projection s u‖ = 0 := by nlinarith [norm_nonneg (projection s u)]
    exact norm_eq_zero.mp this

/-- Fixed-state strong truncation convergence, on the full infinite space. -/
theorem projection_tendsto (u : SpectralHilbert) :
    Tendsto (fun s : Finset ℤ => projection s u) atTop (𝓝 u) :=
  lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u

theorem normalizedProjection_tendsto (u : SpectralHilbert) (hu : ‖u‖ = 1) :
    Tendsto (fun s : Finset ℤ => normalizedProjection s u) atTop (𝓝 u) := by
  have h := ((projection_tendsto u).norm.inv₀ (by rw [hu]; norm_num)).smul (projection_tendsto u)
  simpa [normalizedProjection,hu] using h

/-- An explicit finite-cutoff quantifier, uniform over every larger finite set. -/
theorem exists_normalized_cutoff (u : SpectralHilbert) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ s : Finset ℤ, ∀ s' : Finset ℤ, s ⊆ s' →
      ‖u-normalizedProjection s' u‖ < epsilon ∧ projection s' u ≠ 0 := by
  have h1 := (Metric.tendsto_nhds.mp (normalizedProjection_tendsto u hu)) epsilon he
  have h2 := (Metric.tendsto_nhds.mp (projection_tendsto u)) 1 (by norm_num)
  obtain ⟨s,hs⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨s,fun s' hss => ?_⟩
  obtain ⟨ha,hb⟩ := hs s' hss
  refine ⟨by simpa [dist_eq_norm,norm_sub_rev] using ha, ?_⟩
  intro hz
  simpa [hz,dist_eq_norm,hu] using hb

end
end OntologySeparation.ContinuumFinite
