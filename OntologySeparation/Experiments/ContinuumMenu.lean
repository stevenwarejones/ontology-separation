import OntologySeparation.Experiments.ContinuumLimit

/-! Fixed independent acquisition with heterogeneous complete outcome spaces,
preparations, times and nonnegative integer repetition counts. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset Filter
open scoped Topology

section Products
variable {I : Type} (O : I → Type) [∀ s, Fintype (O s)] (n : I → ℕ)

def MenuSamples : List I → Type
  | [] => Unit
  | s :: m => Samples (O s) (n s) × MenuSamples m

@[reducible] def menuFintype : (m : List I) → Fintype (MenuSamples O n m)
  | [] => inferInstanceAs (Fintype Unit)
  | s :: m => by
      letI := menuFintype m
      exact inferInstanceAs (Fintype (Samples (O s) (n s) × MenuSamples O n m))

instance (m : List I) : Fintype (MenuSamples O n m) := menuFintype O n m

/-- Each multinomial observation stays intact; only trials/settings are independent. -/
def menuLaw (p : ∀ s, FiniteDistribution (O s)) :
    (m : List I) → FiniteDistribution (MenuSamples O n m)
  | [] =>
      { mass := fun _ => 1
        nonneg := by intro; norm_num
        total := by simp [MenuSamples] }
  | s :: m => distributionProduct (iid (p s) (n s)) (menuLaw p m)

theorem menu_tv (p q : ∀ s, FiniteDistribution (O s)) (m : List I)
    (epsilon : I → ℝ) (h : ∀ s ∈ m, tv (p s) (q s) ≤ epsilon s) :
    tv (menuLaw O n p m) (menuLaw O n q m) ≤
      min 1 ((m.map fun s => (n s : ℝ)*epsilon s).sum) := by
  apply le_min (tv_le_one _ _)
  induction m with
  | nil => simp [menuLaw, tv, l1]
  | cons s m ih =>
    have hs := (iid_tv (p s) (q s) (n s)).trans
      (mul_le_mul_of_nonneg_left (h s (by simp)) (Nat.cast_nonneg _))
    have hm := ih (fun k hk => h k (by simp [hk]))
    have hp := product_tv (iid (p s) (n s)) (iid (q s) (n s))
      (menuLaw O n p m) (menuLaw O n q m)
    change tv (distributionProduct _ _) (distributionProduct _ _) ≤ _
    simp only [List.map_cons, List.sum_cons]
    linarith

theorem menu_test_error (p q : ∀ s, FiniteDistribution (O s)) (m : List I)
    (epsilon : I → ℝ) (h : ∀ s ∈ m, tv (p s) (q s) ≤ epsilon s)
    (f : MenuSamples O n m → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    1-min 1 ((m.map fun s => (n s : ℝ)*epsilon s).sum) ≤
      (menuLaw O n p m).mean f + (1-(menuLaw O n q m).mean f) := by
  have ht := test_error (menuLaw O n p m) (menuLaw O n q m) f hf0 hf1
  have hb := menu_tv O n p q m epsilon h
  linarith
end Products

/-- One common cutoff and site threshold for a finite family of fixed states.
The bounded-time approximation remains uniform over all finite Born readouts. -/
theorem finite_family_convergence {I : Type} [Fintype I] (r : Circle)
    (u : I → SpectralHilbert) (hu : ∀ i, ‖u i‖ = 1)
    (T epsilon : ℝ) (hT : 0 ≤ T) (he : 0 < epsilon) :
    ∃ s : Finset ℤ, ∃ J N₀ : ℕ,
      (∀ i, projection s (u i) ≠ 0) ∧ (∀ j ∈ s, j.natAbs ≤ J) ∧
      ∀ N : ℕ, N₀ ≤ N → 2*J < N ∧ 0 < N ∧ ∀ i, ∀ t : ℝ, |t| ≤ T →
        ‖hilbertEvolve (frequency r) t (u i)-
          hilbertEvolve (ringLatticeFrequency r (r.length/N)) t (normalizedProjection s (u i))‖ < epsilon := by
  classical
  have he' : 0 < min (epsilon/4) (1/2) := lt_min (by positivity) (by norm_num)
  have hc : ∀ᶠ s : Finset ℤ in atTop, ∀ i, dist (projection s (u i)) (u i) < min (epsilon/4) (1/2) :=
    Filter.eventually_all.mpr (fun i =>
      (Metric.tendsto_nhds.mp (projection_tendsto (u i))) _ he')
  obtain ⟨s, hs⟩ := eventually_atTop.mp hc
  have hd (i : I) : ‖u i-projection s (u i)‖ < min (epsilon/4) (1/2) := by
    simpa [dist_eq_norm, norm_sub_rev] using hs s le_rfl i
  have hp (i : I) : projection s (u i) ≠ 0 := by
    intro hz
    have h := (hd i).trans_le (min_le_right _ _)
    norm_num [hz, hu i] at h
  let K : ℝ := ∑ j ∈ s, |waveNumber r j|
  have hK : ∀ j ∈ s, |waveNumber r j| ≤ K :=
    fun j hj => single_le_sum (fun k _ => abs_nonneg (waveNumber r k)) hj
  have ha : Tendsto (fun N : ℕ => r.length/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat r.length
  have herr : Tendsto (fun N : ℕ => T*(r.hbar*(r.length/N)^2*K^4/(24*r.mass)))
      atTop (𝓝 0) := by
    convert (((ha.pow 2).const_mul r.hbar).mul_const (K^4)).div_const (24*r.mass)
      |>.const_mul T using 1 <;> simp
  let J := s.sup Int.natAbs
  have hJ : ∀ j ∈ s, j.natAbs ≤ J := fun j hj => le_sup hj
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((herr.eventually_lt_const (by positivity : (0 : ℝ) < epsilon/2)).and
      (eventually_ge_atTop (2*J+1)))
  refine ⟨s, J, N₀, hp, hJ, fun N hN => ?_⟩
  obtain ⟨herr', hlarge⟩ := hN₀ N hN
  have hn : 0 < N := by omega
  refine ⟨by omega, hn, fun i t ht => ?_⟩
  have hb := lattice_tail_error r s (u i) (hu i) (hp i) (r.length/N) K T t
    (div_pos r.length_pos (by exact_mod_cast hn)) hT ht hK
  rw [tail, Real.sqrt_sq (norm_nonneg _)] at hb
  have hd' := (hd i).trans_le (min_le_left _ _)
  linarith

/-- Fixed finite protocols have no uniformly positive refinement margin. States,
counts and menu are fixed before choosing the common cutoff/site threshold. -/
theorem finite_menu_nonseparation {I : Type} [Fintype I]
    (O : I → Type) [∀ i, Fintype (O i)] (r : Circle)
    (u : I → SpectralHilbert) (hu : ∀ i, ‖u i‖ = 1)
    (d : ∀ i, BornInstrument SpectralHilbert (O i)) (n : I → ℕ) (m : List I)
    (t : I → ℝ) (T margin : ℝ) (hT : 0 ≤ T) (ht : ∀ i, |t i| ≤ T) (hm : 0 < margin) :
    ∃ s : Finset ℤ, ∃ J N₀ : ℕ, ∃ hp : ∀ i, projection s (u i) ≠ 0,
      (∀ j ∈ s, j.natAbs ≤ J) ∧ ∀ N : ℕ, N₀ ≤ N → 2*J < N ∧
      let p := fun i => (d i).distribution (hilbertEvolve (frequency r) (t i) (u i)) (by simp [hu i])
      let q := fun i => (d i).distribution
        (hilbertEvolve (ringLatticeFrequency r (r.length/N)) (t i) (normalizedProjection s (u i)))
        (by simpa using normalizedProjection_norm s (u i) (hp i))
      tv (menuLaw O n p m) (menuLaw O n q m) < margin ∧
      ∀ f : MenuSamples O n m → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
        1-margin < (menuLaw O n p m).mean f+(1-(menuLaw O n q m).mean f) := by
  let budget : ℝ := (m.map fun i => (n i : ℝ)).sum
  have hbudget : 0 ≤ budget := List.sum_nonneg (by intro x hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; positivity)
  have he : 0 < margin/(budget+1) := div_pos hm (by positivity)
  obtain ⟨s,J,N₀,hp,hJ,hbound⟩ := finite_family_convergence r u hu T _ hT he
  refine ⟨s,J,N₀,hp,hJ,fun N hN => ?_⟩
  obtain ⟨ha,_,hb⟩ := hbound N hN
  refine ⟨ha, ?_⟩
  dsimp only
  let p := fun i => (d i).distribution (hilbertEvolve (frequency r) (t i) (u i)) (by simp [hu i])
  let q := fun i => (d i).distribution
    (hilbertEvolve (ringLatticeFrequency r (r.length/N)) (t i) (normalizedProjection s (u i)))
    (by simpa using normalizedProjection_norm s (u i) (hp i))
  have hclose (i : I) : tv (p i) (q i) ≤ margin/(budget+1) :=
    (born_tv (d i) _ _ _ _).trans (le_of_lt (hb i (t i) (ht i)))
  have hv := (menu_tv O n p q m (fun _ => margin/(budget+1)) (fun i _ => hclose i)).trans
    (min_le_right _ _)
  rw [List.sum_map_mul_right] at hv
  have hbmargin : budget*(margin/(budget+1)) < margin := by
    have h := (div_mul_cancel₀ margin (by positivity : budget+1 ≠ 0))
    nlinarith
  have htv : tv (menuLaw O n p m) (menuLaw O n q m) < margin := hv.trans_lt hbmargin
  refine ⟨htv, fun f hf0 hf1 => ?_⟩
  have htest := test_error (menuLaw O n p m) (menuLaw O n q m) f hf0 hf1
  linarith

end
end OntologySeparation.ContinuumFinite
