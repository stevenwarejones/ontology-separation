import OntologySeparation.Experiments.ContinuumStatistics
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Complete finite-outcome Born instruments. Each outcome is a bounded linear
Kraus operator; completeness is the operator normalization, not a continuity
assumption on probabilities. Loss must be an outcome of the instrument. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open Finset

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {O : Type} [Fintype O]

structure BornInstrument (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : Type) [Fintype O] where
  operator : O → H →L[ℂ] H
  complete : ∀ u, (∑ o, ‖operator o u‖^2) = ‖u‖^2

def BornInstrument.distribution (d : BornInstrument H O) (u : H) (hu : ‖u‖ = 1) :
    FiniteDistribution O where
  mass o := ‖d.operator o u‖^2
  nonneg o := sq_nonneg _
  total := by rw [d.complete,hu]; norm_num

/-- The Born rule implies a dimension-independent TV continuity bound. -/
theorem born_tv (d : BornInstrument H O) (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    tv (d.distribution u hu) (d.distribution v hv) ≤ ‖u-v‖ := by
  let a := fun o => ‖d.operator o u‖
  let b := fun o => ‖d.operator o v‖
  let e := fun o => ‖d.operator o (u-v)‖
  have ha : ∑ o, (a o)^2 = 1 := by dsimp [a]; rw [d.complete,hu]; norm_num
  have hb : ∑ o, (b o)^2 = 1 := by dsimp [b]; rw [d.complete,hv]; norm_num
  have he : ∑ o, (e o)^2 = ‖u-v‖^2 := d.complete _
  have hab : (∑ o, (a o+b o)^2) ≤ 4 := by
    calc
      _ ≤ ∑ o, (2*(a o)^2+2*(b o)^2) := by
        apply sum_le_sum
        intro o _
        nlinarith [sq_nonneg (a o-b o)]
      _ = 4 := by rw [sum_add_distrib,← mul_sum,← mul_sum,ha,hb]; norm_num
  have hc := sum_mul_sq_le_sq_mul_sq univ e (fun o => a o+b o)
  rw [he] at hc
  have hs : (∑ o, e o*(a o+b o)) ≤ 2*‖u-v‖ := by
    have hm := mul_le_mul_of_nonneg_left hab (sq_nonneg ‖u-v‖)
    nlinarith [norm_nonneg (u-v)]
  have hl : l1 (d.distribution u hu) (d.distribution v hv) ≤
      ∑ o, e o*(a o+b o) := by
    apply sum_le_sum
    intro o _
    change |(a o)^2-(b o)^2| ≤ e o*(a o+b o)
    rw [show (a o)^2-(b o)^2 = (a o-b o)*(a o+b o) by ring,abs_mul,
      abs_of_nonneg (by dsimp [a,b]; positivity : 0 ≤ a o+b o)]
    apply mul_le_mul_of_nonneg_right _ (by dsimp [a,b]; positivity)
    simpa only [a,b,e,map_sub] using abs_norm_sub_norm_le (d.operator o u) (d.operator o v)
  unfold tv
  linarith

/-- Actual joint-product bound for repeated measurements of nearby pure states. -/
theorem born_iid_tv (d : BornInstrument H O) (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (n : ℕ) :
    tv (iid (d.distribution u hu) n) (iid (d.distribution v hv) n) ≤ min 1 (n*‖u-v‖) := by
  apply le_min (tv_le_one _ _)
  exact (iid_tv _ _ n).trans (mul_le_mul_of_nonneg_left (born_tv d u v hu hv) (Nat.cast_nonneg n))

/-- Every randomized test of the joint data has this lower bound on its two errors. -/
theorem born_test_error (d : BornInstrument H O) (u v : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (n : ℕ) (f : Samples O n → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    1-min 1 (n*‖u-v‖) ≤ (iid (d.distribution u hu) n).mean f +
      (1-(iid (d.distribution v hv) n).mean f) := by
  have ht := test_error (iid (d.distribution u hu) n) (iid (d.distribution v hv) n) f hf0 hf1
  have hb := born_iid_tv d u v hu hv n
  linarith

/-- Identify the existing square-summable coefficients with the Hilbert space l². -/
def SpectralVector.toHilbert (c : SpectralVector) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨c.coefficient, memℓp_gen (by simpa using c.summable)⟩

@[simp] theorem SpectralVector.toHilbert_apply (c : SpectralVector) (j : ℤ) :
    c.toHilbert j = c.coefficient j := rfl

theorem hilbert_norm_sq (u : lp (fun _ : ℤ => ℂ) 2) :
    ‖u‖^2 = ∑' j, ‖u j‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) u

theorem spectral_hilbert_mass (c : SpectralVector) : ‖c.toHilbert‖^2 = mass c :=
  hilbert_norm_sq _

theorem spectral_hilbert_normalized (c : SpectralVector) (hc : mass c = 1) :
    ‖c.toHilbert‖ = 1 := by
  have h := spectral_hilbert_mass c
  rw [hc] at h
  nlinarith [norm_nonneg c.toHilbert]

end
end OntologySeparation.ContinuumFinite
