import OntologySeparation.Operational.HiddenInfluenceLP
import OntologySeparation.Operational.HiddenInfluenceWitness

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators

private def baseAtom (e : Early) : Atom := ⟨64*e.val, by omega⟩
private theorem base_early (e : Early) : early (baseAtom e) = e := by
  apply Fin.ext
  simp [early, baseAtom]

/-- All four parties always output zero; no signaling in any direction. -/
noncomputable def baseline : Model := Model.ofAtoms baseAtom (fun _ => 1)
  (fun _ => by norm_num) (fun e => by simp [base_early])

set_option maxRecDepth 100000 in
private theorem base_difference_coeff : ∀ c o,
    (∑ e : Early, differenceCoeff c o (baseAtom e)) = 0 := by decide
private theorem base_score_coeff : (∑ e : Early, scoreCoeff (baseAtom e)) = 6 := by decide

theorem baseline_difference (c o) : difference baseline.behavior c o = 0 := by
  rw [baseline, ofAtoms_difference]
  simp only [mul_one]
  exact_mod_cast base_difference_coeff c o

theorem baseline_score : score baseline.behavior = 6 := by
  rw [baseline, ofAtoms_score]
  simp only [mul_one]
  exact_mod_cast base_score_coeff

noncomputable def Model.mix (a b : Model) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Model where
  weight j := t*a.weight j + (1-t)*b.weight j
  nonnegative j := add_nonneg (mul_nonneg h0 (a.nonnegative j))
    (mul_nonneg (sub_nonneg.mpr h1) (b.nonnegative j))
  normalized e := by
    have term (j : Atom) : (if early j = e then t*a.weight j+(1-t)*b.weight j else 0) =
        t*(if early j = e then a.weight j else 0)+(1-t)*(if early j = e then b.weight j else 0) := by
      split <;> simp_all
    simp_rw [term]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, a.normalized, b.normalized]
    ring

theorem mix_score (a b : Model) (t : ℝ) (h0 h1) :
    score (a.mix b t h0 h1).behavior = t*score a.behavior+(1-t)*score b.behavior := by
  simp only [score_eq, Model.mix, mul_add, Finset.sum_add_distrib]
  simp_rw [mul_left_comm _ t, mul_left_comm _ (1-t)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem mix_difference (a b : Model) (t : ℝ) (h0 h1) (c o) :
    difference (a.mix b t h0 h1).behavior c o =
      t*difference a.behavior c o+(1-t)*difference b.behavior c o := by
  simp only [difference_eq, Model.mix, mul_add, Finset.sum_add_distrib]
  simp_rw [mul_left_comm _ t, mul_left_comm _ (1-t)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Attaining family throughout the rising segment 0 ≤ δ ≤ 1/4. -/
noncomputable def family (delta : ℝ) (h0 : 0 ≤ delta) (h1 : delta ≤ 1/4) : Model :=
  Sharp.model.mix baseline (4*delta) (by positivity) (by linarith)

theorem family_score (delta : ℝ) (h0 h1) :
    score (family delta h0 h1).behavior = 6+8*delta := by
  rw [family, mix_score, Sharp.score_exact, baseline_score]
  ring

theorem family_tv (delta : ℝ) (h0 h1) (c) :
    tv (family delta h0 h1).behavior c = (4*delta)*tv Sharp.model.behavior c := by
  simp only [tv, family, mix_difference, baseline_difference, mul_zero, add_zero,
    abs_mul, abs_of_nonneg (show 0 ≤ 4*delta by positivity)]
  rw [← Finset.mul_sum]
  ring

theorem family_budget (delta : ℝ) (h0 h1) : Within (family delta h0 h1).behavior delta := by
  intro c
  rw [family_tv, Sharp.tv_exact]
  split <;> simp_all <;> linarith

theorem family_signaling (delta : ℝ) (h0 h1) : (family delta h0 h1).signaling = delta := by
  apply le_antisymm ((signaling_le_iff _ _).mpr (family_budget delta h0 h1))
  have h := tv_le_signaling (family delta h0 h1) 5
  rw [family_tv, Sharp.tv_exact] at h
  norm_num at h
  linarith

set_option maxRecDepth 100000 in
private theorem algebraic_coeff : ∀ j : Atom, scoreCoeff j ≤
    4*(if early j = 1 then 1 else 0)+4*(if early j = 2 then 1 else 0) := by decide

/-- Algebraic ceiling for the specified score. -/
theorem algebraic_bound (m : Model) : score m.behavior ≤ 8 := by
  rw [score_eq]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right
      (show (scoreCoeff j : ℝ) ≤ 4*(if early j = 1 then 1 else 0)+4*(if early j = 2 then 1 else 0) by
        exact_mod_cast algebraic_coeff j) (m.nonnegative j)
  simp only [add_mul, mul_assoc, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum, m.normalized, m.normalized] at h
  norm_num at h
  exact h

theorem sharp_bound (m : Model) (delta : ℝ) (budget : Within m.behavior delta) :
    score m.behavior ≤ min (6+8*delta) 8 :=
  le_min (score_bound m delta budget) (algebraic_bound m)

/-- An explicit maximizer for every nonnegative allowed signaling budget. -/
noncomputable def optimalModel (delta : ℝ) (h0 : 0 ≤ delta) : Model :=
  if h1 : delta ≤ 1/4 then family delta h0 h1 else Sharp.model

theorem optimal_budget (delta : ℝ) (h0) : Within (optimalModel delta h0).behavior delta := by
  unfold optimalModel
  split
  · exact family_budget _ _ _
  · intro c; exact le_trans (Sharp.budget c) (by linarith)

theorem optimal_score (delta : ℝ) (h0) :
    score (optimalModel delta h0).behavior = min (6+8*delta) 8 := by
  unfold optimalModel
  split
  · rw [family_score, min_eq_left (by linarith)]
  · rw [Sharp.score_exact, min_eq_right (by linarith)]

theorem optimal_signaling (delta : ℝ) (h0) :
    (optimalModel delta h0).signaling = min delta (1/4) := by
  unfold optimalModel
  split
  · rw [family_signaling, min_eq_left (by assumption)]
  · rw [Sharp.signaling_exact, min_eq_right (by linarith)]

/-- A whole-class optimum, not a maximum over a supplied finite protocol list. -/
theorem sharp_tradeoff (delta : ℝ) (h0 : 0 ≤ delta) :
    (∀ m : Model, Within m.behavior delta → score m.behavior ≤ min (6+8*delta) 8) ∧
    ∃ m : Model, Within m.behavior delta ∧ score m.behavior = min (6+8*delta) 8 :=
  ⟨fun m h => sharp_bound m delta h, optimalModel delta h0,
    optimal_budget delta h0, optimal_score delta h0⟩

/-- With intercept 6 fixed, no smaller universal slope can work. This concerns
this fixed completion, not every possible completion of the score. -/
theorem coefficient_optimal (k : ℝ)
    (h : ∀ m : Model, score m.behavior ≤ 6+k*m.signaling) : 8 ≤ k := by
  have hk := h Sharp.model
  rw [Sharp.score_exact, Sharp.signaling_exact] at hk
  linarith

end OntologySeparation.HiddenInfluence
