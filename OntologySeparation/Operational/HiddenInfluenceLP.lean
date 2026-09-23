import OntologySeparation.Operational.HiddenInfluenceEncoding

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators

/-- Auxiliaries are actual absolute changes of observable probabilities. -/
noncomputable def Model.lpWeights (m : Model) (j : ForcedSignaling.Column) : ℝ :=
  Fin.addCases (motive := fun _ => ℝ) m.weight (fun k : Fin 128 =>
    let pair := (finProdFinEquiv : Context × Recipient ≃ Fin 128).symm k
    |difference m.behavior pair.1 pair.2|) j

theorem pairing_lpWeights (m : Model) (a : ForcedSignaling.Column → ℤ) :
    ForcedSignaling.pairing a m.lpWeights =
      (∑ j, (a (LP.massColumn j) : ℝ) * m.weight j) +
        ∑ c, ∑ o, (a (LP.slackColumn c o) : ℝ) * |difference m.behavior c o| := by
  unfold ForcedSignaling.pairing
  rw [Fin.sum_univ_add (a := 256) (b := 128)]
  simp only [Model.lpWeights, Fin.addCases_left, Fin.addCases_right]
  congr 1
  rw [← (finProdFinEquiv : Context × Recipient ≃ Fin 128).sum_comp]
  simp only [Fintype.sum_prod_type, Equiv.symm_apply_apply]

theorem lp_normalized (m : Model) (e : Early) :
    ForcedSignaling.pairing (ForcedSignaling.normalization e) m.lpWeights = 1 := by
  rw [pairing_lpWeights]
  simp [LP.normalization_mass, LP.normalization_slack, ite_mul, m.normalized]

theorem lp_abs (m : Model) (c : Context) (o : Recipient) (n : Bool) :
    ForcedSignaling.pairing (ForcedSignaling.constraint (LP.absRow c o n)) m.lpWeights =
      (if n then -difference m.behavior c o else difference m.behavior c o) -
        |difference m.behavior c o| := by
  rw [pairing_lpWeights]
  cases n <;>
    simp [LP.abs_mass, LP.abs_slack, ite_and, ite_mul, ← difference_eq, sub_eq_add_neg]

theorem lp_tv (m : Model) (c : Context) :
    ForcedSignaling.pairing (ForcedSignaling.constraint (LP.tvRow c)) m.lpWeights =
      2 * tv m.behavior c := by
  rw [pairing_lpWeights]
  simp [LP.tv_mass, LP.tv_slack, ite_mul, tv]
  ring

theorem lp_score (m : Model) :
    ForcedSignaling.pairing ForcedSignaling.objective m.lpWeights = score m.behavior := by
  rw [pairing_lpWeights, score_eq]
  simp [LP.objective_mass, LP.objective_slack]

/-- Physics → LP: normalization and a bound on all actual recipient TV distances
suffice. No coefficient/row assumptions are requested from the adopter. -/
noncomputable def Model.toLP (m : Model) (delta : ℝ) (budget : Within m.behavior delta) :
    ForcedSignaling.Feasible delta where
  weights := m.lpWeights
  nonnegative j := by
    unfold Model.lpWeights
    refine Fin.addCases (m := 256) (n := 128) (fun k => ?_) (fun k => ?_) j
    · simpa using m.nonnegative k
    · simp [abs_nonneg]
  normalized := lp_normalized m
  bounded i := by
    by_cases h : i.val < 256
    · let c : Context := ⟨i.val / 16, by omega⟩
      let o : Recipient := ⟨i.val / 2 % 8, by omega⟩
      let n : Bool := i.val % 2 = 1
      have hi : i = LP.absRow c o n := by
        apply Fin.ext
        dsimp [LP.absRow, c, o, n]
        by_cases hm : i.val % 2 = 1 <;> simp [hm] <;> omega
      rw [if_pos h, hi, lp_abs]
      split
      · linarith [neg_le_abs (difference m.behavior c o)]
      · linarith [le_abs_self (difference m.behavior c o)]
    · let c : Context := ⟨i.val - 256, by omega⟩
      have hi : i = LP.tvRow c := by apply Fin.ext; dsimp [LP.tvRow, c]; omega
      rw [if_neg h, hi, lp_tv]
      exact mul_le_mul_of_nonneg_left (budget c) (by norm_num)

theorem score_bound (m : Model) (delta : ℝ) (budget : Within m.behavior delta) :
    score m.behavior ≤ 6 + 8 * delta := by
  have h := ForcedSignaling.bound delta (m.toLP delta budget)
  change ForcedSignaling.pairing ForcedSignaling.objective m.lpWeights ≤ _ at h
  simpa [lp_score] using h

end OntologySeparation.HiddenInfluence
