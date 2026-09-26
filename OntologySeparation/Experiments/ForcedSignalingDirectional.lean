import OntologySeparation.Experiments.ForcedSignalingTheorem2
import OntologySeparation.Operational.HiddenInfluenceLP

/-!
# Directional forced-signaling refinement

Kernel-checked port of Proposition 1 of the forced-signaling manuscript.

The 16 early-setting comparisons split exactly as in the certificate verifier:
contexts 0..7 change A's setting x, and contexts 8..15 change D's setting w.
The K=8 dual certificate then yields the sharper directional inequality
  S4^op <= 6 + 4 deltaA + 4 deltaD.
-/

namespace OntologySeparation.ForcedSignalingDirectional
noncomputable section
open scoped BigOperators
open HiddenInfluence

def contextA (i : Fin 8) : Context := Fin.castAdd 8 i
def contextD (i : Fin 8) : Context := Fin.natAdd 8 i

noncomputable def deltaA (m : Model) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 8 => tv m.behavior (contextA i))

noncomputable def deltaD (m : Model) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 8 => tv m.behavior (contextD i))

theorem tv_le_deltaA (m : Model) (i : Fin 8) :
    tv m.behavior (contextA i) ≤ deltaA m := by
  unfold deltaA
  exact Finset.le_sup' (fun k : Fin 8 => tv m.behavior (contextA k))
    (Finset.mem_univ i)

theorem tv_le_deltaD (m : Model) (i : Fin 8) :
    tv m.behavior (contextD i) ≤ deltaD m := by
  unfold deltaD
  exact Finset.le_sup' (fun k : Fin 8 => tv m.behavior (contextD k))
    (Finset.mem_univ i)

theorem deltaA_le_signaling (m : Model) : deltaA m ≤ m.signaling := by
  unfold deltaA
  apply Finset.sup'_le
  intro i _
  exact tv_le_signaling m (contextA i)

theorem deltaD_le_signaling (m : Model) : deltaD m ≤ m.signaling := by
  unfold deltaD
  apply Finset.sup'_le
  intro i _
  exact tv_le_signaling m (contextD i)

theorem signaling_eq_max (m : Model) :
    m.signaling = max (deltaA m) (deltaD m) := by
  apply le_antisymm
  · rw [signaling_le_iff]
    intro c
    by_cases h : c.val < 8
    · let i : Fin 8 := ⟨c.val, h⟩
      have hc : contextA i = c := by apply Fin.ext; rfl
      rw [← hc]
      exact le_trans (tv_le_deltaA m i) (le_max_left _ _)
    · let i : Fin 8 := ⟨c.val - 8, by omega⟩
      have hc : contextD i = c := by
        apply Fin.ext
        dsimp [contextD, i]
        omega
      rw [← hc]
      exact le_trans (tv_le_deltaD m i) (le_max_right _ _)
  · exact max_le (deltaA_le_signaling m) (deltaD_le_signaling m)

theorem deltaA_nonnegative (m : Model) : 0 ≤ deltaA m :=
  le_trans (by unfold tv; positivity) (tv_le_deltaA m 0)

theorem deltaD_nonnegative (m : Model) : 0 ≤ deltaD m :=
  le_trans (by unfold tv; positivity) (tv_le_deltaD m 0)

private theorem row_bound (m : Model) (i : ForcedSignaling.Row) :
    ForcedSignaling.pairing (ForcedSignaling.constraint i) m.lpWeights ≤
      if i.val < 256 then 0
      else if i.val < 264 then 2 * deltaA m else 2 * deltaD m := by
  by_cases h : i.val < 256
  · let c : Context := ⟨i.val / 16, by omega⟩
    let o : Recipient := ⟨i.val / 2 % 8, by omega⟩
    let n : Bool := i.val % 2 = 1
    have hi : i = HiddenInfluence.LP.absRow c o n := by
      apply Fin.ext
      dsimp [HiddenInfluence.LP.absRow, c, o, n]
      by_cases hm : i.val % 2 = 1 <;> simp [hm] <;> omega
    rw [if_pos h, hi, HiddenInfluence.lp_abs]
    split
    · linarith [neg_le_abs (difference m.behavior c o)]
    · linarith [le_abs_self (difference m.behavior c o)]
  · let c : Context := ⟨i.val - 256, by omega⟩
    have hi : i = HiddenInfluence.LP.tvRow c := by
      apply Fin.ext
      dsimp [HiddenInfluence.LP.tvRow, c]
      omega
    rw [if_neg h, hi, HiddenInfluence.lp_tv]
    by_cases hc8 : c.val < 8
    · rw [if_pos (by dsimp [HiddenInfluence.LP.tvRow]; omega)]
      let k : Fin 8 := ⟨c.val, hc8⟩
      have hc : contextA k = c := by
        apply Fin.ext
        rfl
      exact mul_le_mul_of_nonneg_left (by simpa [hc] using tv_le_deltaA m k) (by norm_num)
    · rw [if_neg (by dsimp [HiddenInfluence.LP.tvRow]; omega)]
      let k : Fin 8 := ⟨c.val - 8, by omega⟩
      have hc : contextD k = c := by
        apply Fin.ext
        dsimp [contextD, k]
        omega
      exact mul_le_mul_of_nonneg_left (by simpa [hc] using tv_le_deltaD m k) (by norm_num)

private theorem support_budget (m : Model) :
    (∑ k : Fin 36,
      ForcedSignaling.pairing
        (ForcedSignaling.constraint (ForcedSignaling.support k)) m.lpWeights)
      ≤ 4 * deltaA m + 4 * deltaD m := by
  calc
    _ ≤ ∑ k : Fin 36,
        (if (ForcedSignaling.support k).val < 256 then 0
         else if (ForcedSignaling.support k).val < 264
         then 2 * deltaA m else 2 * deltaD m) :=
      Finset.sum_le_sum fun k _ => row_bound m (ForcedSignaling.support k)
    _ = _ := by
      norm_num [ForcedSignaling.support, Fin.sum_univ_succ]
      ring

/-- Proposition 1 directional refinement of the K=8 tradeoff. -/
theorem directional_bound (m : Model) :
    score m.behavior ≤ 6 + 4 * deltaA m + 4 * deltaD m := by
  have hcol (j : ForcedSignaling.Column) : (ForcedSignaling.objective j : ℝ) ≤
      (∑ k : Fin 4, (ForcedSignaling.normalizationDual k : ℝ) *
        (ForcedSignaling.normalization k j : ℝ)) +
      ∑ k : Fin 36, (ForcedSignaling.constraint (ForcedSignaling.support k) j : ℝ) := by
    exact_mod_cast ForcedSignaling.dual_feasible j
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hcol j)
      (show 0 ≤ m.lpWeights j by
        unfold Model.lpWeights
        refine Fin.addCases (m := 256) (n := 128) (fun a => ?_) (fun a => ?_) j
        · simpa only [Fin.addCases_left] using m.nonnegative a
        · simp only [Fin.addCases_right, abs_nonneg]))
  have hn : (∑ k : Fin 4, (ForcedSignaling.normalizationDual k : ℝ) *
      ForcedSignaling.pairing (ForcedSignaling.normalization k) m.lpWeights) = 6 := by
    norm_num [HiddenInfluence.lp_normalized, ForcedSignaling.normalizationDual,
      Fin.sum_univ_succ]
  have heq : (∑ j : ForcedSignaling.Column,
      ((∑ k : Fin 4, (ForcedSignaling.normalizationDual k : ℝ) *
          (ForcedSignaling.normalization k j : ℝ)) +
        ∑ k : Fin 36, (ForcedSignaling.constraint (ForcedSignaling.support k) j : ℝ)) *
          m.lpWeights j) =
      (∑ k : Fin 4, (ForcedSignaling.normalizationDual k : ℝ) *
        ForcedSignaling.pairing (ForcedSignaling.normalization k) m.lpWeights) +
      ∑ k : Fin 36,
        ForcedSignaling.pairing
          (ForcedSignaling.constraint (ForcedSignaling.support k)) m.lpWeights := by
    simp only [ForcedSignaling.pairing, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1 <;> rw [Finset.sum_comm]
  change ForcedSignaling.pairing ForcedSignaling.objective m.lpWeights ≤ _ at h
  rw [heq, hn, HiddenInfluence.lp_score] at h
  linarith [support_budget m]

/-- LC4 directional lower bound: the sum of directional signaling strengths is
at least twice the scalar optimum. -/
theorem lc4_directional_lower_bound {m : Model}
    (h : ForcedSignalingTheorem2.MatchesCluster m) :
    (Real.sqrt 2 - 1) / 2 ≤ deltaA m + deltaD m := by
  have hs := directional_bound m
  rw [ForcedSignalingTheorem2.matches_score h] at hs
  linarith

end
end OntologySeparation.ForcedSignalingDirectional
