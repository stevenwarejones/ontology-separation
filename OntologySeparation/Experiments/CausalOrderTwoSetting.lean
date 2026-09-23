import OntologySeparation.Experiments.CausalOrderAdversary

/-! A two-setting follow-up to the P06 fixed-order adversary.

The first setting uses the anticommuting X/Z pair already in P06. The second
uses X/X, whose two coherent orders coincide. This richer table distinguishes
the coherent-control circuit from the specific fixed-sequence adversary that
mimicked the original scalar fringe.

It is NOT a causal-order inequality: a more general definite-order class with
setting-dependent instruments has not yet been excluded. -/
namespace OntologySeparation.CausalOrderTwoSetting
open Research CausalOrderAdversary

def xxMinus (v : Vector) : Rat :=
  normSq (fun b => (xGate (xGate v) b - xGate (xGate v) b) / 2)

theorem xxMinus_zero (v : Vector) : xxMinus v = 0 := by
  simp [xxMinus, normSq]

def coherentProbability (setting : Bool) (v : Vector) : Rat :=
  if setting then xxMinus v else orderMinus v

def fixedProbability (setting : Bool) (v : Vector) : Rat :=
  if setting then normSq (xGate (xGate v)) else normSq (xGate (zGate v))

theorem fixedProbability_eq_norm (setting : Bool) (v : Vector) :
    fixedProbability setting v = normSq v := by
  cases setting
  · simp [fixedProbability, CausalOrderAdversary.xGate_norm,
      CausalOrderAdversary.zGate_norm]
  · simp [fixedProbability, CausalOrderAdversary.xGate_norm]

theorem coherent_xz_eq_norm (v : Vector) :
    coherentProbability false v = normSq v := by
  simp [coherentProbability, order_probability]

theorem coherent_xx_zero (v : Vector) :
    coherentProbability true v = 0 := by
  simp [coherentProbability, xxMinus_zero]

theorem old_setting_still_mimicked (v : Vector) :
    fixedProbability false v = coherentProbability false v := by
  rw [fixedProbability_eq_norm, coherent_xz_eq_norm]

theorem xx_setting_separates (v : Vector) (hnorm : normSq v = 1) :
    fixedProbability true v - coherentProbability true v = 1 := by
  rw [fixedProbability_eq_norm, coherent_xx_zero, hnorm]
  norm_num

theorem two_setting_not_equivalent (v : Vector) (hnorm : normSq v = 1) :
    ¬ (∀ setting, fixedProbability setting v = coherentProbability setting v) := by
  intro h
  have htrue := h true
  rw [fixedProbability_eq_norm, coherent_xx_zero, hnorm] at htrue
  norm_num at htrue

end OntologySeparation.CausalOrderTwoSetting
