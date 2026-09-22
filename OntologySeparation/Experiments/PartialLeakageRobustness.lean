import OntologySeparation.Experiments.PartialLeakage
import Mathlib.Tactic

/-! Symbolic robustness region for the partial-leakage/recovery showcase.

This is a theorem path, not a finite-grid scan. The real-valued theorem covers
the full continuous parameter square; the exact rational backend then produces
a proof-bearing separator at any supported exact point in that region. -/
namespace OntologySeparation.PartialLeakage
noncomputable section
open Recipes RecipeSeparation ExperimentAccess

/-- The continuous probability-gap formula corresponding to the exact model. -/
def realGap (visibility recovery : ℝ) : ℝ :=
  visibility * recovery / 2

/-- Real parameters define an actual dephasing channel on the full physical square. -/
def realNoise (v r : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Qubit.Noise where
  strength := 1 - v * r
  nonneg := by nlinarith
  le_one := by nlinarith

/-- The continuous formula is the Born-rule gap in the existing real-qubit
semantics, not just an algebraic extension of rational samples. -/
theorem real_channel_gap (v r : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (Qubit.experiment (Qubit.dephase (realNoise v r hv0 hv1 hr0 hr1))).behavior.prob () true -
      (Qubit.experiment (Qubit.dephase ⟨1, by norm_num, by norm_num⟩)).behavior.prob () true =
      realGap v r := by
  simp [Qubit.experiment, Experiment.behavior, Qubit.dephase,
    Qubit.plus, Qubit.readX, realNoise, realGap]
  ring

/-- Over physical nonnegative parameters, the recovery signal is strictly
positive exactly when both parameters are positive (including upper edges). -/
theorem realGap_positive_iff {visibility recovery : ℝ}
    (hv : 0 ≤ visibility) (hr : 0 ≤ recovery) :
    0 < realGap visibility recovery ↔ 0 < visibility ∧ 0 < recovery := by
  simp only [realGap, div_pos_iff]
  constructor
  · intro h
    have hp : 0 < visibility * recovery := by
      rcases h with h | h
      · exact h.1
      · norm_num at h
    exact ⟨pos_of_mul_pos_left hp hr, pos_of_mul_pos_right hp hv⟩
  · rintro ⟨hvpos, hrpos⟩
    exact Or.inl ⟨mul_pos hvpos hrpos, by norm_num⟩

/-- The exact rational gap embeds into the continuous real formula. -/
theorem exact_gap_eq_realGap (m : Mechanism) :
    ((probability m.wignerLaw coherenceProbe -
      probability friendLaw coherenceProbe : ℚ) : ℝ) =
      realGap (m.visibility.value : ℝ) (m.recovery.value : ℝ) := by
  rw [recovery_gap]
  simp [realGap]

/-- Positive retained visibility and positive recovery efficiency make the
Wigner law strictly less dephased than the fully leaked friend law. -/
theorem wigner_exposure_lt_friend (m : Mechanism)
    (hv : 0 < m.visibility.value) (hr : 0 < m.recovery.value) :
    m.wignerLaw.exposure.value < friendLaw.exposure.value := by
  have hp : 0 < m.visibility.value * m.recovery.value := mul_pos hv hr
  simp [Mechanism.wignerLaw, Mechanism.recoverableCoherence, Rate.complement,
    Rate.mul, friendLaw, Law.dephasing, Rate.fraction]
  linarith

/-- Every exact point in the positive robustness region carries the existing
proof-bearing separator certificate for the coherence/recovery experiment. -/
def separator (m : Mechanism)
    (hv : 0 < m.visibility.value) (hr : 0 < m.recovery.value) :
    Separator RecipeSeparation.predict (fun r => r = coherenceProbe)
      m.wignerLaw friendLaw :=
  coherenceSeparator m.wignerLaw friendLaw (wigner_exposure_lt_friend m hv hr)

/-- At either physical boundary the checked recovery gap vanishes. This says
this witness no longer separates; it does not assert global model equivalence. -/
theorem zero_visibility_gap (m : Mechanism) (h : m.visibility.value = 0) :
    probability m.wignerLaw coherenceProbe - probability friendLaw coherenceProbe = 0 := by
  rw [recovery_gap, h]
  ring

theorem zero_recovery_gap (m : Mechanism) (h : m.recovery.value = 0) :
    probability m.wignerLaw coherenceProbe - probability friendLaw coherenceProbe = 0 := by
  rw [recovery_gap, h]
  ring

/-- In this effective-law family the zero-signal boundary is actual law equality,
not merely failure of this witness. This does not identify broader ontologies. -/
theorem zero_visibility_law (m : Mechanism) (h : m.visibility.value = 0) :
    m.wignerLaw = friendLaw := by
  simp [Mechanism.wignerLaw, Mechanism.recoverableCoherence, Rate.complement,
    Rate.mul, friendLaw, Law.dephasing, Rate.fraction, h]

theorem zero_recovery_law (m : Mechanism) (h : m.recovery.value = 0) :
    m.wignerLaw = friendLaw := by
  simp [Mechanism.wignerLaw, Mechanism.recoverableCoherence, Rate.complement,
    Rate.mul, friendLaw, Law.dephasing, Rate.fraction, h]

end
end OntologySeparation.PartialLeakage
