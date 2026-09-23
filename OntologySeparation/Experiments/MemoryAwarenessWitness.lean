import Mathlib
import OntologySeparation.Experiments.MemoryAwareness

/-! Exact arithmetic witness for the Baumann--Brukner memory-awareness obstruction.

Appendix B of Baumann & Brukner, Quantum 8, 1481 (2024), derives under the
non-signaling requirement an effective flip probability

  q = 2 |a|^2 |b|^2
      - (2 sqrt(2) / 3) (|a|^3 |b| - |a| |b|^3) cos(Δφ).

For the normalized real Wigner coefficients a = 24/25, b = 7/25 and phase
cos(Δφ)=1, this required q is negative.  Hence no probability can satisfy the
paper's non-signaling compatibility condition at this explicit setting.

This file checks the arithmetic consequence of the published formula.  It does
not yet derive that formula from the repository's own quantum circuit semantics. -/

namespace OntologySeparation.MemoryAwarenessWitness
noncomputable section

def a : ℝ := 24 / 25
def b : ℝ := 7 / 25

def requiredNoSignalQ : ℝ :=
  2 * a^2 * b^2 -
    (2 * Real.sqrt 2 / 3) * (a^3 * b - a * b^3)

theorem wigner_coefficients_normalized : a^2 + b^2 = 1 := by
  norm_num [a, b]

theorem sqrt_two_gt_seven_fifths : (7 : ℝ) / 5 < Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- The candidate flip rate forced by the published non-signaling equations is
strictly negative at this exact normalized setting. -/
theorem requiredNoSignalQ_negative : requiredNoSignalQ < 0 := by
  have hs := sqrt_two_gt_seven_fifths
  unfold requiredNoSignalQ a b
  norm_num
  nlinarith

/-- Therefore the required quantity cannot be a probability. -/
theorem no_probability_realizes_requiredNoSignalQ :
    ¬ ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ q = requiredNoSignalQ := by
  rintro ⟨q, hq0, hq1, hq⟩
  rw [hq] at hq0
  exact (not_lt_of_ge hq0) requiredNoSignalQ_negative

/-- In particular, there is no bounded rate in [0,1] satisfying the published
non-signaling candidate value. -/
theorem explicit_setting_forces_signaling_or_unfaithful_model :
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q ≠ requiredNoSignalQ := by
  intro q h0 h1 hq
  exact no_probability_realizes_requiredNoSignalQ ⟨q, h0, h1, hq⟩

end
end OntologySeparation.MemoryAwarenessWitness
