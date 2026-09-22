import OntologySeparation.Adapters.FiniteQuantum
import QIT.HypothesisTesting.Basic
import QIT.Channels.Diamond

/-! An adoption interface for existing Lean-QIT discrimination theorems.
The objective is equal-prior, single-copy decision error. The input states and
accessible Hilbert space are fixed before choosing a test. -/
namespace OntologySeparation.QuantumDiscrimination
noncomputable section
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def minimumError (rho sigma : QIT.State A) : ℝ :=
  (1 / 2) * (1 - rho.normalizedTraceDistance sigma)

def error (rho sigma : QIT.State A) (t : FiniteQuantum.Test A B Bool) : ℝ :=
  (QIT.BinaryHypothesisTest.equalPriorError t.readout (t.evolution.applyState rho)
    (t.evolution.applyState sigma) : ℝ)

/-- Arbitrary finite CPTP preprocessing and binary readout cannot improve the
accessible states' Helstrom optimum. Reuses upstream data processing. -/
theorem every_test (rho sigma : QIT.State A) (t : FiniteQuantum.Test A B Bool) :
    minimumError rho sigma ≤ error rho sigma t := by
  have h := QIT.BinaryHypothesisTest.helstrom_equalPriorError_lower_bound
    t.readout (t.evolution.applyState rho) (t.evolution.applyState sigma)
  have hd := t.evolution.normalizedTraceDistance_applyState_le rho sigma
  unfold minimumError error
  linarith

/-- A proof-bearing mathematical optimum, not an assertion that a given device
can implement its spectral measurement. -/
def optimalTest (rho sigma : QIT.State A) : FiniteQuantum.Test A A Bool :=
  FiniteQuantum.measure (rho.helstromTest sigma)

theorem attained (rho sigma : QIT.State A) :
    error rho sigma (optimalTest rho sigma) = minimumError rho sigma := by
  unfold error optimalTest FiniteQuantum.measure FiniteQuantum.oneStep
  rw [QIT.State.idChannel_applyState, QIT.State.idChannel_applyState]
  exact QIT.State.helstromTest_equalPriorError_eq rho sigma

theorem same_state_error (rho : QIT.State A) (t : FiniteQuantum.Test A B Bool) :
    error rho rho t = 1 / 2 := by
  unfold error
  rw [QIT.BinaryHypothesisTest.equalPriorError_eq_half_one_sub_score]
  simp

theorem strict_improvement (rho sigma : QIT.State A) (h : rho ≠ sigma) :
    minimumError rho sigma < 1 / 2 := by
  have hn := rho.normalizedTraceDistance_nonneg sigma
  have hp : 0 < rho.normalizedTraceDistance sigma := by
    apply lt_of_le_of_ne hn
    intro hz
    exact h (QIT.State.eq_of_normalizedTraceDistance_eq_zero hz.symm)
  unfold minimumError
  linarith
end
end OntologySeparation.QuantumDiscrimination
