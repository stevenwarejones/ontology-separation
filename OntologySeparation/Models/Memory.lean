import OntologySeparation.Runtime.Memory
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Proofs about the exact executable rational memory engine.
The engine is shared with the report; there is no second numerical implementation. -/
namespace OntologySeparation.Memory

/-- Physically permitted parameter values, kept in the proof layer. -/
structure Model where
  strength : ℚ
  nonneg : 0 ≤ strength
  atMostOne : strength ≤ 1

instance : Coe Model Parameters := ⟨fun m => ⟨m.strength⟩⟩


/-- Exact parametric prediction; derived from matrix operations, not entered as a table. -/
theorem echo_probability (m : Parameters) : probability m echo = 1 - m.strength / 2 := by
  simp [probability, echo, run, step, readPlus, Parameters.record, cnot,
    cnotIndex, dephase, initial, Bool.xor]
  ring

theorem leakedEcho_probability (m : Parameters) : probability m leakedEcho = 1/2 := by
  simp [probability, leakedEcho, run, step, readPlus, Parameters.record, cnot,
    cnotIndex, dephase, initial, Bool.xor]
  ring

theorem phaseEcho_probability (m : Parameters) : probability m phaseEcho = m.strength / 2 := by
  simp [probability, phaseEcho, run, step, readPlus, Parameters.record, cnot,
    cnotIndex, dephase, initial, Bool.xor, phaseSign]
  ring

theorem echo_separates : probability unitary echo ≠ probability collapse echo := by
  rw [echo_probability, echo_probability]
  norm_num [unitary, collapse]

theorem leakedEcho_indistinguishable (a b : Parameters) :
    probability a leakedEcho = probability b leakedEcho := by
  rw [leakedEcho_probability, leakedEcho_probability]

/-- No irreversible event is undone by the reverse instruction. -/
theorem echo_probability_range (m : Model) :
    0 ≤ probability m echo ∧ probability m echo ≤ 1 := by
  rw [echo_probability]
  constructor <;> linarith [m.nonneg, m.atMostOne]

/-- Every executable example parameter lies in the physical range. -/
theorem registered_parameters_valid :
    (0 ≤ unitary.strength ∧ unitary.strength ≤ 1) ∧
    (0 ≤ collapse.strength ∧ collapse.strength ≤ 1) ∧
    (0 ≤ halfDephasing.strength ∧ halfDephasing.strength ≤ 1) := by
  norm_num [unitary, collapse, halfDephasing]

end OntologySeparation.Memory
