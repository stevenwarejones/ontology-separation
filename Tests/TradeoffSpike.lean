import OntologySeparation.Certificates.ForcedSignaling

namespace OntologySeparation.TradeoffSpikeTests
open ForcedSignaling
open scoped BigOperators

-- A normalized satisfying model and its actual score, not an assumed witness.
example : pairing objective zeroBudget.weights = 6 := zeroBudget_score
example : pairing objective zeroBudget.weights ≤ 6 := by
  simpa using bound 0 zeroBudget

-- Removing a TV-budget row leaves an uncontrolled auxiliary column.
-- A changed certificate cannot be reused merely because its labels match.
example : ¬ (objective 296 ≤
    (∑ k : Fin 4, normalizationDual k * normalization k 296) +
      ∑ k : Fin 36, if support k = 261 then 0 else constraint (support k) 296) := by
  decide

-- Pointwise optimality is weaker than one protocol working for every model.
private def gap (protocol model : Bool) : ℚ := if protocol = model then 1 else 0
example : ∀ model, ∃ protocol, gap protocol model = 1 := by
  intro model
  exact ⟨model, by simp [gap]⟩
example : ¬ ∃ protocol, ∀ model, 0 < gap protocol model := by
  rintro ⟨protocol, h⟩
  have hh := h (!protocol)
  cases protocol <;> norm_num [gap] at hh

-- Merely attaching the valid certificate does not prove a stronger intercept.
example : True := by
  fail_if_success
    have bad : pairing objective zeroBudget.weights ≤ 5 := by
      simpa using bound 0 zeroBudget
  trivial
end OntologySeparation.TradeoffSpikeTests
