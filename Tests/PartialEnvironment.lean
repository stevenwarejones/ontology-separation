import OntologySeparation.PartialEnvironment

namespace Tests.PartialEnvironment
noncomputable section
open OntologySeparation PartialEnvironment

def exampleLeakage : Leakage := ⟨3/5, 4/5, by norm_num, by norm_num⟩

example : test.prob (coherent exampleLeakage) true = 197/250 := by
  rw [coherent_probability]; norm_num [exampleLeakage]

example : (coherent exampleLeakage).normalizedTraceDistance (collapsed exampleLeakage) = 36/125 := by
  rw [distance_exact]; norm_num [exampleLeakage]

-- Exact boundary: no accessible quantum test clears the allowance criterion.
example {B : Type} [Fintype B] [DecidableEq B]
    (t : FiniteQuantum.Test Accessible B Bool) : ¬ Resolves exampleLeakage t (18/125) (18/125) := by
  apply no_test_resolves
  norm_num [exampleLeakage]

example : Resolves exampleLeakage test (1/20) (1/25) := by
  unfold Resolves
  rw [coherent_probability, collapsed_probability]; norm_num [exampleLeakage]

-- Full retained coherence and total hidden which-branch information endpoints.
example : (coherent (Leakage.ofOverlap 0 (by norm_num) (by norm_num))) =
    collapsed (Leakage.ofOverlap 0 (by norm_num) (by norm_num)) := by
  apply QIT.State.eq_of_normalizedTraceDistance_eq_zero
  rw [distance_exact]; norm_num [Leakage.ofOverlap]

example : QuantumDiscrimination.minimumError
    (coherent (Leakage.ofOverlap 1 (by norm_num) (by norm_num)))
    (collapsed (Leakage.ofOverlap 1 (by norm_num) (by norm_num))) = 13/50 := by
  rw [optimal_error]; norm_num [Leakage.ofOverlap]

-- The inaccessible register cannot be passed to an accessible test.
example : True := by
  fail_if_success
    have bad := test.prob (source exampleLeakage).state true
  trivial

-- The source rejects unnormalized amplitudes even if the overlap looks physical.
example : ¬ ((3/5 : ℝ)^2 + (3/5 : ℝ)^2 = 1) := by norm_num

end
end Tests.PartialEnvironment
