import OntologySeparation.Experiments.ReturnStatistics

namespace OntologySeparation.Tests.FiniteShot
open OntologySeparation.FiniteShot ReturnStatistics
noncomputable section

def planned := design 8 (1/100) (1/100)
example : planned.decision (fun _ => true) = .rejectNull := by decide
example : planned.decision (fun _ => false) = .inconclusive := by decide

example : ¬ ((337/625 + 1/5 : ℚ)^8 ≤ 1/100) := by norm_num

example (wrongLength : Outcomes 7) : True := by
  fail_if_success have bad := planned.decision wrongLength
  trivial

-- An adversarial memory example: a fair coin is copied into both outcomes.
-- Each marginal success rate is 1/2, but all-success probability is also 1/2,
-- rather than the IID value 1/4. It must fail the required history bound.
def correlated : Trials 2 where
  mass x := (point (fun _ => true)).mass x / 2 + (point (fun _ => false)).mass x / 2
  nonneg x := add_nonneg (div_nonneg ((point _).nonneg x) (by norm_num))
    (div_nonneg ((point _).nonneg x) (by norm_num))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    rw [FiniteDistribution.total, FiniteDistribution.total]
    norm_num

theorem correlated_prefix (k : ℕ) : prefixMass correlated k =
    prefixMass (point (fun _ : Fin 2 => true)) k / 2 +
      prefixMass (point (fun _ : Fin 2 => false)) k / 2 := by
  unfold prefixMass correlated
  simp only [add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib, Finset.sum_div]

theorem correlated_one : prefixMass correlated 1 = 1/2 := by
  rw [correlated_prefix, prefix_point, prefix_point]
  norm_num [survives, Fin.forall_fin_succ]

theorem correlated_two : prefixMass correlated 2 = 1/2 := by
  rw [correlated_prefix, prefix_point, prefix_point]
  norm_num [survives, Fin.forall_fin_succ]

example : ¬ NullBound correlated (1/2) := by
  intro h
  have hh := h 1 (by norm_num)
  rw [correlated_one, correlated_two] at hh
  norm_num at hh

-- Non-vacuity and zero-probability prefixes are included, without dividing by them.
example : NullBound (point (fun _ : Fin 8 => false)) 0 :=
  always_failure_null 8 0 le_rfl
end
end OntologySeparation.Tests.FiniteShot
