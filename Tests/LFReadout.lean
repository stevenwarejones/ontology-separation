import OntologySeparation.Assumptions

namespace OntologySeparation.Tests.LFReadout
open OntologySeparation.LFReadout
open LFJoint (Table)
noncomputable section

example (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    withinBudget t (sharpTable t h0 h1) := sharpTable_within t h0 h1

example : RealQuantum.genuineLF (sharpTable (1/8) (by norm_num) (by norm_num)).behavior = 13/2 := by
  rw [sharpTable_score]
  norm_num

example : ¬ RealQuantum.genuineLF (sharpTable (1/8) (by norm_num) (by norm_num)).behavior ≤ 6 := by
  rw [sharpTable_score]
  norm_num

example : ¬ budgetTheory (1/8) RealQuantum.lfBehavior := quantum_excluded _ (by norm_num)

-- A budget above the exclusion threshold admits a score above the quantum target.
-- This is not a witness that the target's full probability table belongs to the class.
example : ∃ j : Table, withinBudget (1/4) j ∧
    RealQuantum.genuineLF RealQuantum.lfBehavior < RealQuantum.genuineLF j.behavior := by
  refine ⟨sharpTable (1/4) (by norm_num) (by norm_num), sharpTable_within _ _ _, ?_⟩
  rw [sharpTable_score, RealQuantum.lfBehavior_value]
  norm_num

-- Zero and unit budgets are genuine endpoints, not limits silently omitted.
example : mismatchA (sharpTable 0 (by norm_num) (by norm_num)) = 0 := by
  rw [sharpTable_mismatchA]; norm_num
example : RealQuantum.genuineLF (sharpTable 1 (by norm_num) (by norm_num)).behavior = 10 := by
  rw [sharpTable_score]; norm_num

example : True := by
  fail_if_success
    have h : (1/4 : ℚ) < 65453 / 361250 := by norm_num
  trivial

example : Claim.quantity (budgetClaim (1/8) (by norm_num) (by norm_num)) = some (13/2) := by
  norm_num [budgetClaim, Claim.quantity]
example : Claim.kind (budgetClaim (1/8) (by norm_num) (by norm_num)) = "realizedBound" := rfl

end
end OntologySeparation.Tests.LFReadout
