import OntologySeparation.Assumptions

namespace LFReadoutStudy
open OntologySeparation
noncomputable section

/-- Maximum total disagreement probability allowed by this study. Edit this one value. -/
def budget : ℚ := 1 / 8

-- Both the reported ceiling and its attaining witness derive from budget.
def ceiling : Claim := LFReadout.budgetClaim budget
  (by norm_num [budget]) (by norm_num [budget])

def attainingModel : Claim := LFReadout.attainingClaim budget
  (by norm_num [budget]) (by norm_num [budget])

-- Raising the budget too far invalidates this proof: no stale exclusion survives.
def quantumExclusion : Claim := LFReadout.exclusionClaim budget (by norm_num [budget])

#export_claim ceiling
#export_claim attainingModel
#export_claim quantumExclusion
#export_theorem OntologySeparation.LFReadout.sharp_total_budget
#export_theorem OntologySeparation.LFReadout.required_mismatch

end
end LFReadoutStudy
