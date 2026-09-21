import OntologySeparation.Experiments.ModelCompatibility
import OntologySeparation.Reporting.Claim

/-! An end-to-end example, including a new adopter-defined model. -/
namespace MyModelClassStudy
open OntologySeparation FiniteModels ModelCompatibility
noncomputable section

-- Change this to another rational in [0,1]. All four entries are checked.
def weights : FiniteDistribution Bool where
  mass bit := if bit then 1/3 else 2/3
  nonneg bit := by cases bit <;> norm_num
  total := by norm_num [Fintype.sum_bool]

-- Define a target independently so a mismatch cannot hide in the constructor.
def target : Behavior interface where
  prob _ bit := if bit then 1/3 else 2/3
  nonneg _ bit := by cases bit <;> norm_num
  normalized _ := by
    change (∑ b : Bool, if b then (1/3 : ℝ) else 2/3) = 1
    norm_num [Fintype.sum_bool]

def certificate : Membership fixed target where
  weights := weights
  reproduces s o := by cases o <;> norm_num [mixture, weights, fixed, target, Fintype.sum_bool]

def compatibleClaim : Claim := .theoremResult (Compatible fixed target) certificate.compatible
end
end MyModelClassStudy

#export_claim MyModelClassStudy.compatibleClaim
#export_claim OntologySeparation.ModelCompatibility.fairClaim
#export_claim OntologySeparation.ModelCompatibility.echoClaim
#export_theorem OntologySeparation.ModelCompatibility.passes_one_bound_but_excluded
#export_claim OntologySeparation.ModelCompatibility.recordClassClaim

#export_claim OntologySeparation.ModelCompatibility.recordBoundClaim
