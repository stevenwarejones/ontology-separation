import OntologySeparation.Statistics

/-! A prospective design, not an analysis of laboratory observations.
Change the shot count or calibration allowance; infeasible significance fails.
Physical history/calibration premises are explained in docs/FINITE_SHOT_GUIDE.md. -/
namespace FiniteShotStudy
noncomputable section
open OntologySeparation

def planned := ReturnStatistics.design 8 (1/100) (1/100)
def risk := planned.riskClaim
def missedDetection := ReturnStatistics.powerClaim planned.shots (1/100)

#export_claim risk
#export_claim missedDetection
#export_theorem ReturnStatistics.calibrated_valid
#export_theorem FiniteShot.Plan.false_rejection_control
end
end FiniteShotStudy
