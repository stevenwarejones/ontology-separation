import OntologySeparation.Study

namespace PartialLeakageStudy

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite
open OntologySeparation.PartialLeakage

noncomputable section

/-- One exact point inside the proved continuous region. -/
def mechanism : Mechanism :=
  ⟨Rate.fraction 1 2, Rate.fraction 3 4⟩

def wigner : Law := mechanism.wignerLaw
def friend : Law := friendLaw

def calibrationFamily : ProtocolFamily Recipe := ⟨calibrationProbe, []⟩
def recoveryFamily : ProtocolFamily Recipe := ⟨coherenceProbe, []⟩

def calibrationResult :=
  certifyFamily exactBackend calibrationFamily wigner friend

def recoveryResult :=
  certifyFamily exactBackend recoveryFamily wigner friend

def settingLabel (_ : Unit) : String := "single setting"
def outcomeLabel (o : Bool) : String := if o then "+" else "-"

def calibrationReport : ComparisonReport :=
  CheckedResult.report exactBackend calibrationFamily wigner friend
    Law.label Recipe.label settingLabel outcomeLabel calibrationResult

def recoveryReport : ComparisonReport :=
  CheckedResult.report exactBackend recoveryFamily wigner friend
    Law.label Recipe.label settingLabel outcomeLabel recoveryResult

def visibilityClaim : Claim :=
  .exact (mechanism.visibility.value : ℝ) (1 / 2) (by
    norm_num [mechanism, Rate.fraction])

def recoveryEfficiencyClaim : Claim :=
  .exact (mechanism.recovery.value : ℝ) (3 / 4) (by
    norm_num [mechanism, Rate.fraction])

def pointGapClaim : Claim :=
  .exact
    ((probability wigner coherenceProbe - probability friend coherenceProbe : ℚ) : ℝ)
    (3 / 16) (by
      norm_num [wigner, friend, mechanism, recovery_gap, Rate.fraction])

/-- Symbolic theorem: every point with positive visibility and recovery has a
positive recovery-probe gap. This is not a finite scan. -/
def robustnessClaim : Claim :=
  .theoremResult
    (∀ v r : ℝ, 0 ≤ v → 0 ≤ r →
      (0 < realGap v r ↔ 0 < v ∧ 0 < r))
    (by
      intro v r hv hr
      exact realGap_positive_iff hv hr)

end
end PartialLeakageStudy

#export_claim PartialLeakageStudy.visibilityClaim
#export_claim PartialLeakageStudy.recoveryEfficiencyClaim
#export_claim PartialLeakageStudy.pointGapClaim
#export_claim PartialLeakageStudy.robustnessClaim
#export_comparison PartialLeakageStudy.calibrationReport
#export_comparison PartialLeakageStudy.recoveryReport
