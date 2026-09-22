import OntologySeparation.Study
import Mathlib.Tactic

/-! End-to-end certified partial-leakage showcase.

The exact point comparison and the continuous robustness theorem are exported as
different checked objects. The report must not present finite checking as proof
of the continuum or the continuum theorem as a claim about a broader ontology. -/
namespace PartialLeakageStudy

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite
open OntologySeparation.PartialLeakage

noncomputable section

def mechanism : Mechanism :=
  ⟨Rate.fraction 1 2, Rate.fraction 3 4⟩

def wigner : Law := mechanism.wignerLaw
def friend : Law := friendLaw

def recoveryFamily : ProtocolFamily Recipe :=
  ⟨coherenceProbe, []⟩

def pointResult :=
  certifyFamily exactBackend recoveryFamily wigner friend

def modelLabel (law : Law) : String :=
  if law.exposure.value = wigner.exposure.value then
    "Wigner/recovery model (v=1/2, r=3/4)"
  else
    "fully leaked friend law"

def settingLabel (_ : Unit) : String := "single setting"
def outcomeLabel (o : Bool) : String := if o then "+" else "-"

def pointReport : ComparisonReport :=
  CheckedResult.report exactBackend recoveryFamily wigner friend
    modelLabel Recipe.label settingLabel outcomeLabel pointResult

/-- Finite exact statement at the selected physical point. -/
def pointClaim : Claim := pointResult.claim

/-- Continuous statement over the physical parameter square. This is a theorem
claim, not a finite comparison result. -/
def robustnessClaim : Claim :=
  .theoremResult
    (∀ v r : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ r → r ≤ 1 →
      (0 < realGap v r ↔ 0 < v ∧ 0 < r))
    (by
      intro v r hv0 _ hr0 _
      exact realGap_positive_iff hv0 hr0)

example :
    probability wigner coherenceProbe - probability friend coherenceProbe = 3 / 16 := by
  norm_num [wigner, friend, mechanism, recovery_gap, Rate.fraction]

example : pointReport.claim.statement := pointResult.sound
example : robustnessClaim.statement := robustnessClaim.sound

end
end PartialLeakageStudy

#export_claim PartialLeakageStudy.pointClaim
#export_claim PartialLeakageStudy.robustnessClaim
#export_comparison PartialLeakageStudy.pointReport
