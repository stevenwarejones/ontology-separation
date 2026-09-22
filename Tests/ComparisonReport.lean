import OntologySeparation.Reporting.Comparison
import OntologySeparation.Recipes.Separation

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite

noncomputable section

def reportIdeal : Law := Law.dephasing 0 1
def reportNoisy : Law := Law.dephasing 1 2
def reportFamily : ProtocolFamily Recipe := ⟨coherenceProbe, []⟩
def reportResult := certifyFamily exactBackend reportFamily reportIdeal reportNoisy

def reportSetting (_ : Unit) : String := "single setting"
def reportOutcome (o : Bool) : String := if o then "+" else "-"

def physicalReport : ComparisonReport :=
  CheckedResult.report exactBackend reportFamily reportIdeal reportNoisy
    Law.label Recipe.label reportSetting reportOutcome reportResult

example : physicalReport.claim.statement := by
  change reportResult.claim.statement
  exact reportResult.sound

-- Presentation fields are derived getters, not editable record inputs.
example : True := by
  fail_if_success
    have forged : ComparisonReport := { physicalReport with gap := some 1 }
  fail_if_success
    have forged : ComparisonReport := { physicalReport with leftProbability := some 1 }
  fail_if_success
    have forged : ComparisonReport := { physicalReport with verdict := "agreement" }
  fail_if_success
    have forged : ComparisonReport := { physicalReport with coveredProtocols := ["all experiments"] }
  trivial

end
