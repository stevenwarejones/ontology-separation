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

example : physicalReport.claim.statement := reportResult.sound

end
