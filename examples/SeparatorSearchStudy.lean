import OntologySeparation.Study

namespace SeparatorSearchStudy
open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite
noncomputable section

def ideal : Law := Law.dephasing 0 1
def noisy : Law := Law.dephasing 1 2
def baseFamily : ProtocolFamily Recipe := ⟨calibrationProbe, []⟩
def candidates : ProtocolFamily Recipe := ⟨calibrationProbe, [coherenceProbe]⟩
def result := search exactBackend baseFamily candidates ideal noisy
def settingLabel (_ : Unit) : String := "single setting"
def outcomeLabel (o : Bool) : String := if o then "+" else "-"
def report : SearchReport :=
  SearchResult.report exactBackend baseFamily candidates ideal noisy
    Law.label Recipe.label settingLabel outcomeLabel result
end
end SeparatorSearchStudy

#export_search SeparatorSearchStudy.report
