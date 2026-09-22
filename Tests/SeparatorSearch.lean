import OntologySeparation.Core.SeparatorSearch
import OntologySeparation.Reporting.Search
import OntologySeparation.Recipes.Separation
import Mathlib.Tactic

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.ExactFinite

noncomputable section

def searchIdeal : Law := Law.dephasing 0 1
def searchNoisy : Law := Law.dephasing 1 2
def searchCalibration : ProtocolFamily Recipe := ⟨calibrationProbe, []⟩
def searchCoherence : ProtocolFamily Recipe := ⟨coherenceProbe, []⟩

def searchTag {backend : ExactFinite.Backend RecipeSeparation.predict}
    {base candidates : ProtocolFamily Recipe} {a b : Law} :
    SearchResult backend base candidates a b → Nat
  | .baseSeparatesAB _ => 0
  | .baseSeparatesBA _ => 1
  | .noCandidate _ _ => 2
  | .foundAB _ _ => 3
  | .foundBA _ _ => 4

-- Reduce the finite grid explicitly, then check rational comparisons with
-- kernel-checked arithmetic; `decide` alone cannot reduce these search results.

/-- Base calibration agrees; coherence search finds the reverse-oriented witness
because false is the first Boolean outcome. -/
example :
    searchTag (search exactBackend searchCalibration searchCoherence
      searchIdeal searchNoisy) = 4 := by
  unfold search certifyFamily certify
  dsimp +instances [searchCalibration, searchCoherence, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    List.flatMap, List.map, List.append, List.flatten, List.finRange, List.dedup,
    List.ofFn, List.pwFilter, Fin.foldr, Fin.foldr.loop, List.get,
    FinEnum.toList, FinEnum.ofList, FinEnum.ofNodupList, FinEnum.punit, boolFinEnum]
  unfold scan
  norm_num [searchTag, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchIdeal, searchNoisy,
    Law.dephasing, Rate.fraction]

/-- Reversing model order exercises the AB separator branch. -/
example :
    searchTag (search exactBackend searchCalibration searchCoherence
      searchNoisy searchIdeal) = 3 := by
  unfold search certifyFamily certify
  dsimp +instances [searchCalibration, searchCoherence, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    List.flatMap, List.map, List.append, List.flatten, List.finRange, List.dedup,
    List.ofFn, List.pwFilter, Fin.foldr, Fin.foldr.loop, List.get,
    FinEnum.toList, FinEnum.ofList, FinEnum.ofNodupList, FinEnum.punit, boolFinEnum]
  unfold scan
  norm_num [searchTag, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchIdeal, searchNoisy,
    Law.dephasing, Rate.fraction]

/-- Exhausting a candidate family that also agrees produces a checked negative
search result for that supplied family, not a global no-separator claim. -/
example :
    searchTag (search exactBackend searchCalibration searchCalibration
      searchIdeal searchNoisy) = 2 := by
  unfold search certifyFamily certify
  dsimp +instances [searchCalibration, searchCoherence, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    List.flatMap, List.map, List.append, List.flatten, List.finRange, List.dedup,
    List.ofFn, List.pwFilter, Fin.foldr, Fin.foldr.loop, List.get,
    FinEnum.toList, FinEnum.ofList, FinEnum.ofNodupList, FinEnum.punit, boolFinEnum]
  unfold scan
  norm_num [searchTag, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchIdeal, searchNoisy,
    Law.dephasing, Rate.fraction]

/-- If the base family already separates, search reports that failed premise
rather than pretending an additional intervention was needed. -/
example :
    searchTag (search exactBackend searchCoherence searchCalibration
      searchIdeal searchNoisy) = 1 := by
  unfold search certifyFamily certify
  dsimp +instances [searchCalibration, searchCoherence, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    List.flatMap, List.map, List.append, List.flatten, List.finRange, List.dedup,
    List.ofFn, List.pwFilter, Fin.foldr, Fin.foldr.loop, List.get,
    FinEnum.toList, FinEnum.ofList, FinEnum.ofNodupList, FinEnum.punit, boolFinEnum]
  unfold scan
  norm_num [searchTag, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchIdeal, searchNoisy,
    Law.dephasing, Rate.fraction]

/-- Multi-candidate regression: the first candidate agrees, while the later
coherence protocol supplies the reverse-oriented separator. -/
def searchCandidates : ProtocolFamily Recipe :=
  ⟨calibrationProbe, [coherenceProbe]⟩

def multiSearch :=
  search exactBackend searchCalibration searchCandidates searchIdeal searchNoisy

def multiReport : SearchReport :=
  SearchResult.report exactBackend searchCalibration searchCandidates searchIdeal searchNoisy
    Law.label Recipe.label (fun _ => "single setting") (fun o => if o then "+" else "-")
    multiSearch

example : searchTag multiSearch = 4 := by
  unfold multiSearch
  unfold search certifyFamily certify
  dsimp +instances [searchCandidates, searchCalibration, searchCoherence, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    List.flatMap, List.map, List.append, List.flatten, List.finRange, List.dedup,
    List.ofFn, List.pwFilter, Fin.foldr, Fin.foldr.loop, List.get,
    FinEnum.toList, FinEnum.ofList, FinEnum.ofNodupList, FinEnum.punit, boolFinEnum]
  unfold scan
  norm_num [SearchResult.report, CheckedResult.report, ComparisonReport.protocol,
    ComparisonReport.gap, searchTag, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchIdeal, searchNoisy,
    Law.dephasing, Rate.fraction]

example :
    match multiReport.candidate with
    | some report =>
        report.protocol = some (Recipe.label coherenceProbe) ∧
        report.gap = some (1 / 4)
    | none => False := by
  unfold multiReport multiSearch
  unfold search certifyFamily certify
  dsimp +instances [searchCandidates, searchCalibration, searchCoherence, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    List.flatMap, List.map, List.append, List.flatten, List.finRange, List.dedup,
    List.ofFn, List.pwFilter, Fin.foldr, Fin.foldr.loop, List.get,
    FinEnum.toList, FinEnum.ofList, FinEnum.ofNodupList, FinEnum.punit, boolFinEnum]
  unfold scan
  norm_num [SearchResult.report, CheckedResult.report, ComparisonReport.protocol,
    ComparisonReport.gap, searchTag, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchIdeal, searchNoisy,
    Law.dephasing, Rate.fraction]
  constructor
  · rfl
  · change some (exactBackend.probability searchNoisy coherenceProbe () false -
      exactBackend.probability searchIdeal coherenceProbe () false) = some (1 / 4)
    norm_num [exactBackend, outcomeProbability, coherence_probability,
      searchIdeal, searchNoisy, Law.dephasing, Rate.fraction]
