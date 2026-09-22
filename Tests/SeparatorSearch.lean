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

/-- Base calibration agrees; coherence search finds the reverse-oriented witness
because false is the first Boolean outcome. -/
example :
    searchTag (search exactBackend searchCalibration searchCoherence
      searchIdeal searchNoisy) = 4 := by
  generalize_proofs
  norm_num [searchTag, search, certifyFamily, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    certify, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchCalibration,
    searchCoherence, searchIdeal, searchNoisy, Law.dephasing, Rate.fraction,
    boolFinEnum]

/-- Reversing model order exercises the AB separator branch. -/
example :
    searchTag (search exactBackend searchCalibration searchCoherence
      searchNoisy searchIdeal) = 3 := by
  generalize_proofs
  norm_num [searchTag, search, certifyFamily, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    certify, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchCalibration,
    searchCoherence, searchIdeal, searchNoisy, Law.dephasing, Rate.fraction,
    boolFinEnum]

/-- Exhausting a candidate family that also agrees produces a checked negative
search result for that supplied family, not a global no-separator claim. -/
example :
    searchTag (search exactBackend searchCalibration searchCalibration
      searchIdeal searchNoisy) = 2 := by
  generalize_proofs
  norm_num [searchTag, search, certifyFamily, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    certify, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, searchCalibration, searchIdeal, searchNoisy,
    Law.dephasing, Rate.fraction, boolFinEnum]

/-- If the base family already separates, search reports that failed premise
rather than pretending an additional intervention was needed. -/
example :
    searchTag (search exactBackend searchCoherence searchCalibration
      searchIdeal searchNoisy) = 1 := by
  generalize_proofs
  norm_num [searchTag, search, certifyFamily, ProtocolFamily.grid,
    ProtocolFamily.entries, ProtocolFamily.protocols, entriesForProtocol,
    certify, scan, compareEntry, exactBackend, outcomeProbability,
    calibration_probability, coherence_probability, searchCalibration,
    searchCoherence, searchIdeal, searchNoisy, Law.dephasing, Rate.fraction,
    boolFinEnum]

