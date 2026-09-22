import OntologySeparation.Core.SeparatorSearch
import OntologySeparation.Reporting.Comparison
import Lean

/-! Proof-linked publication adapter for finite separator search. -/
namespace OntologySeparation.ExactFinite

variable {P M : Type} {E : Interface} {predict : ExperimentAccess.Predictions M P E}
  [FinEnum E.Setting] [FinEnum E.Outcome]

structure SearchReport where
  status : String
  base : ComparisonReport
  candidate : Option ComparisonReport

def SearchResult.report (backend : Backend predict) (base candidates : ProtocolFamily P)
    (a b : M) (modelLabel : M → String) (protocolLabel : P → String)
    (settingLabel : E.Setting → String) (outcomeLabel : E.Outcome → String)
    (result : SearchResult backend base candidates a b) : SearchReport :=
  match result with
  | .baseSeparatesAB certificate =>
      { status := "base-separates"
        base := CheckedResult.report backend base a b modelLabel protocolLabel
          settingLabel outcomeLabel (.separatesAB certificate)
        candidate := none }
  | .baseSeparatesBA certificate =>
      { status := "base-separates"
        base := CheckedResult.report backend base a b modelLabel protocolLabel
          settingLabel outcomeLabel (.separatesBA certificate)
        candidate := none }
  | .noCandidate baseAgreement candidateAgreement =>
      { status := "no-candidate"
        base := CheckedResult.report backend base a b modelLabel protocolLabel
          settingLabel outcomeLabel (.agreement baseAgreement)
        candidate := some (CheckedResult.report backend candidates a b modelLabel protocolLabel
          settingLabel outcomeLabel (.agreement candidateAgreement)) }
  | .foundAB baseAgreement certificate =>
      { status := "found"
        base := CheckedResult.report backend base a b modelLabel protocolLabel
          settingLabel outcomeLabel (.agreement baseAgreement)
        candidate := some (CheckedResult.report backend candidates a b modelLabel protocolLabel
          settingLabel outcomeLabel (.separatesAB certificate)) }
  | .foundBA baseAgreement certificate =>
      { status := "found"
        base := CheckedResult.report backend base a b modelLabel protocolLabel
          settingLabel outcomeLabel (.agreement baseAgreement)
        candidate := some (CheckedResult.report backend candidates a b modelLabel protocolLabel
          settingLabel outcomeLabel (.separatesBA certificate)) }

end OntologySeparation.ExactFinite

open Lean Elab Command Meta
namespace OntologySeparation.SearchReportExport

private def optionComparisonJson (e : Expr) : MetaM Json := do
  let e ← whnf e
  if e.isAppOfArity ``Option.none 1 then return Json.null
  unless e.isAppOfArity ``Option.some 2 do
    throwError "Expected a reducible optional candidate comparison"
  ComparisonReportExport.reportJson e.getAppArgs[1]!

def reportJson (report : Expr) : MetaM Json := withTransparency .all do
  let status ← ClaimExport.stringValue (← mkAppM ``ExactFinite.SearchReport.status #[report])
  let base ← ComparisonReportExport.reportJson
    (← mkAppM ``ExactFinite.SearchReport.base #[report])
  let candidate ← optionComparisonJson
    (← mkAppM ``ExactFinite.SearchReport.candidate #[report])
  return Json.mkObj [("status", toJson status), ("base", base), ("candidate", candidate)]

end OntologySeparation.SearchReportExport

syntax (name := exportSearch) "#export_search " ident : command
elab_rules : command
  | `(#export_search $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo name
    unless ← liftTermElabM (isDefEq info.type
      (mkConst ``OntologySeparation.ExactFinite.SearchReport)) do
      throwError "Expected a structured SearchReport"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Cannot publish search: unsupported proof dependency {ax}"
    let report ← liftTermElabM <|
      OntologySeparation.SearchReportExport.reportJson (mkConst name)
    liftIO <| IO.println ("ONTOLOGY_SEARCH " ++ (Json.mkObj [
      ("declaration", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString)),
      ("report", report)]).compress)
