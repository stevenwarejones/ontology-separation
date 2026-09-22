import OntologySeparation.Core.AutomaticGrid
import OntologySeparation.Reporting.Claim
import Lean

/-! Structured, proof-linked presentation data for exact finite comparisons.

The mathematical verdict remains the existing Claim. Human-facing model names,
covered protocols, witness coordinates, exact probabilities and gap are derived
from the same checked result rather than maintained as a parallel result string. -/
namespace OntologySeparation.ExactFinite

variable {P M : Type} {E : Interface} {predict : ExperimentAccess.Predictions M P E}

structure ComparisonReport where
  leftModel : String
  rightModel : String
  coveredProtocols : List String
  verdict : String
  protocol : Option String := none
  setting : Option String := none
  outcome : Option String := none
  leftProbability : Option ℚ := none
  rightProbability : Option ℚ := none
  gap : Option ℚ := none
  claim : Claim

/-- Derive presentation data from the checked result. Reverse separators swap
model order and probabilities to match the separator actually proved. -/
def CheckedResult.report (backend : Backend predict) (family : ProtocolFamily P)
    (a b : M) (modelLabel : M → String) (protocolLabel : P → String)
    (settingLabel : E.Setting → String) (outcomeLabel : E.Outcome → String)
    (result : CheckedResult backend family.allowed a b) : ComparisonReport :=
  match result with
  | .agreement _ =>
      { leftModel := modelLabel a
        rightModel := modelLabel b
        coveredProtocols := family.protocols.map protocolLabel
        verdict := "agreement"
        claim := result.claim }
  | .separatesAB certificate =>
      let pa := backend.probability a certificate.protocol certificate.setting certificate.outcome
      let pb := backend.probability b certificate.protocol certificate.setting certificate.outcome
      { leftModel := modelLabel a
        rightModel := modelLabel b
        coveredProtocols := family.protocols.map protocolLabel
        verdict := "separation"
        protocol := some (protocolLabel certificate.protocol)
        setting := some (settingLabel certificate.setting)
        outcome := some (outcomeLabel certificate.outcome)
        leftProbability := some pa
        rightProbability := some pb
        gap := some (pa - pb)
        claim := result.claim }
  | .separatesBA certificate =>
      let pb := backend.probability b certificate.protocol certificate.setting certificate.outcome
      let pa := backend.probability a certificate.protocol certificate.setting certificate.outcome
      { leftModel := modelLabel b
        rightModel := modelLabel a
        coveredProtocols := family.protocols.map protocolLabel
        verdict := "separation"
        protocol := some (protocolLabel certificate.protocol)
        setting := some (settingLabel certificate.setting)
        outcome := some (outcomeLabel certificate.outcome)
        leftProbability := some pb
        rightProbability := some pa
        gap := some (pb - pa)
        claim := result.claim }

end OntologySeparation.ExactFinite

open Lean Elab Command Meta
namespace OntologySeparation.ComparisonReportExport

private partial def stringList (e : Expr) : MetaM (List String) := do
  let e ← whnf e
  if e.isAppOf \`\`List.nil then return []
  unless e.isAppOfArity \`\`List.cons 3 do
    throwError "Expected a reducible list of comparison labels"
  let args := e.getAppArgs
  let head ← ClaimExport.stringValue args[1]!
  return head :: (← stringList args[2]!)

private def optionString (e : Expr) : MetaM Json := do
  let e ← whnf e
  if e.isAppOfArity \`\`Option.none 1 then return Json.null
  unless e.isAppOfArity \`\`Option.some 2 do
    throwError "Expected a reducible optional comparison label"
  return toJson (← ClaimExport.stringValue e.getAppArgs[1]!)

private def optionRat (e : Expr) : MetaM Json := do
  let e ← whnf e
  if e.isAppOfArity \`\`Option.none 1 then return Json.null
  unless e.isAppOfArity \`\`Option.some 2 do
    throwError "Expected a reducible optional exact probability"
  ClaimExport.rationalJson e.getAppArgs[1]!

def reportJson (report : Expr) : MetaM Json := withTransparency .all do
  let left ← ClaimExport.stringValue (← mkAppM \`\`ExactFinite.ComparisonReport.leftModel #[report])
  let right ← ClaimExport.stringValue (← mkAppM \`\`ExactFinite.ComparisonReport.rightModel #[report])
  let protocols ← stringList (← mkAppM \`\`ExactFinite.ComparisonReport.coveredProtocols #[report])
  let verdict ← ClaimExport.stringValue (← mkAppM \`\`ExactFinite.ComparisonReport.verdict #[report])
  let protocol ← optionString (← mkAppM \`\`ExactFinite.ComparisonReport.protocol #[report])
  let setting ← optionString (← mkAppM \`\`ExactFinite.ComparisonReport.setting #[report])
  let outcome ← optionString (← mkAppM \`\`ExactFinite.ComparisonReport.outcome #[report])
  let leftP ← optionRat (← mkAppM \`\`ExactFinite.ComparisonReport.leftProbability #[report])
  let rightP ← optionRat (← mkAppM \`\`ExactFinite.ComparisonReport.rightProbability #[report])
  let gap ← optionRat (← mkAppM \`\`ExactFinite.ComparisonReport.gap #[report])
  let claimExpr ← mkAppM \`\`ExactFinite.ComparisonReport.claim #[report]
  let claim ← ClaimExport.claimJson claimExpr
  return Json.mkObj [
    ("left_model", toJson left), ("right_model", toJson right),
    ("covered_protocols", toJson protocols), ("verdict", toJson verdict),
    ("protocol", protocol), ("setting", setting), ("outcome", outcome),
    ("left_probability", leftP), ("right_probability", rightP), ("gap", gap),
    ("claim", claim)]

end OntologySeparation.ComparisonReportExport

syntax (name := exportComparison) "#export_comparison " ident : command
elab_rules : command
  | \`(#export_comparison $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo name
    unless ← liftTermElabM (isDefEq info.type (mkConst \`\`OntologySeparation.ExactFinite.ComparisonReport)) do
      throwError "Expected a structured ComparisonReport"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[\`propext, \`Classical.choice, \`Quot.sound].contains ax do
        throwError "Cannot publish comparison: unsupported proof dependency {ax}"
    let report ← liftTermElabM <|
      OntologySeparation.ComparisonReportExport.reportJson (mkConst name)
    liftIO <| IO.println ("ONTOLOGY_COMPARISON " ++ (Json.mkObj [
      ("declaration", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString)),
      ("report", report)]).compress)
