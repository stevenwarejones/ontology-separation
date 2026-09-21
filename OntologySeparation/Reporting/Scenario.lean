import OntologySeparation.Core.Scenario
import OntologySeparation.Reporting.Claim

open Lean Elab Command Meta
namespace OntologySeparation.ScenarioExport
open ClaimExport
private partial def entries (e : Expr) : MetaM (Array (String × Expr)) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then return #[]
  unless e.isAppOfArity ``List.cons 3 do
    throwError "Expected a reducible list of selected models or procedures"
  let args := e.getAppArgs
  let label ← stringValue (← mkAppM ``Prod.fst #[args[1]!])
  let value ← mkAppM ``Prod.snd #[args[1]!]
  return #[(label, value)] ++ (← entries args[2]!)
private def validateLabels (axis : String) (items : Array (String × Expr)) : MetaM Unit := do
  if items.isEmpty then throwError "A comparison needs at least one {axis}"
  let mut seen : Array String := #[]
  for (label, _) in items do
    if label.trimAscii.toString.isEmpty then throwError "Empty {axis} label"
    let normalized := label.trimAscii.toString
    if seen.contains normalized then throwError "Duplicate {axis} label: {label}"
    seen := seen.push normalized
/-- Project only checked rational data; never execute the real-valued interpretation. -/
-- Circuit expressions need more reduction depth than scalar recipes. Keep this
-- budget local to export, finite, and at least as large as an explicit user setting.
-- This only changes resource limits: proofs and the axiom whitelist are unchanged.
def comparisonJson (table : Expr) : MetaM Json :=
    withOptions (fun opts => maxRecDepth.set opts (max 4096 (maxRecDepth.get opts))) <|
    withTransparency .all do
  let title ← stringValue (← mkAppM ``Scenario.Comparison.title #[table])
  let description ← stringValue (← mkAppM ``Scenario.Comparison.description #[table])
  let models ← entries (← mkAppM ``Scenario.Comparison.models #[table])
  let protocols ← entries (← mkAppM ``Scenario.Comparison.protocols #[table])
  validateLabels "model" models
  validateLabels "procedure" protocols
  let predictions ← mkAppM ``Scenario.Comparison.predictions #[table]
  let mut rows : Array Json := #[]
  for (_, m) in models do
    let mut cells : Array Json := #[]
    for (_, p) in protocols do
      let claim ← mkAppM ``Scenario.ExactPredictions.claim #[predictions, m, p]
      cells := cells.push (← ClaimExport.claimJson claim)
    rows := rows.push (toJson cells)
  return Json.mkObj [
    ("schema", toJson "ontology-scenario-v2"), ("title", toJson title),
    ("description", toJson description), ("models", toJson (models.map Prod.fst)),
    ("protocols", toJson (protocols.map Prod.fst)), ("values", toJson rows)]
end OntologySeparation.ScenarioExport

/-- Publish only a checked Comparison; its cell proofs are audited transitively. -/
syntax (name := exportScenario) "#export_scenario " ident : command
elab_rules : command
  | `(#export_scenario $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo name
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Cannot publish scenario: unsupported proof dependency {ax}"
    let statement ← liftTermElabM <| withOptions (fun opts => opts.setBool `pp.fullNames true) do
      return (← ppExpr info.type).pretty
    let comparison ← liftTermElabM <| OntologySeparation.ScenarioExport.comparisonJson (mkConst name)
    let record := Json.mkObj [("declaration", toJson name.toString),
      ("type", toJson statement), ("comparison", comparison)]
    liftIO <| IO.println ("ONTOLOGY_SCENARIO " ++ record.compress)
