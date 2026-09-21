import OntologySeparation.Core.Scenario
import OntologySeparation.Reporting.Export

open Lean Elab Command Meta
namespace OntologySeparation.ScenarioExport
private partial def characters (e : Expr) : MetaM (List Char) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then return []
  unless e.isAppOfArity ``List.cons 3 do
    throwError "Expected reducible characters in a generated label"
  let args := e.getAppArgs
  let some code ← getNatValue? (← whnf (← mkAppM ``Char.toNat #[args[1]!]))
    | throwError "Expected a reducible character in a generated label"
  return Char.ofNat code :: (← characters args[2]!)
private def stringValue (e : Expr) : MetaM String := do
  if let some s := getStringValue? (← whnf e) then return s
  return String.ofList (← characters (← mkAppM ``String.toList #[e]))
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
def comparisonJson (table : Expr) : MetaM Json := withTransparency .all do
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
      let value ← mkAppM ``Scenario.ExactPredictions.value #[predictions, m, p]
      let num ← whnf (← mkAppM ``Rat.num #[value])
      let numerator ← if num.isAppOfArity ``Int.ofNat 1 then do
          let some n ← getNatValue? (← whnf num.getAppArgs[0]!)
            | throwError "Expected a reducible integer numerator"
          pure (Int.ofNat n)
        else if num.isAppOfArity ``Int.negSucc 1 then do
          let some n ← getNatValue? (← whnf num.getAppArgs[0]!)
            | throwError "Expected a reducible integer numerator"
          pure (Int.negSucc n)
        else throwError "Expected a reducible integer numerator, got {num}"
      let some denominator ← getNatValue? (← whnf (← mkAppM ``Rat.den #[value]))
        | throwError "Expected a reducible natural denominator"
      cells := cells.push (Json.mkObj [
        ("numerator", toJson (toString numerator)),
        ("denominator", toJson (toString denominator))])
    rows := rows.push (toJson cells)
  return Json.mkObj [
    ("schema", toJson "ontology-scenario-v1"), ("title", toJson title),
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
