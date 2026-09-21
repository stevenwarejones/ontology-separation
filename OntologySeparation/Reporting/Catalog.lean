import OntologySeparation.Catalog.Matrix
import OntologySeparation.Reporting.Claim

open Lean Elab Command Meta
namespace OntologySeparation.CatalogExport
open ClaimExport
partial def listItems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then return #[]
  unless e.isAppOfArity ``List.cons 3 do throwError "Expected a reducible list"
  return #[e.getAppArgs[1]!] ++ (← listItems e.getAppArgs[2]!)
def stringField (name : Name) (e : Expr) : MetaM Json := return toJson (← stringValue (← mkAppM name #[e]))
def stringList (e : Expr) : MetaM Json := do
  return toJson (← (← listItems e).mapM stringValue)
def cellsJson (table : Expr) : MetaM Json := withTransparency .all do
  let mut cells := #[]
  for cell in ← listItems table do
    let proof ← whnf (← mkAppM ``Catalog.Cell.claim #[cell])
    let claim ← if proof.isAppOfArity ``Option.some 2 then claimJson proof.getAppArgs[1]! else pure Json.null
    let applicability ← whnf (← mkAppM ``Catalog.Cell.applicability #[cell])
    let scope := if applicability.isConstOf ``Catalog.Applicability.native then "native" else "additional"
    cells := cells.push (Json.mkObj [
      ("scenario", ← stringField ``Catalog.Cell.scenario cell),
      ("model", ← stringField ``Catalog.Cell.model cell),
      ("applicability", toJson scope), ("claim", claim),
      ("supporting", toJson (← (← listItems (← mkAppM ``Catalog.Cell.supporting #[cell])).mapM claimJson)),
      ("assumptions", ← stringList (← mkAppM ``Catalog.Cell.assumptions #[cell])),
      ("limitation", ← stringField ``Catalog.Cell.limitation cell)])
  return toJson cells

def extensionsJson : MetaM Json := withTransparency .all do
  let mut rows := #[]
  for e in ← listItems (mkConst ``Catalog.extensions) do
    rows := rows.push (Json.mkObj [
      ("scenario", ← stringField ``Catalog.ExtensionInfo.scenario e),
      ("title", ← stringField ``Catalog.ExtensionInfo.title e),
      ("requiredLaw", ← stringField ``Catalog.ExtensionInfo.requiredLaw e),
      ("supporting", toJson (← (← listItems (← mkAppM ``Catalog.ExtensionInfo.supporting #[e])).mapM claimJson)),
      ("scope", ← stringField ``Catalog.ExtensionInfo.scope e),
      ("claim", ← claimJson (← mkAppM ``Catalog.ExtensionInfo.claim #[e]))])
  return toJson rows
end OntologySeparation.CatalogExport

/-- The entire catalog and all extension claims are audited before anything is emitted. -/
syntax (name := exportCatalog) "#export_catalog" : command
elab_rules : command
  | `(#export_catalog) => do
    for name in #[``OntologySeparation.Catalog.matrix, ``OntologySeparation.Catalog.extensions] do
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Cannot publish catalog: unsupported proof dependency {ax}"
    let cells ← liftTermElabM <| OntologySeparation.CatalogExport.cellsJson (mkConst ``OntologySeparation.Catalog.matrix)
    let extensions ← liftTermElabM OntologySeparation.CatalogExport.extensionsJson
    let report := Json.mkObj [
      ("schema_version", toJson (3 : Nat)),
      ("scenarios", toJson OntologySeparation.Catalog.scenarios),
      ("models", toJson OntologySeparation.Catalog.models),
      ("cells", cells), ("extensions", extensions),
      ("binary_profiles", toJson OntologySeparation.binaryProfiles),
      ("profile_notice", toJson "Sixteen expressible profiles; physical realizability requires a vocabulary and a satisfying model.")]
    liftIO <| IO.println ("ONTOLOGY_CATALOG " ++ report.compress)
