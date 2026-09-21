import OntologySeparation.Core.Claim
import Lean

open Lean Elab Command Meta
namespace OntologySeparation.ClaimExport
private partial def characters (e : Expr) : MetaM (List Char) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then return []
  unless e.isAppOfArity ``List.cons 3 do
    throwError "Expected reducible characters in a generated label"
  let args := e.getAppArgs
  let some code ← getNatValue? (← whnf (← mkAppM ``Char.toNat #[args[1]!]))
    | throwError "Expected a reducible character in a generated label"
  return Char.ofNat code :: (← characters args[2]!)
def stringValue (e : Expr) : MetaM String := do
  if let some s := getStringValue? (← whnf e) then return s
  return String.ofList (← characters (← mkAppM ``String.toList #[e]))
def rationalJson (value : Expr) : MetaM Json := do
  let num ← whnf (← mkAppM ``Rat.num #[value])
  let numerator ← if num.isAppOfArity ``Int.ofNat 1 then do
      let some n ← getNatValue? (← whnf num.getAppArgs[0]!)
        | throwError "Expected a reducible integer numerator"
      pure (Int.ofNat n)
    else if num.isAppOfArity ``Int.negSucc 1 then do
      let some n ← getNatValue? (← whnf num.getAppArgs[0]!)
        | throwError "Expected a reducible integer numerator"
      pure (Int.negSucc n)
    else throwError "Expected a reducible integer numerator"
  let some denominator ← getNatValue? (← whnf (← mkAppM ``Rat.den #[value]))
    | throwError "Expected a reducible denominator"
  return Json.mkObj [("numerator", toJson (toString numerator)),
    ("denominator", toJson (toString denominator))]

/-- Kernel reduction for data, actual proposition for evidence; no evaluation of real semantics. -/
def claimJson (claim : Expr) : MetaM Json := withTransparency .all do
  let kind ← stringValue (← mkAppM ``Claim.kind #[claim])
  let value ← whnf (← mkAppM ``Claim.quantity #[claim])
  let quantity ← if value.isAppOfArity ``Option.some 2 then
      rationalJson value.getAppArgs[1]!
    else pure Json.null
  let prop ← whnf (← mkAppM ``Claim.statement #[claim])
  let statement ← withOptions (fun o => o.setBool `pp.fullNames true) do
    return (← ppExpr prop).pretty
  return Json.mkObj [("kind", toJson kind), ("quantity", quantity), ("statement", toJson statement)]
end OntologySeparation.ClaimExport

syntax (name := exportClaim) "#export_claim " ident : command
elab_rules : command
  | `(#export_claim $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo name
    unless ← liftTermElabM (isDefEq info.type (mkConst ``OntologySeparation.Claim)) do
      throwError "Expected a proof-bearing Claim"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Cannot publish claim: unsupported proof dependency {ax}"
    let claim ← liftTermElabM <| OntologySeparation.ClaimExport.claimJson (mkConst name)
    liftIO <| IO.println ("ONTOLOGY_CLAIM " ++ (Json.mkObj [
      ("declaration", toJson name.toString), ("axioms", toJson (axioms.map Name.toString)), ("claim", claim)]).compress)

/-- Convenience syntax for a general theorem, using the same claim exporter. -/
syntax (name := exportTheorem) "#export_theorem " ident : command
elab_rules : command
  | `(#export_theorem $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo name
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a proved theorem"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Cannot publish theorem: unsupported proof dependency {ax}"
    let claim ← liftTermElabM do
      let term ← mkAppM ``OntologySeparation.Claim.theoremResult #[info.type, mkConst name (info.levelParams.map Level.param)]
      OntologySeparation.ClaimExport.claimJson term
    liftIO <| IO.println ("ONTOLOGY_CLAIM " ++ (Json.mkObj [
      ("declaration", toJson name.toString), ("axioms", toJson (axioms.map Name.toString)),
      ("claim", claim)]).compress)
