import Lean

/-! Export actual kernel-checked theorem types. Generated JSON remains a snapshot;
recheck trusted Lean source rather than trusting editable report labels. -/
open Lean Elab Command Meta
syntax (name := exportTheorem) "#export_theorem " ident : command
elab_rules : command
  | `(#export_theorem $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let info ← getConstInfo name
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a proved theorem, not a model name, description, or definition"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Cannot publish theorem: unsupported proof dependency {ax}"
    let statement ← liftTermElabM <| withOptions (fun opts => opts.setBool `pp.fullNames true) do
      return (← ppExpr info.type).pretty
    let record := Json.mkObj [
      ("declaration", toJson name.toString), ("statement", toJson statement),
      ("axioms", toJson (axioms.map Name.toString)), ("kind", toJson "theorem")]
    liftIO <| IO.println ("ONTOLOGY_THEOREM " ++ record.compress)
