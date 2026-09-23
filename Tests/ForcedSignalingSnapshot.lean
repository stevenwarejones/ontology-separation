import OntologySeparation.Certificates.ForcedSignaling
import Lean
open OntologySeparation.ForcedSignaling
-- Executable transcription check only. No theorem relies on this evaluation.
-- Stream rows so formatting does not construct one large nested JSON document.
#eval do
  IO.println <| Lean.Json.compress <| Lean.Json.mkObj [
    ("objective", Lean.toJson ((List.finRange 384).map objective)),
    ("normalization", Lean.toJson ((List.finRange 4).map fun k =>
      (List.finRange 384).map (normalization k))),
    ("support", Lean.toJson ((List.finRange 36).map fun k => (support k).val)),
    ("normalizationDual", Lean.toJson ((List.finRange 4).map normalizationDual))]
  for i in List.finRange 272 do
    IO.println <| Lean.Json.compress <| Lean.toJson (
      (List.finRange 384).map (constraint i))
