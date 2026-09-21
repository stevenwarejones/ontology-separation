import OntologySeparation.Core.Claim
import OntologySeparation.Catalog.Evidence

open OntologySeparation

-- Bound-only evidence can legitimately cover an empty class, without asserting existence.
def emptyBound : Claim := .bound (M := Empty) (fun _ => True) (fun _ => 0) 0
  (fun m => nomatch m)
example : emptyBound.kind = "bound" := rfl
example : emptyBound.statement := emptyBound.sound

example : (Catalog.noisyBellClaim ⟨1, by norm_num, by norm_num⟩).quantity = some (14/25) := by
  norm_num [Catalog.noisyBellClaim, Claim.quantity]
example : Catalog.lfBoundClaim.statement := Catalog.lfBoundClaim.sound
example : Catalog.bellLocalClaim.statement := Catalog.bellLocalClaim.sound
example : Catalog.localThreeClaim.statement := Catalog.localThreeClaim.sound
example : Catalog.nsLFClaim.statement := Catalog.nsLFClaim.sound
