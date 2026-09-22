import OntologySeparation.Core.Comparison
import Mathlib.Tactic.NormNum

open OntologySeparation
open ExperimentAccess
open Comparison

abbrev ComparisonTestInterface : Interface := { Setting := Unit, Outcome := Bool }

def bitBehavior (bit : Bool) : Behavior ComparisonTestInterface where
  prob _ o := if o = bit then 1 else 0
  nonneg _ o := by split_ifs <;> norm_num
  normalized _ := by cases bit <;> norm_num [ComparisonTestInterface, Fintype.sum_bool]

def bitPredict (model : Bool) (_ : Unit) : Behavior ComparisonTestInterface := bitBehavior model

def sameFamily : FamilyAgreement bitPredict (fun _ => True) false false where
  proof := Equivalent.refl bitPredict (fun _ => True) false
  protocol := ()
  included := trivial

def fullCoverage : Coverage (fun _ : Unit => True) (fun _ => True) where
  covers := by intro _ _; trivial

def sameDomain : DomainAgreement bitPredict (fun _ => True) false false :=
  sameFamily.promote fullCoverage

def different : Separator bitPredict (fun _ => True) false true where
  protocol := ()
  accessible := trivial
  setting := ()
  outcome := false
  gap := 1
  positive := by norm_num
  difference := by norm_num [bitPredict, bitBehavior]

def agreementResult : Result bitPredict (fun _ => True) false false :=
  .agreement sameDomain

def separationResult : Result bitPredict (fun _ => True) false true :=
  .separation different

example : agreementResult.claim.kind = "agreement" := rfl
example : separationResult.claim.kind = "separation" := rfl
example : agreementResult.claim.statement := agreementResult.sound
example : separationResult.claim.statement := separationResult.sound

-- A supplied-family agreement cannot be constructed for an empty protocol type:
-- the certificate itself must contain one included protocol.
example (predict : Predictions Bool Empty ComparisonTestInterface) (a b : Bool)
    (h : FamilyAgreement predict (fun _ => False) a b) : False :=
  nomatch h.protocol

-- Agreement and separation over the exact same models/semantics/access cannot coexist.
example (h : DomainAgreement bitPredict (fun _ => True) false true) : False :=
  no_conflicting_results h different
