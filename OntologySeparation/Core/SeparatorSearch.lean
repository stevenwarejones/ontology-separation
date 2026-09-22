import OntologySeparation.Core.AutomaticGrid

/-! Exact search for an additional separating protocol after a checked base family.

The search is deliberately finite and ordered. It first certifies the base
family. Only if the base agrees does it scan the explicitly supplied candidate
family and return either a proof-bearing separator or proof that the supplied
candidate family also agrees. -/
namespace OntologySeparation.ExactFinite

open ExperimentAccess
open Comparison

variable {P M : Type} {E : Interface} {predict : Predictions M P E}
  [FinEnum E.Setting] [FinEnum E.Outcome]

/-- Proof-bearing result of searching an explicitly supplied candidate family.

The found constructors mean the base family agrees and the candidate family
contains a checked separator. The no-candidate constructor means every protocol
in both supplied finite families agrees. The base-separates constructors record
that the premise of indistinguishability under base access was already false. -/
inductive SearchResult (backend : Backend predict)
    (base candidates : ProtocolFamily P) (a b : M)
  | baseSeparatesAB
      (certificate : Separator predict base.allowed a b)
  | baseSeparatesBA
      (certificate : Separator predict base.allowed b a)
  | noCandidate
      (baseAgreement : FamilyAgreement predict base.allowed a b)
      (candidateAgreement : FamilyAgreement predict candidates.allowed a b)
  | foundAB
      (baseAgreement : FamilyAgreement predict base.allowed a b)
      (certificate : Separator predict candidates.allowed a b)
  | foundBA
      (baseAgreement : FamilyAgreement predict base.allowed a b)
      (certificate : Separator predict candidates.allowed b a)

/-- Search the finite candidate family only after certifying agreement on the
finite base family. Traversal order determines which valid separator is returned
first; it does not alter any proof. -/
def search (backend : Backend predict) (base candidates : ProtocolFamily P)
    (a b : M) : SearchResult backend base candidates a b :=
  match certifyFamily backend base a b with
  | .separatesAB certificate => .baseSeparatesAB certificate
  | .separatesBA certificate => .baseSeparatesBA certificate
  | .agreement baseAgreement =>
      match certifyFamily backend candidates a b with
      | .agreement candidateAgreement =>
          .noCandidate baseAgreement candidateAgreement
      | .separatesAB certificate =>
          .foundAB baseAgreement certificate
      | .separatesBA certificate =>
          .foundBA baseAgreement certificate

end OntologySeparation.ExactFinite
