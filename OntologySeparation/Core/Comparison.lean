import OntologySeparation.Core.ExperimentAccess
import OntologySeparation.Core.Claim

/-! Proof-bearing comparison results with explicit model, semantics, and scope.

The core equivalence and separator notions remain in ExperimentAccess. This layer
packages them for reporting and distinguishes direct domain-wide agreement from
agreement on a supplied nonempty family. Promotion from a family to a broader
allowed domain requires an explicit coverage proof. -/
namespace OntologySeparation.Comparison

open ExperimentAccess
variable {P M : Type} {E : Interface}

/-- Agreement on a supplied family, together with evidence that the family is
not empty. This prevents a vacuous empty family from being presented as a
substantive checked family. -/
structure FamilyAgreement (predict : Predictions M P E) (family : P → Prop) (a b : M) where
  proof : Equivalent predict family a b
  protocol : P
  included : family protocol

/-- Evidence that every protocol in an allowed domain is represented by the
supplied family. Coverage is a proof obligation rather than renderer metadata. -/
structure Coverage (family allowed : P → Prop) where
  covers : ∀ p, allowed p → family p

/-- Agreement across the entire explicitly supplied allowed domain. -/
structure DomainAgreement (predict : Predictions M P E) (allowed : P → Prop) (a b : M) where
  proof : Equivalent predict allowed a b

/-- Upgrade family agreement only when coverage of the desired domain is proved. -/
def FamilyAgreement.promote
    {predict : Predictions M P E} {family allowed : P → Prop} {a b : M}
    (agreement : FamilyAgreement predict family a b)
    (coverage : Coverage family allowed) :
    DomainAgreement predict allowed a b :=
  ⟨agreement.proof.restrict coverage.covers⟩

/-- A reportable comparison is either agreement over the stated allowed domain
or a verified separator that itself satisfies the stated access predicate. -/
inductive Result (predict : Predictions M P E) (allowed : P → Prop) (a b : M)
  | agreement (certificate : DomainAgreement predict allowed a b)
  | separation (certificate : Separator predict allowed a b)

/-- The exact proposition exported for a comparison is derived from its constructor. -/
def Result.claim
    {predict : Predictions M P E} {allowed : P → Prop} {a b : M} :
    Result predict allowed a b → Claim
  | .agreement c => .agreement predict allowed a b c.proof
  | .separation w => .separation predict allowed a b w

theorem Result.sound
    {predict : Predictions M P E} {allowed : P → Prop} {a b : M}
    (r : Result predict allowed a b) : r.claim.statement := r.claim.sound

/-- The two reportable conclusions cannot both hold for the same models,
prediction semantics, and access domain. -/
theorem no_conflicting_results
    {predict : Predictions M P E} {allowed : P → Prop} {a b : M}
    (agreement : DomainAgreement predict allowed a b)
    (separation : Separator predict allowed a b) : False :=
  separation.not_equivalent agreement.proof

end OntologySeparation.Comparison
