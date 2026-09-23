import OntologySeparation.Core.Claim

namespace OntologySeparation

/-- A whole-class upper bound and an attaining model share the *same* predicate,
observable, and value. An LP optimizer alone cannot inhabit this interface for a
physical model class: the physical witness and both proofs are required. -/
structure SharpOptimum {M : Type} (admissible : M → Prop) (score : M → ℝ) (value : ℝ) where
  upper : ∀ m, admissible m → score m ≤ value
  model : M
  satisfies : admissible model
  attains : score model = value

namespace SharpOptimum
variable {M : Type} {admissible : M → Prop} {score : M → ℝ} {value : ℝ}

theorem sound (s : SharpOptimum admissible score value) :
    (∀ m, admissible m → score m ≤ value) ∧
      ∃ m, admissible m ∧ score m = value :=
  ⟨s.upper, s.model, s.satisfies, s.attains⟩

/-- Reporting only needs an exact rational rendering, not another physical proof. -/
def boundClaim (s : SharpOptimum admissible score value) (q : ℚ) (hq : value = (q : ℝ)) : Claim :=
  .realizedBound admissible score q (by simpa [← hq] using s.upper) s.model s.satisfies

def witnessClaim (s : SharpOptimum admissible score value) (q : ℚ) (hq : value = (q : ℝ)) : Claim :=
  .witness admissible score s.model s.satisfies q (s.attains.trans hq)

end SharpOptimum
end OntologySeparation
