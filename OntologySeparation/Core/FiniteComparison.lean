import OntologySeparation.Core.Comparison

/-! Exact automatic comparison over finite protocol, setting, and outcome types.

The checker searches only for a positive left-minus-right probability gap. If no
such entry exists, normalization plus pointwise nonpositivity forces equality of
every entry. This avoids an orientation bug when the first differing entry happens
to be negative. -/
namespace OntologySeparation.FiniteComparison

open ExperimentAccess
open Comparison

variable {P M : Type} {E : Interface}

/-- A backend supplies exact rational probabilities and a proof that they are the
same probabilities used by the common normalized Behavior semantics. -/
structure ExactEvaluator (predict : Predictions M P E) where
  value : M → P → E.Setting → E.Outcome → ℚ
  correct : ∀ m p s o, (predict m p).prob s o = (value m p s o : ℝ)

/-- The finite checker distinguishes a genuinely empty allowed domain from
substantive agreement. -/
inductive Result (predict : Predictions M P E) (allowed : P → Prop) (a b : M)
  | empty (proof : ¬ ∃ p, allowed p)
  | agreement (certificate : FamilyAgreement predict allowed a b)
  | separation (certificate : Separator predict allowed a b)

/-- A nonempty checker result can be converted to the common reportable result.
The identity coverage proof upgrades exhaustive finite-family agreement to the
same allowed domain. -/
def Result.toComparison
    {predict : Predictions M P E} {allowed : P → Prop} {a b : M}
    (r : Result predict allowed a b) (nonempty : ∃ p, allowed p) :
    Comparison.Result predict allowed a b :=
  match r with
  | .empty h => False.elim (h nonempty)
  | .agreement h =>
      .agreement (h.promote ⟨by intro p hp; exact hp⟩)
  | .separation w => .separation w

def Result.claim
    {predict : Predictions M P E} {allowed : P → Prop} {a b : M}
    (r : Result predict allowed a b) (nonempty : ∃ p, allowed p) : Claim :=
  (r.toComparison nonempty).claim

/-- Decide a finite exact comparison. The returned proof refers to exactly the
supplied allowed predicate; unsupported or infinite semantics do not enter here. -/
def compare [Fintype P] [Fintype E.Setting] [Fintype E.Outcome]
    (evaluator : ExactEvaluator (E := E) (M := M) (P := P) predict)
    (allowed : P → Prop) [DecidablePred allowed] (a b : M) :
    Result predict allowed a b := by
  if hnonempty : ∃ p, allowed p then
    if hpositive :
        ∃ p, allowed p ∧ ∃ s o,
          evaluator.value a p s o > evaluator.value b p s o then
      rcases hpositive with ⟨p, hp, s, o, hgap⟩
      exact .separation {
        protocol := p
        accessible := hp
        setting := s
        outcome := o
        gap := ((evaluator.value a p s o - evaluator.value b p s o : ℚ) : ℝ)
        positive := by
          exact_mod_cast (sub_pos.mpr hgap)
        difference := by
          rw [evaluator.correct a p s o, evaluator.correct b p s o]
          push_cast
          ring
      }
    else
      rcases hnonempty with ⟨witness, hwitness⟩
      exact .agreement {
        protocol := witness
        included := hwitness
        proof := by
          intro p hp s o
          have hqle : ∀ o', evaluator.value a p s o' ≤ evaluator.value b p s o' := by
            intro o'
            exact le_of_not_gt (by
              intro hgt
              exact hpositive ⟨p, hp, s, o', hgt⟩)
          have hreal_le : ∀ o', (predict a p).prob s o' ≤ (predict b p).prob s o' := by
            intro o'
            rw [evaluator.correct a p s o', evaluator.correct b p s o']
            exact_mod_cast hqle o'
          have hle := hreal_le o
          have hnotlt : ¬ (predict a p).prob s o < (predict b p).prob s o := by
            intro hstrict
            have hsumlt : (∑ o', (predict a p).prob s o') <
                ∑ o', (predict b p).prob s o' := by
              apply Finset.sum_lt_sum
              · intro i hi
                exact hreal_le i
              · exact ⟨o, Finset.mem_univ _, hstrict⟩
            rw [(predict a p).normalized s, (predict b p).normalized s] at hsumlt
            exact (lt_irrefl 1 hsumlt)
          exact le_antisymm hle (le_of_not_gt hnotlt)
      }
  else
    exact .empty hnonempty

end OntologySeparation.FiniteComparison
