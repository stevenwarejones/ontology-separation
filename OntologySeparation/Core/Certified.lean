import OntologySeparation.Core.Exclusion

/-! Proofs indexed by the actual question, model, protocol, and claimed value. -/
namespace OntologySeparation
structure Question where
  interface : Interface
  score : Observable interface
structure Prediction (q : Question) (p : Behavior q.interface) where
  value : ℝ
  correct : q.score p = value
structure ProfileBound {M : Type} (q : Question) (v : Vocabulary M)
    (profile : AssumptionProfile) (predict : M → Behavior q.interface) where
  target : Theory q.interface
  bridge : ProfileBridge M v profile predict target
  bound : Bound target q.score
namespace ProfileBound
variable {M : Type} {q : Question} {v : Vocabulary M} {profile : AssumptionProfile}
  {predict : M → Behavior q.interface}
theorem valid (r : ProfileBound q v profile predict) (m : M)
    (h : profile.Satisfied v m) : q.score (predict m) ≤ r.bound.ceiling :=
  r.bound.valid _ (r.bridge.sound m h)
theorem excludes (r : ProfileBound q v profile predict) (p : Behavior q.interface)
    (h : r.bound.ceiling < q.score p) : ¬ profileTheory v profile predict p :=
  r.bridge.excludes p (fun hp => (not_lt_of_ge (r.bound.valid p hp)) h)
end ProfileBound

/-- A universal bound together with an actual model satisfying exactly its profile.
This rules out an empty model class, but does not assert the ceiling is attained
or that this mathematical model describes a physical system. -/
structure RealizedProfileBound {M : Type} (q : Question) (v : Vocabulary M)
    (profile : AssumptionProfile) (predict : M → Behavior q.interface) where
  result : ProfileBound q v profile predict
  model : M
  satisfies : profile.Satisfied v model

namespace RealizedProfileBound
variable {M : Type} {q : Question} {v : Vocabulary M} {profile : AssumptionProfile}
  {predict : M → Behavior q.interface}
theorem realizable (r : RealizedProfileBound q v profile predict) : profile.Realizable v :=
  ⟨r.model, r.satisfies⟩
def witness (r : RealizedProfileBound q v profile predict) :
    Witness (profileTheory v profile predict) := profileWitness v profile predict r.model r.satisfies
theorem valid (r : RealizedProfileBound q v profile predict) (m : M)
    (h : profile.Satisfied v m) : q.score (predict m) ≤ r.result.bound.ceiling :=
  r.result.valid m h
end RealizedProfileBound

structure PredictionFamily {M P : Type} (q : Question)
    (predict : M → P → Behavior q.interface) where
  value : M → P → ℝ
  correct : ∀ m p, q.score (predict m p) = value m p
end OntologySeparation
