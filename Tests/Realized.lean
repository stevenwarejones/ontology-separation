import OntologySeparation

open OntologySeparation

-- Requiring every predicate and imposing no constraint are different operations.
example : AssumptionProfile.requireAll.realism = .require := rfl
example : AssumptionProfile.unconstrained.locality = .unspecified := rfl
example : ¬ (AssumptionProfile.select .require .reject .require .require).globalTruth.Holds True :=
  fun h => h trivial

-- A realized bound supplies a model AND the matching law proof.
example : OperationalBell.screeningOffProfile.Realizable
    (OperationalBell.vocabulary (Λ := Unit)) := ClassicalWorld.realizedBound.realizable
example : Bell.score ClassicalWorld.constantWorld.operational.behavior ≤ 2 :=
  ClassicalWorld.realizedBound.valid _ ClassicalWorld.realizedBound.satisfies

-- An empty profile can have a universal bound, but cannot have a realized one.
example {M : Type} {q : Question} {v : Vocabulary M} {p : AssumptionProfile}
    {predict : M → Behavior q.interface} (empty : ¬ p.Realizable v)
    (r : RealizedProfileBound q v p predict) : False := empty r.realizable

-- One cannot attach a model without evidence that it satisfies the same profile.
example {M : Type} {q : Question} {v : Vocabulary M} {p : AssumptionProfile}
    {predict : M → Behavior q.interface} (_bound : ProfileBound q v p predict) (_m : M) : True := by
  fail_if_success
    have wrong : RealizedProfileBound q v p predict := ⟨_bound, _m, by trivial⟩
  trivial
