import OntologySeparation.Core.Profiles

/-! Exclusion rules do not assert that a measured estimator is the true expectation.
A statistical lower bound must be justified externally or by a separate theorem. -/
namespace OntologySeparation

/-- If the true statistic exceeds a universal ceiling, the model is excluded. -/
theorem Bound.excluded_by_lower {E : Interface} {T : Theory E} {score : Observable E}
    (b : Bound T score) (p : Behavior E) (lower : ℝ)
    (hvalid : lower ≤ score p) (hviolates : b.ceiling < lower) : ¬ T p := by
  intro hp
  have h := b.valid p hp
  linarith

/-- A bridge must be proved for the chosen vocabulary and predictor. Merely naming
four Boolean axes supplies no such proof. -/
structure ProfileBridge {E : Interface} (M : Type) (v : Vocabulary M)
    (profile : AssumptionProfile) (predict : M → Behavior E) (T : Theory E) where
  sound : ∀ m, profile.Satisfied v m → T (predict m)

theorem ProfileBridge.excludes {E : Interface} {M : Type} {v : Vocabulary M}
    {profile : AssumptionProfile} {predict : M → Behavior E} {T : Theory E}
    (bridge : ProfileBridge M v profile predict T) (p : Behavior E) (h : ¬ T p) :
    ¬ profileTheory v profile predict p := by
  rintro ⟨m, hm, rfl⟩
  exact h (bridge.sound m hm)

/-- Supporting one allowed behavior cannot identify a unique theory. -/
theorem witness_does_not_identify {E : Interface} {T : Theory E} (p : Behavior E)
    (hp : T p) : T p ∧ (fun _ : Behavior E => True) p := ⟨hp, trivial⟩

end OntologySeparation
