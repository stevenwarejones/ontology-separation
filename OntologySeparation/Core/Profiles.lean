import OntologySeparation.Core.Operational
import OntologySeparation.Core.Assumptions

/-! Connect assumption profiles to actual experimental predictions.
The model author supplies the semantics; the profile filters that same model space. -/
namespace OntologySeparation

/-- Observable behaviors produced by models satisfying the selected physical laws. -/
def profileTheory {E : Interface} {M : Type} (v : Vocabulary M)
    (profile : AssumptionProfile) (predict : M → Behavior E) : Theory E := fun p =>
  ∃ m, profile.Satisfied v m ∧ predict m = p

/-- A physically realized profile produces an operational witness in the common API. -/
def profileWitness {E : Interface} {M : Type} (v : Vocabulary M)
    (profile : AssumptionProfile) (predict : M → Behavior E) (m : M)
    (h : profile.Satisfied v m) : Witness (profileTheory v profile predict) :=
  ⟨predict m, ⟨m, h, rfl⟩⟩

/-- An inconsistent profile has no observable realizations under any predictor. -/
theorem profileTheory_empty {E : Interface} {M : Type} (v : Vocabulary M)
    (profile : AssumptionProfile) (predict : M → Behavior E)
    (h : ¬ profile.Realizable v) : ∀ p, ¬ profileTheory v profile predict p := by
  intro p hp
  obtain ⟨m, hm, _⟩ := hp
  exact h ⟨m, hm⟩

end OntologySeparation
