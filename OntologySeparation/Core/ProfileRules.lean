import OntologySeparation.Core.Certified
namespace OntologySeparation
/-- Stronger selections retain every law required or rejected by the weaker one. -/
def Stance.Extends (strong weak : Stance) : Prop := weak = .unspecified ∨ strong = weak
instance (a b : Stance) : Decidable (a.Extends b) := inferInstanceAs (Decidable (_ ∨ _))
theorem Stance.Extends.sound {a b : Stance} (h : a.Extends b) (P : Prop)
    (hp : a.Holds P) : b.Holds P := by
  rcases h with h | h
  · rw [h]; trivial
  · rw [← h]; exact hp

def AssumptionProfile.Extends (strong weak : AssumptionProfile) : Prop :=
  strong.realism.Extends weak.realism ∧ strong.globalTruth.Extends weak.globalTruth ∧
  strong.locality.Extends weak.locality ∧
  strong.measurementIndependent.Extends weak.measurementIndependent
instance (a b : AssumptionProfile) : Decidable (a.Extends b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
theorem AssumptionProfile.Extends.sound {a b : AssumptionProfile} (h : a.Extends b)
    {M : Type} (v : Vocabulary M) (m : M) (ha : a.Satisfied v m) : b.Satisfied v m :=
  ⟨h.1.sound _ ha.1, h.2.1.sound _ ha.2.1,
   h.2.2.1.sound _ ha.2.2.1, h.2.2.2.sound _ ha.2.2.2⟩
def ProfileBound.under {M : Type} {q : Question} {v : Vocabulary M}
    {base : AssumptionProfile} {predict : M → Behavior q.interface}
    (result : ProfileBound q v base predict) (stronger : AssumptionProfile)
    (h : stronger.Extends base) : ProfileBound q v stronger predict where
  target := result.target
  bridge := ⟨fun m hm => result.bridge.sound m (h.sound v m hm)⟩
  bound := result.bound
end OntologySeparation
