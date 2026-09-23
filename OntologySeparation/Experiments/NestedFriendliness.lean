import OntologySeparation.Experiments.LFAssumptionAtlas

/-! Passive finite nesting does not strengthen the repository's finite LF class.

A nested observer layer is represented only by an additional durable copy of each
friend record. No new incompatible intervention or reversal is added. The theorem
below shows that any finite number of such passive copy layers leaves the public
behavior class exactly equal to the existing operational LF class. This is a
negative adversary result: merely saying "super-Wigner" repeatedly cannot produce
a stronger no-go theorem in this model language. -/

namespace OntologySeparation.NestedFriendliness
noncomputable section

open FriendRecords

/-- A friend-record model equipped with `Depth` passive outer record copies. -/
structure Model (Depth : Nat) (Λ : Type) [Fintype Λ] where
  base : FriendRecords.Model Λ
  outerCharlie : Fin Depth → Λ → Bool
  outerDebbie : Fin Depth → Λ → Bool

variable {Depth : Nat} {Λ : Type} [Fintype Λ]

/-- Every passive outer layer stores exactly the already-existing friend records. -/
def CopyConsistent (m : Model Depth Λ) : Prop :=
  ∀ i l, m.outerCharlie i l = m.base.charlie l ∧
    m.outerDebbie i l = m.base.debbie l

/-- The nested class deliberately adds no new dynamical law beyond passive copying. -/
def Admissible (m : Model Depth Λ) : Prop :=
  ReadableRecords m.base ∧
  ConditionalLocality m.base ∧
  IndependentPreparation m.base ∧
  CopyConsistent m

/-- Public behaviors admitting `Depth` passive nested observer layers. -/
def theory (Depth : Nat) (p : Behavior LF.interface) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (m : Model Depth Λ),
    Admissible m ∧ m.base.behavior = p

/-- Add arbitrarily many passive copies to any operational LF model. -/
def lift (Depth : Nat) (m : FriendRecords.Model Λ) : Model Depth Λ where
  base := m
  outerCharlie := fun _ l => m.charlie l
  outerDebbie := fun _ l => m.debbie l

theorem lift_copyConsistent (Depth : Nat) (m : FriendRecords.Model Λ) :
    CopyConsistent (lift Depth m) := by
  intro i l
  exact ⟨rfl, rfl⟩

/-- Passive finite nesting is behaviorally exactly ordinary operational LF. -/
theorem theory_iff_operational (Depth : Nat) (p : Behavior LF.interface) :
    theory Depth p ↔ LFAssumptionAtlas.OperationalLF p := by
  constructor
  · rintro ⟨Λ, inst, m, h, hp⟩
    letI := inst
    exact ⟨Λ, inst, m.base, h.1, h.2.1, h.2.2.1, hp⟩
  · rintro ⟨Λ, inst, m, hr, hl, hi, hp⟩
    letI := inst
    exact ⟨Λ, inst, lift Depth m,
      ⟨hr, hl, hi, lift_copyConsistent Depth m⟩, hp⟩

/-- Hence passive nesting also leaves the exact finite LF class unchanged. -/
theorem theory_iff_lf (Depth : Nat) (p : Behavior LF.interface) :
    theory Depth p ↔ LF.theory p :=
  (theory_iff_operational Depth p).trans
    (LFAssumptionAtlas.operational_iff_lf p)

/-- The existing quantum LF witness is excluded for every passive nesting depth,
but for exactly the same reason as at depth zero. -/
theorem quantum_excluded (Depth : Nat) :
    ¬ theory Depth RealQuantum.lfBehavior := by
  intro h
  exact LF.quantumSeparation.excludes ((theory_iff_lf Depth _).mp h)

/-- Increasing passive nesting depth cannot shrink or enlarge the public class. -/
theorem depth_invariant (d e : Nat) (p : Behavior LF.interface) :
    theory d p ↔ theory e p := by
  rw [theory_iff_lf, theory_iff_lf]

end
end OntologySeparation.NestedFriendliness
