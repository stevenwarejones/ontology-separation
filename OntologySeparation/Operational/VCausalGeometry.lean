import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Preferred-frame geometry. Coordinates are (ct,x), with c=1.
Hidden cones are open, as in Li et al. S.I.5; ordinary causal futures are closed.
Hidden links and sender exclusion have strict margins in the examples.
A recipient-to-collector link may lie on the closed light-cone boundary. -/
namespace OntologySeparation.VCausal

structure Event where
  t : ℚ
  x : ℚ
  deriving DecidableEq

def precedes (v : ℚ) (p q : Event) : Prop :=
  p.t < q.t ∧ |q.x - p.x| < v * (q.t - p.t)

instance (v : ℚ) (p q : Event) : Decidable (precedes v p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

def lightFuture (p q : Event) : Prop := |q.x - p.x| ≤ q.t - p.t

instance (p q : Event) : Decidable (lightFuture p q) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem precedes_irrefl (v : ℚ) (p : Event) : ¬ precedes v p p := by
  simp [precedes]

theorem precedes_trans {v : ℚ} {p q r : Event}
    (hpq : precedes v p q) (hqr : precedes v q r) : precedes v p r := by
  constructor
  · exact lt_trans hpq.1 hqr.1
  · have h := abs_add_le (r.x - q.x) (q.x - p.x)
    have he : r.x - q.x + (q.x - p.x) = r.x - p.x := by ring
    rw [he] at h
    nlinarith [hpq.2, hqr.2]

theorem lightFuture_refl (p : Event) : lightFuture p p := by
  simp [lightFuture]

theorem lightFuture_trans {p q r : Event}
    (hpq : lightFuture p q) (hqr : lightFuture q r) : lightFuture p r := by
  have h := abs_add_le (r.x - q.x) (q.x - p.x)
  have he : r.x - q.x + (q.x - p.x) = r.x - p.x := by ring
  rw [he] at h
  unfold lightFuture at *
  linarith

inductive Party | A | B | C | D deriving DecidableEq, Fintype
abbrev Layout := Party → Event

/-- Choices can be separated from outcomes. Inputs may reach a party only if
 their actual choice events are in its causal past; an outcome cannot be sent
 before its production event. -/
structure MeasurementLayout where
  choice : Layout
  outcome : Layout
  choice_before : ∀ p, lightFuture (choice p) (outcome p)

/-- Coincident choice/outcome events are an explicit idealization. -/
def Layout.instantaneous (L : Layout) : MeasurementLayout where
  choice := L
  outcome := L
  choice_before := fun p => lightFuture_refl (L p)

structure LC4Layout (L : Layout) (v : ℚ) : Prop where
  speed : 1 < v
  ab : precedes v (L .A) (L .B)
  ac : precedes v (L .A) (L .C)
  db : precedes v (L .D) (L .B)
  dc : precedes v (L .D) (L .C)
  bc : ¬ precedes v (L .B) (L .C)
  cb : ¬ precedes v (L .C) (L .B)

/-- Transitivity prevents relays from creating a path outside the v-cone. -/
theorem relay_inside_cone {v : ℚ} {p q : Event}
    (h : Relation.TransGen (precedes v) p q) : precedes v p q := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact precedes_trans ih h

theorem LC4Layout.no_late_to_early {L : Layout} {v : ℚ} (h : LC4Layout L v) :
    ¬ precedes v (L .B) (L .A) ∧ ¬ precedes v (L .C) (L .A) ∧
    ¬ precedes v (L .B) (L .D) ∧ ¬ precedes v (L .C) (L .D) := by
  exact ⟨fun k => (precedes_irrefl v _) (precedes_trans h.ab k),
    fun k => (precedes_irrefl v _) (precedes_trans h.ac k),
    fun k => (precedes_irrefl v _) (precedes_trans h.db k),
    fun k => (precedes_irrefl v _) (precedes_trans h.dc k)⟩

end OntologySeparation.VCausal
