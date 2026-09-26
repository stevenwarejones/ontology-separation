import OntologySeparation.Operational.VCausalGeometry
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Push

namespace OntologySeparation.VCausal

/-- Direct collection of a nonempty set of records outside the sender's
closed light cone. Geometry and other settings are fixed during a switch. -/
def Collectible (s : Event) (R : Finset Event) : Prop :=
  R.Nonempty ∧ ∃ q, (∀ r ∈ R, lightFuture r q) ∧ ¬ lightFuture s q

def plus (p : Event) : ℚ := p.t + p.x
def minus (p : Event) : ℚ := p.t - p.x

theorem lightFuture_iff (p q : Event) :
    lightFuture p q ↔ plus p ≤ plus q ∧ minus p ≤ minus q := by
  unfold lightFuture plus minus
  rw [abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

/-- Apex of the intersection in 1+1 dimensions; no optimization oracle. -/
def collectionApex (R : Finset Event) (h : R.Nonempty) : Event :=
  let u := R.sup' h plus
  let w := R.sup' h minus
  ⟨(u+w)/2, (u-w)/2⟩

theorem apex_plus (R : Finset Event) (h : R.Nonempty) :
    plus (collectionApex R h) = R.sup' h plus := by
  change (R.sup' h plus + R.sup' h minus)/2 +
    (R.sup' h plus - R.sup' h minus)/2 = R.sup' h plus
  ring

theorem apex_minus (R : Finset Event) (h : R.Nonempty) :
    minus (collectionApex R h) = R.sup' h minus := by
  change (R.sup' h plus + R.sup' h minus)/2 -
    (R.sup' h plus - R.sup' h minus)/2 = R.sup' h minus
  ring

theorem apex_receives (R : Finset Event) (h : R.Nonempty) (r : Event) (hr : r ∈ R) :
    lightFuture r (collectionApex R h) := by
  rw [lightFuture_iff, apex_plus, apex_minus]
  exact ⟨Finset.le_sup' plus hr, Finset.le_sup' minus hr⟩

theorem apex_before_collection (R : Finset Event) (h : R.Nonempty) (q : Event)
    (hq : ∀ r ∈ R, lightFuture r q) : lightFuture (collectionApex R h) q := by
  rw [lightFuture_iff, apex_plus, apex_minus]
  constructor
  · exact Finset.sup'_le _ _ (fun r hr => ((lightFuture_iff r q).mp (hq r hr)).1)
  · exact Finset.sup'_le _ _ (fun r hr => ((lightFuture_iff r q).mp (hq r hr)).2)

theorem collectible_iff_apex (s : Event) (R : Finset Event) (h : R.Nonempty) :
    Collectible s R ↔ ¬ lightFuture s (collectionApex R h) := by
  constructor
  · rintro ⟨_, q, hq, hs⟩ hsa
    exact hs (lightFuture_trans hsa (apex_before_collection R h q hq))
  · intro hs
    exact ⟨h, collectionApex R h, apex_receives R h, hs⟩

theorem collectible_criterion (s : Event) (R : Finset Event) (h : R.Nonempty) :
    Collectible s R ↔ R.sup' h plus < plus s ∨ R.sup' h minus < minus s := by
  rw [collectible_iff_apex s R h, lightFuture_iff, apex_plus, apex_minus]
  simp only [not_and_or, not_le]

/-- If the sender is between both later blind stations, their joint records
can never be collected outside its light cone, at any collection point. -/
theorem segment_obstruction (s b c q : Event)
    (htb : s.t ≤ b.t) (htc : s.t ≤ c.t)
    (hxb : b.x ≤ s.x) (hxc : s.x ≤ c.x)
    (hb : lightFuture b q) (hc : lightFuture c q) : lightFuture s q := by
  rw [lightFuture_iff] at hb hc ⊢
  unfold plus minus at *
  exact ⟨by linarith [hc.1], by linarith [hb.2]⟩

theorem not_collectible_of_between (s b c : Event)
    (htb : s.t ≤ b.t) (htc : s.t ≤ c.t)
    (hxb : b.x ≤ s.x) (hxc : s.x ≤ c.x) :
    ¬ Collectible s {b,c} := by
  rintro ⟨_, q, hq, hs⟩
  exact hs (segment_obstruction s b c q htb htc hxb hxc
    (hq b (by simp)) (hq c (by simp)))

/-- More required records cannot make collection easier. -/
theorem Collectible.mono {s : Event} {R S : Finset Event}
    (h : Collectible s S) (hR : R.Nonempty) (hsub : R ⊆ S) : Collectible s R := by
  obtain ⟨_,q,hq,hs⟩ := h
  exact ⟨hR,q,fun r hr => hq r (hsub hr),hs⟩

/-- The only recipient sets not covered by a pinned pair contain BOTH blind
parties. This enumeration concerns sets of parties, not probability tables. -/
theorem recipients_A_dichotomy (R : Finset Party) (hA : Party.A ∉ R) :
    R ⊆ {.B,.D} ∨ R ⊆ {.C,.D} ∨ ({.B,.C} : Finset Party) ⊆ R := by
  by_cases hB : Party.B ∈ R
  · by_cases hC : Party.C ∈ R
    · exact Or.inr (Or.inr (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl <;> assumption))
    · left
      intro p hp
      cases p <;> simp_all
  · right; left
    intro p hp
    cases p <;> simp_all

theorem recipients_D_dichotomy (R : Finset Party) (hD : Party.D ∉ R) :
    R ⊆ {.A,.B} ∨ R ⊆ {.A,.C} ∨ ({.B,.C} : Finset Party) ⊆ R := by
  by_cases hB : Party.B ∈ R
  · by_cases hC : Party.C ∈ R
    · exact Or.inr (Or.inr (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl <;> assumption))
    · left
      intro p hp
      cases p <;> simp_all
  · right; left
    intro p hp
    cases p <;> simp_all

/-- In the segment layout every collectible A-recipient set is contained in
one of the two pinned pairs. This includes the co-located three-site layout. -/
theorem collectible_A_pinned_pair (L : Layout) (R : Finset Party)
    (hA : Party.A ∉ R)
    (htb : (L .A).t ≤ (L .B).t) (htc : (L .A).t ≤ (L .C).t)
    (hxb : (L .B).x ≤ (L .A).x) (hxc : (L .A).x ≤ (L .C).x)
    (hc : Collectible (L .A) (R.image L)) : R ⊆ {.B,.D} ∨ R ⊆ {.C,.D} := by
  rcases recipients_A_dichotomy R hA with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    apply not_collectible_of_between (L .A) (L .B) (L .C) htb htc hxb hxc
    apply hc.mono (by simp)
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Finset.mem_image.mpr ⟨.B,h (by simp),rfl⟩
    · exact Finset.mem_image.mpr ⟨.C,h (by simp),rfl⟩

theorem collectible_D_pinned_pair (L : Layout) (R : Finset Party)
    (hD : Party.D ∉ R)
    (htb : (L .D).t ≤ (L .B).t) (htc : (L .D).t ≤ (L .C).t)
    (hxb : (L .B).x ≤ (L .D).x) (hxc : (L .D).x ≤ (L .C).x)
    (hc : Collectible (L .D) (R.image L)) : R ⊆ {.A,.B} ∨ R ⊆ {.A,.C} := by
  rcases recipients_D_dichotomy R hD with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    apply not_collectible_of_between (L .D) (L .B) (L .C) htb htc hxb hxc
    apply hc.mono (by simp)
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Finset.mem_image.mpr ⟨.B,h (by simp),rfl⟩
    · exact Finset.mem_image.mpr ⟨.C,h (by simp),rfl⟩

end OntologySeparation.VCausal
