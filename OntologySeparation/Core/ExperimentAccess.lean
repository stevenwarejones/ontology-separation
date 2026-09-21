import OntologySeparation.Core.Operational

/-! Equivalence is relative to explicitly allowed experiments. Models cannot choose
which protocol is compared. A separating witness must establish a positive gap. -/
namespace OntologySeparation.ExperimentAccess

variable {P M : Type} {E : Interface}

/-- The same protocol is interpreted by each model into a normalized behavior. -/
abbrev Predictions (M P : Type) (E : Interface) := M → P → Behavior E

/-- Agreement on every setting and outcome of every allowed protocol. -/
def Equivalent (predict : Predictions M P E) (allowed : P → Prop) (a b : M) : Prop :=
  ∀ p, allowed p → ObservationallyEquivalent (predict a p) (predict b p)

/-- An operational difference, with both access and a strict probability gap checked. -/
structure Separator (predict : Predictions M P E) (allowed : P → Prop) (a b : M) where
  protocol : P
  accessible : allowed protocol
  setting : E.Setting
  outcome : E.Outcome
  gap : ℝ
  positive : 0 < gap
  difference : (predict a protocol).prob setting outcome -
    (predict b protocol).prob setting outcome = gap

theorem Equivalent.restrict {predict : Predictions M P E} {wide narrow : P → Prop}
    {a b : M} (h : Equivalent predict wide a b) (access : ∀ p, narrow p → wide p) :
    Equivalent predict narrow a b := fun p hp => h p (access p hp)

theorem Equivalent.refl (predict : Predictions M P E) (allowed : P → Prop) (a : M) :
    Equivalent predict allowed a a := fun _ _ _ _ => rfl

theorem Equivalent.symm {predict : Predictions M P E} {allowed : P → Prop} {a b : M}
    (h : Equivalent predict allowed a b) : Equivalent predict allowed b a :=
  fun p hp s o => (h p hp s o).symm

theorem Equivalent.trans {predict : Predictions M P E} {allowed : P → Prop} {a b c : M}
    (hab : Equivalent predict allowed a b) (hbc : Equivalent predict allowed b c) :
    Equivalent predict allowed a c := fun p hp s o => (hab p hp s o).trans (hbc p hp s o)

theorem Separator.not_equivalent {predict : Predictions M P E} {allowed : P → Prop}
    {a b : M} (w : Separator predict allowed a b) : ¬ Equivalent predict allowed a b := by
  intro h
  have he := h w.protocol w.accessible w.setting w.outcome
  have hd := w.difference
  have hg := w.positive
  rw [he, sub_self] at hd
  linarith

/-- More access preserves a previously available distinguishing experiment. -/
def Separator.enlarge {predict : Predictions M P E} {narrow wide : P → Prop} {a b : M}
    (w : Separator predict narrow a b) (access : ∀ p, narrow p → wide p) :
    Separator predict wide a b := { w with accessible := access _ w.accessible }

/-- Equivalence also prevents distinguishing by any statistic of a behavior,
not just by the particular entries a user happened to display. -/
theorem Equivalent.statistic {predict : Predictions M P E} {allowed : P → Prop}
    {a b : M} (h : Equivalent predict allowed a b) (p : P) (hp : allowed p)
    (score : Observable E) : score (predict a p) = score (predict b p) := by
  have he : predict a p = predict b p := by
    cases h₁ : predict a p with
    | mk f hf hn =>
      cases h₂ : predict b p with
      | mk g hg hm =>
        have hfg : f = g := funext fun s => funext fun o => by
          simpa [ObservationallyEquivalent, h₁, h₂] using h p hp s o
        cases hfg
        rfl
  rw [he]
end OntologySeparation.ExperimentAccess
