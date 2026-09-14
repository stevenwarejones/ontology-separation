import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Theory-independent finite operational interfaces and proof-bearing comparisons.
Physical laws are predicates supplied as data, never global logical axioms. -/

namespace OntologySeparation

universe u v

/-- Public experimental settings and outcomes; internal memories need not be outcomes. -/
structure Interface where
  Setting : Type u
  Outcome : Type v
  [finiteOutcome : Fintype Outcome]

attribute [instance] Interface.finiteOutcome

/-- A conditional probability table with normalization proved for each setting. -/
structure Behavior (E : Interface) where
  prob : E.Setting → E.Outcome → ℝ
  nonneg : ∀ s o, 0 ≤ prob s o
  normalized : ∀ s, ∑ o, prob s o = 1

/-- Each entry is bounded above by one, derived from the distribution laws. -/
theorem Behavior.prob_le_one {E : Interface} (p : Behavior E) (s : E.Setting)
    (o : E.Outcome) : p.prob s o ≤ 1 := by
  classical
  calc
    p.prob s o ≤ ∑ j, p.prob s j :=
      Finset.single_le_sum (fun j _ => p.nonneg s j) (Finset.mem_univ o)
    _ = 1 := p.normalized s

/-- Convexly mix two models without leaving the probability simplex. -/
def Behavior.mix {E : Interface} (p q : Behavior E) (v : ℝ)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) : Behavior E where
  prob s o := v * p.prob s o + (1-v) * q.prob s o
  nonneg s o := add_nonneg (mul_nonneg hv (p.nonneg s o))
    (mul_nonneg (sub_nonneg.mpr hv1) (q.nonneg s o))
  normalized s := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      p.normalized, q.normalized]
    ring

/-- An assumption-defined class. This does not assert that the class is inhabited. -/
abbrev Theory (E : Interface) := Behavior E → Prop

/-- A statistic of the publicly observable behavior. -/
abbrev Observable (E : Interface) := Behavior E → ℝ

/-- A universal bound, with its proof attached. -/
structure Bound {E : Interface} (T : Theory E) (score : Observable E) where
  ceiling : ℝ
  valid : ∀ p, T p → score p ≤ ceiling

/-- A realized member, separately establishing that the theory is nonempty. -/
structure Witness {E : Interface} (T : Theory E) where
  behavior : Behavior E
  admissible : T behavior

/-- A bound for one class and a violating realization in another. -/
structure Separation {E : Interface} (A B : Theory E) (score : Observable E) where
  bound : Bound A score
  witness : Witness B
  violation : bound.ceiling < score witness.behavior

/-- The witness of a separation cannot belong to the bounded theory. -/
theorem Separation.excludes {E : Interface} {A B : Theory E} {score : Observable E}
    (s : Separation A B score) : ¬ A s.witness.behavior := by
  intro h
  exact (not_lt_of_ge (s.bound.valid _ h)) s.violation

/-- A theory refines another when every permitted behavior is permitted by the latter. -/
def Refines {E : Interface} (A B : Theory E) : Prop := ∀ p, A p → B p

theorem Bound.restrict {E : Interface} {A B : Theory E} {score : Observable E}
    (b : Bound B score) (h : Refines A B) : ∀ p, A p → score p ≤ b.ceiling := by
  intro p hp
  exact b.valid p (h p hp)

/-- Comparison is extensional in public probabilities, not in interpretation labels. -/
def ObservationallyEquivalent {E : Interface} (p q : Behavior E) : Prop :=
  ∀ s o, p.prob s o = q.prob s o

/-- A deterministic operational model supplies a normalized behavior for each protocol. -/
structure Interpreter (Protocol : Type) (E : Interface) where
  supports : Protocol → Prop
  interpret : (p : Protocol) → supports p → Behavior E

end OntologySeparation
