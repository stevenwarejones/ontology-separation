import OntologySeparation.Core.Extensions

/-! State maps may act on density operators or other physical states; these
states are not assumed to be hidden-variable samples. -/
namespace OntologySeparation
structure Procedure (A B : Type) where
  evolve : A → B
namespace Procedure
variable {A B C : Type}
def thenDo (p : Procedure A B) (q : Procedure B C) : Procedure A C :=
  ⟨fun a => q.evolve (p.evolve a)⟩
def identity (A : Type) : Procedure A A := ⟨id⟩
def iterate (p : Procedure A A) (n : Nat) : Procedure A A := ⟨p.evolve^[n]⟩
@[simp] theorem thenDo_evolve (p : Procedure A B) (q : Procedure B C) (a : A) :
    (p.thenDo q).evolve a = q.evolve (p.evolve a) := rfl
end Procedure
/-- Only the final readout makes an internal state publicly observable. -/
structure Experiment (S A B O : Type) [Fintype O] where
  prepare : S → A
  procedure : Procedure A B
  readout : B → FiniteDistribution O
namespace Experiment
variable {S A B O : Type} [Fintype O]
def behavior (e : Experiment S A B O) : Behavior { Setting := S, Outcome := O } where
  prob s := (e.readout (e.procedure.evolve (e.prepare s))).mass
  nonneg s := (e.readout (e.procedure.evolve (e.prepare s))).nonneg
  normalized s := (e.readout (e.procedure.evolve (e.prepare s))).total

theorem same_evolution (e f : Experiment S A B O) (hr : e.readout = f.readout)
    (h : ∀ s, e.procedure.evolve (e.prepare s) = f.procedure.evolve (f.prepare s)) :
    ObservationallyEquivalent e.behavior f.behavior := by
  intro s o
  simp only [behavior, hr, h s]
end Experiment
end OntologySeparation
