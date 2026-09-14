import Lean

/-! Executable rational two-qubit engine. Its mathematics is proved in Parameterss/Memory. -/
namespace OntologySeparation.Memory

abbrev Index := Bool × Bool
abbrev Density := Index → Index → Rat

/-- |+0><+0|, a normalized pure state with rational matrix entries. -/
def initial : Density := fun i j => if !i.2 && !j.2 then 1/2 else 0

/-- CNOT is its own inverse. -/
def cnotIndex (i : Index) : Index := (i.1, xor i.1 i.2)

def cnot (ρ : Density) : Density := fun i j => ρ (cnotIndex i) (cnotIndex j)

/-- Complete dephasing of the memory in its computational basis. -/
def dephase (ρ : Density) : Density := fun i j => if i.2 = j.2 then ρ i j else 0

/-- Convex mixture of identity and complete dephasing, with a physical parameter. -/
structure Parameters where
  strength : Rat

def Parameters.record (m : Parameters) (ρ : Density) : Density :=
  fun i j => (1 - m.strength) * cnot ρ i j + m.strength * dephase (cnot ρ) i j

/-- A deliberately small executable instruction language. -/
inductive Gate where
  | record
  | reverse
  | leak
  | phaseFlip
  deriving Repr, BEq

def phaseSign (i : Index) : Rat := if i.1 then -1 else 1

def step (m : Parameters) (ρ : Density) : Gate → Density
  | .record => m.record ρ
  | .reverse => cnot ρ
  | .leak => dephase ρ
  | .phaseFlip => fun i j => phaseSign i * phaseSign j * ρ i j

def run (m : Parameters) (gates : List Gate) : Density :=
  gates.foldl (step m) initial

/-- Born probability for signal outcome +, tracing over the physical memory. -/
def readPlus (ρ : Density) : Rat :=
  let term (m : Bool) := (ρ (false,m) (false,m) + ρ (false,m) (true,m)
    + ρ (true,m) (false,m) + ρ (true,m) (true,m)) / 2
  term false + term true

def probability (m : Parameters) (gates : List Gate) : Rat := readPlus (run m gates)

def unitary : Parameters := ⟨0⟩
def collapse : Parameters := ⟨1⟩
def halfDephasing : Parameters := ⟨1/2⟩

def echo : List Gate := [.record, .reverse]
def leakedEcho : List Gate := [.record, .leak, .reverse]
def phaseEcho : List Gate := [.record, .phaseFlip, .reverse]


end OntologySeparation.Memory
