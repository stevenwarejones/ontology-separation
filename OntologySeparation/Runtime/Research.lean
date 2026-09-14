import Lean

/-! Small executable experiments. No imported proof libraries enter the native binary.
Proofs in Experiments/Research check these exact functions. -/
namespace OntologySeparation.Research

abbrev Triple := Bool × Bool × Bool

def mismatch (a b : Bool) : Rat := if a == b then 0 else 1

def triangle (v : Triple) : Rat :=
  mismatch v.1 v.2.1 + mismatch v.2.1 v.2.2 + mismatch v.1 v.2.2

/-- Three contexts each return one fair bit and its opposite. -/
def pairwise (a b : Bool) : Rat := if a == b then 0 else 1/2

/-- Decoder outputs true with probability `d observed`. Input bits are fair. -/
def success (d : Bool → Rat) (a b : Bool) : Rat :=
  if xor a b then d a else 1-d a

def oneBitRecovery (d : Bool → Rat) : Rat :=
  (success d false false + success d false true +
   success d true false + success d true true) / 4

def jointRecovery (d : Bool → Bool → Bool) : Rat :=
  let hit (a b : Bool) : Rat := if d a b == xor a b then 1 else 0
  (hit false false + hit false true + hit true false + hit true true) / 4

abbrev Vector := Bool → Rat

def xGate (v : Vector) : Vector := fun b => v (!b)
def zGate (v : Vector) : Vector := fun b => (if b then -1 else 1) * v b

def normSq (v : Vector) : Rat := v false ^ 2 + v true ^ 2

/-- Minus-port probability: unnormalized branch difference carries factor 1/2.
For X,Z the two orders differ by a sign. -/
def orderMinus (v : Vector) : Rat :=
  normSq (fun b => (xGate (zGate v) b - zGate (xGate v) b) / 2)

/-- A classical mixture of the two orders destroys the off-diagonal control blocks. -/
def orderDephased (v : Vector) : Rat :=
  (normSq (xGate (zGate v)) + normSq (zGate (xGate v))) / 4

def noisyOrder (p : Rat) (v : Vector) : Rat :=
  (1-p) * orderMinus v + p * orderDephased v

abbrev Amplitude := Bool → Bool → Rat

def product (a b : Vector) : Amplitude := fun i j => a i * b j

def determinant (v : Amplitude) : Rat :=
  v false false * v true true - v false true * v true false

/-- CZ applied to |++>, in computational basis. -/
def phaseState : Amplitude := fun a b => if a && b then -1/2 else 1/2

/-- Weight of non-LF runs in a contamination model, not a communication metric. -/
def contaminatedScore (epsilon good bad : Rat) : Rat :=
  (1-epsilon) * good + epsilon * bad

end OntologySeparation.Research
