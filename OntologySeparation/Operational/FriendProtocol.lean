import OntologySeparation.Recipes.TwoQubit
import Mathlib.Tactic.FinCases

/-! Four explicit registers: Alice's system, Bob's system, Charlie's record,
Debbie's record. Only a proved encoded subspace is stored compactly. -/
namespace OntologySeparation.FriendProtocol
open TwoQubit
abbrev Registers := Bool × Bool × Bool × Bool
abbrev Amplitude := Registers → ℚ

def blank (v : Amplitudes) : Amplitude := fun (a,b,c,d) =>
  if c = false ∧ d = false then v.entry (a,b) else 0

def copyA (f : Amplitude) : Amplitude := fun (a,b,c,d) => f (a,b,xor c a,d)
def copyB (f : Amplitude) : Amplitude := fun (a,b,c,d) => f (a,b,c,xor d b)
def encode (v : Amplitudes) : Amplitude := copyB (copyA (blank v))

theorem encode_entry (v : Amplitudes) (a b c d : Bool) :
    encode v (a,b,c,d) = if c = a ∧ d = b then v.entry (a,b) else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem copyA_involution (f : Amplitude) : copyA (copyA f) = f := by
  funext ⟨a,b,c,d⟩; cases a <;> cases c <;> rfl
theorem copyB_involution (f : Amplitude) : copyB (copyB f) = f := by
  funext ⟨a,b,c,d⟩; cases b <;> cases d <;> rfl

theorem undo_friends (v : Amplitudes) : copyA (copyB (encode v)) = blank v := by
  rw [encode, copyB_involution, copyA_involution]

theorem encode_norm (v : Amplitudes) : ∑ r : Registers, (encode v r)^2 = v.normSq := by
  simp [Fintype.sum_prod_type, encode_entry, Amplitudes.entry, Amplitudes.normSq]
  ring

theorem record_agreement (v : Amplitudes) (a b c d : Bool)
    (different : c ≠ a ∨ d ≠ b) : encode v (a,b,c,d) = 0 := by
  rw [encode_entry]; split_ifs with h
  · exact False.elim (different.elim (fun hc => hc h.1) (fun hd => hd h.2))
  · rfl

/-- Physical Z on Charlie's or Debbie's record. -/
def recordZ (w : Wire) (f : Amplitude) : Amplitude := fun (a,b,c,d) =>
  (if (match w with | .alice => c | .bob => d) then -1 else 1) * f (a,b,c,d)

theorem recordZ_encoded (w : Wire) (v : Pure) :
    recordZ w (encode v.vector) = encode (v.gate (.z w)).vector := by
  funext ⟨a,b,c,d⟩
  cases w <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [recordZ, encode_entry, Pure.gate, Gate.apply, Amplitudes.entry]

inductive Choice where
  | readRecord
  | reverse (basis : Basis)

def Choice.basis : Choice → Basis | .readRecord => .z | .reverse q => q
/-- Coordinate transform on a system, after uncopying its own record. -/
def rotateA (q : Basis) (f : Amplitude) : Amplitude := fun (a,b,c,d) =>
  if a then -q.s*f (false,b,c,d)+q.c*f (true,b,c,d)
  else q.c*f (false,b,c,d)+q.s*f (true,b,c,d)
def rotateB (q : Basis) (f : Amplitude) : Amplitude := fun (a,b,c,d) =>
  if b then -q.s*f (a,false,c,d)+q.c*f (a,true,c,d)
  else q.c*f (a,false,c,d)+q.s*f (a,true,c,d)
def actA : Choice → Amplitude → Amplitude
  | .readRecord, f => f | .reverse q, f => rotateA q (copyA f)
def actB : Choice → Amplitude → Amplitude
  | .readRecord, f => f | .reverse q, f => rotateB q (copyB f)
/-- The unreported bit is summed out, never conditioned on. -/
def slot (q : Choice) (out hidden : Bool) : Bool × Bool :=
  match q with | .readRecord => (hidden,out) | .reverse _ => (out,hidden)
def Choice.scale (q : Choice) : ℚ := q.basis.c^2+q.basis.s^2

/-- Norm of the actual four-register output before final readout. -/
theorem output_norm (v : Amplitudes) (x y : Choice) :
    ∑ r : Registers, (actB y (actA x (encode v)) r)^2 =
      x.scale * y.scale * v.normSq := by
  cases x <;> cases y <;>
    simp [Choice.scale, Choice.basis, actA, actB, rotateA, rotateB,
      copyA, copyB, encode, blank, Fintype.sum_prod_type,
      Amplitudes.entry, Amplitudes.normSq, Basis.z, Basis.of] <;> ring

def pureProbability (v : Pure) (x y : Choice) (a b : Bool) : ℚ :=
  (∑ h : Bool × Bool,
    (actB y (actA x (encode v.vector))
      ((slot x a h.1).1,(slot y b h.2).1,(slot x a h.1).2,(slot y b h.2).2))^2) /
    (x.scale * y.scale * v.vector.normSq)

/-- Exact reduction of the full four-register read/reverse experiment, all branches. -/
theorem pure_probability_bridge (v : Pure) (x y : Choice) (a b : Bool) :
    pureProbability v x y a b =
      (readout (.pure v) x.basis y.basis).probability (a,b) := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    simp [pureProbability, Choice.scale, Choice.basis, slot, actA, actB, rotateA, rotateB,
      copyA, copyB, encode, blank, Fintype.sum_prod_type,
      readout, State.gate, State.probability, Pure.probability, Pure.gate,
      Gate.apply, Amplitudes.entry, Amplitudes.normSq,
      Basis.z, Basis.of] <;> ring

theorem pure_normalized (v : Pure) (x y : Choice) :
    ∑ o : Bool × Bool, pureProbability v x y o.1 o.2 = 1 := by
  simp_rw [pure_probability_bridge]
  exact (readout (.pure v) x.basis y.basis).normalized

/-- Ensembles include record dephasing via recordZ_encoded. -/
def probability : State → Choice → Choice → Bool → Bool → ℚ
  | .pure v, x,y,a,b => pureProbability v x y a b
  | .mix p l r, x,y,a,b => p.value * probability l x y a b + (1-p.value)*probability r x y a b

theorem probability_bridge (v : State) (x y : Choice) (a b : Bool) :
    probability v x y a b = (readout v x.basis y.basis).probability (a,b) := by
  induction v with
  | pure v => exact pure_probability_bridge v x y a b
  | mix p l r hl hr => simp [probability, readout, State.gate, State.probability, hl, hr, readout] at *

end OntologySeparation.FriendProtocol
