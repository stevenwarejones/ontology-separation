import OntologySeparation.Experiments.LFFiniteSpeed

/-!
# Trusted diagnostics for finite-speed Local Friendliness

This module formalizes the *observable being discussed* in the numerical follow-up.
It deliberately does not certify any solver-discovered optimum.

A "record-revealed" recipient keeps the absolute friend-record pair together with
one late outcome.  This is stronger information than the public Alice/Bob behavior.
The total-variation quantities below therefore measure hidden conditional locality
failure, not operational public signaling.
-/

namespace OntologySeparation.LFFiniteSpeed
noncomputable section

open LFJoint

/-- Joint mass of the absolute record pair and Alice's late outcome. -/
def recordAlice (j : AbsoluteEventTable) (x y : Fin 3) (r : Record) (a : Bool) : ℝ :=
  ∑ b : Bool, j.prob (x,y) r (a,b)

/-- Joint mass of the absolute record pair and Bob's late outcome. -/
def recordBob (j : AbsoluteEventTable) (x y : Fin 3) (r : Record) (b : Bool) : ℝ :=
  ∑ a : Bool, j.prob (x,y) r (a,b)

/-- Record-revealed TV when Bob's setting is changed while Alice's is fixed. -/
def recordTVAlice (j : AbsoluteEventTable) (x y y' : Fin 3) : ℝ :=
  (∑ r : Record, ∑ a : Bool, |recordAlice j x y r a - recordAlice j x y' r a|) / 2

/-- Record-revealed TV when Alice's setting is changed while Bob's is fixed. -/
def recordTVBob (j : AbsoluteEventTable) (x x' y : Fin 3) : ℝ :=
  (∑ r : Record, ∑ b : Bool, |recordBob j x y r b - recordBob j x' y r b|) / 2

theorem recordTVAlice_nonnegative (j : AbsoluteEventTable) (x y y' : Fin 3) :
    0 ≤ recordTVAlice j x y y' := by
  unfold recordTVAlice
  positivity

theorem recordTVBob_nonnegative (j : AbsoluteEventTable) (x x' y : Fin 3) :
    0 ≤ recordTVBob j x x' y := by
  unfold recordTVBob
  positivity

/-- Conditional locality kills every record-revealed Alice TV exactly. -/
theorem recordTVAlice_zero_of_local (j : AbsoluteEventTable) (hl : LFJoint.Local j)
    (x y y' : Fin 3) : recordTVAlice j x y y' = 0 := by
  simp [recordTVAlice, recordAlice, hl.1]

/-- Conditional locality kills every record-revealed Bob TV exactly. -/
theorem recordTVBob_zero_of_local (j : AbsoluteEventTable) (hl : LFJoint.Local j)
    (x x' y : Fin 3) : recordTVBob j x x' y = 0 := by
  simp [recordTVBob, recordBob, hl.2]

/-- Uniform ceiling on every record-revealed remote-setting comparison. -/
def RecordRevealedWithin (j : AbsoluteEventTable) (delta : ℝ) : Prop :=
  (∀ x y y', recordTVAlice j x y y' ≤ delta) ∧
  (∀ x x' y, recordTVBob j x x' y ≤ delta)

/-- The blind-pair law implies zero record-revealed signaling. -/
theorem local_recordRevealedWithin_zero (j : AbsoluteEventTable) (hl : LFJoint.Local j) :
    RecordRevealedWithin j 0 := by
  constructor
  · intro x y y'
    rw [recordTVAlice_zero_of_local j hl x y y']
  · intro x x' y
    rw [recordTVBob_zero_of_local j hl x x' y]

/-- A lower-bound statement for the full quantum table.  This is a proposition
whose proof is intentionally absent until an exact certificate is checked. -/
def FullTableRecordLowerBound (delta : ℝ) : Prop :=
  ∀ j : AbsoluteEventTable,
    LFJoint.Readable j →
    LFJoint.IndependentRecords j →
    j.behavior = RealQuantum.lfBehavior →
    (∃ x y y', delta ≤ recordTVAlice j x y y') ∨
      ∃ x x' y, delta ≤ recordTVBob j x x' y

namespace NumericalCandidates

/-- Solver-discovered target only.  No theorem in the repository asserts this
is optimal until a rational certificate is imported and kernel-checked. -/
def fullTableRecordTV : ℚ := 63 / 625

/-- Solver-discovered target from the reduced reversible-record score LP. -/
def scoreEightTV : ℚ := 1 / 8

/-- Solver-discovered zero-signaling score ceiling from that same reduced LP. -/
def zeroSignalScore : ℚ := 22 / 3

end NumericalCandidates

/-- The exact theorem shape that would promote the 63/625 numerical candidate
to a trusted result.  At present this is only a named proposition, not a theorem. -/
def FullTableCandidateStatement : Prop :=
  FullTableRecordLowerBound (NumericalCandidates.fullTableRecordTV : ℝ)

end
end OntologySeparation.LFFiniteSpeed
