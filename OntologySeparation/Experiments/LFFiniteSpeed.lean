import OntologySeparation.Experiments.LFJoint
import OntologySeparation.Adapters.Shared

/-!
# Local-Agency relaxation with unread friend records

This module isolates a Local-Agency relaxation in the standard two-laboratory
Local Friendliness experiment.  Finite-speed hidden influences motivated the
question, but the formal statement below is not a finite-speed theorem.

The setup keeps absolute friend records and asks what follows when the late
Alice/Bob responses are conditionally local at fixed records.  In the existing
joint-event language this is exactly `LFJoint.Local`.

The useful negative result is that unread/reversible friend records can hide
conditional dependence that is absent from the public Alice/Bob marginals.  Thus
this module should be read as a relaxation/diagnostic for Local Agency, not as a
Bancal-style finite-speed operational-signaling theorem.
-/

namespace OntologySeparation.LFFiniteSpeed
noncomputable section

open LFJoint

/-- AOE is represented by one joint table over the two friend records and the
two Wigner outcomes for every Wigner setting pair. -/
abbrev AbsoluteEventTable := LFJoint.Table

/-- Geometric content of the finite-speed layout after Alice and Bob have been
placed outside one another's v-cones: at fixed absolute friend records, neither
late choice changes the other late marginal. -/
def BlindLatePair (j : AbsoluteEventTable) : Prop := LFJoint.Local j

/-- The first-pass finite-speed LF class: exact friend readout (AOE records are
operationally recoverable), no-superdeterministic record preparation, and a
late pair that is blind at the chosen finite influence speed. -/
def Compatible (j : AbsoluteEventTable) : Prop :=
  LFJoint.Readable j ∧ BlindLatePair j ∧ LFJoint.IndependentRecords j

/-- Observable behaviors admitting the finite-speed/AOE joint extension for the
blind-pair layout. -/
def theory (p : Behavior LF.interface) : Prop :=
  ∃ j : AbsoluteEventTable, Compatible j ∧ j.behavior = p

theorem compatible_iff_admissible (j : AbsoluteEventTable) :
    Compatible j ↔ LFJoint.Admissible j := by
  rfl

theorem theory_iff_joint (p : Behavior LF.interface) :
    theory p ↔ LFJoint.theory p := by
  rfl

/-- The blind-pair finite-speed specialization has exactly the genuine LF
ceiling. No numerical optimizer is trusted here. -/
theorem bound (j : AbsoluteEventTable) (h : Compatible j) :
    RealQuantum.genuineLF j.behavior ≤ 6 := by
  exact LFJoint.bound j h

/-- Exact violation margin of the rational singlet witness used by the project. -/
theorem quantum_gap :
    RealQuantum.genuineLF RealQuantum.lfBehavior - 6 = (130906 : ℝ) / 180625 := by
  rw [RealQuantum.lfBehavior_value]
  norm_num

theorem quantum_gap_positive :
    0 < RealQuantum.genuineLF RealQuantum.lfBehavior - 6 := by
  rw [quantum_gap]
  norm_num

/-- The public quantum LF behavior is exactly no-signaling. This matters:
failure of the blind-pair hidden condition is not itself an operational signal. -/
theorem quantum_public_noSignaling :
    Shared.NoSignaling RealQuantum.lfBehavior := by
  exact Shared.singlet_noSignaling RealQuantum.lfAlice RealQuantum.lfBob

/-- No AOE + exact-readout + setting-independent-record model with a finite-speed
blind late pair reproduces the project quantum LF target. -/
theorem quantum_excluded : ¬ theory RealQuantum.lfBehavior := by
  rw [theory_iff_joint]
  exact LFJoint.quantum_excluded

/-- The cheapest feasibility test in one theorem: the quantum target is publicly
no-signaling but has no compatible blind-pair finite-speed AOE extension. -/
theorem feasibility :
    Shared.NoSignaling RealQuantum.lfBehavior ∧
      ¬ ∃ j : AbsoluteEventTable, Compatible j ∧ j.behavior = RealQuantum.lfBehavior := by
  exact ⟨quantum_public_noSignaling, quantum_excluded⟩

end
end OntologySeparation.LFFiniteSpeed
