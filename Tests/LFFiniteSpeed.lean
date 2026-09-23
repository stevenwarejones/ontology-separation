import OntologySeparation.Experiments.LFFiniteSpeedDiagnostics

namespace OntologySeparation.Tests.LFFiniteSpeed
open OntologySeparation.LFFiniteSpeed
noncomputable section

example : Shared.NoSignaling RealQuantum.lfBehavior :=
  quantum_public_noSignaling

example :
    RealQuantum.genuineLF RealQuantum.lfBehavior - 6 = (130906 : ℝ) / 180625 :=
  quantum_gap

example : ¬ theory RealQuantum.lfBehavior :=
  quantum_excluded

example :
    Shared.NoSignaling RealQuantum.lfBehavior ∧
      ¬ ∃ j : AbsoluteEventTable, Compatible j ∧ j.behavior = RealQuantum.lfBehavior :=
  feasibility

example (j : AbsoluteEventTable) (hl : LFJoint.Local j) :
    RecordRevealedWithin j 0 :=
  local_recordRevealedWithin_zero j hl

example : NumericalCandidates.fullTableRecordTV = (63 : ℚ) / 625 := rfl
example : NumericalCandidates.scoreEightTV = (1 : ℚ) / 8 := rfl
example : NumericalCandidates.zeroSignalScore = (22 : ℚ) / 3 := rfl

-- Deliberately no example of FullTableCandidateStatement: that proposition
-- remains unproved until an exact rational certificate is checked in Lean.
end
end OntologySeparation.Tests.LFFiniteSpeed
