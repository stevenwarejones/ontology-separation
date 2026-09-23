import OntologySeparation.Experiments.LFAgencyRelaxationDiagnostics

namespace OntologySeparation.Tests.LFAgencyRelaxation
open OntologySeparation.LFAgencyRelaxation
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
end
end OntologySeparation.Tests.LFAgencyRelaxation
