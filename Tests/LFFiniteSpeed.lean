import OntologySeparation.Experiments.LFFiniteSpeed

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

end
end OntologySeparation.Tests.LFFiniteSpeed
