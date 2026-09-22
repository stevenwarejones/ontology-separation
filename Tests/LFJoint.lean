import OntologySeparation.Assumptions

namespace OntologySeparation.Tests.LFJoint
open OntologySeparation.LFJoint
noncomputable section

def exampleTable : Table := fromOperational LFAssumptionAtlas.prOperational

theorem example_independent : IndependentRecords exampleTable :=
  fromOperational_independent _ (LFAssumptionAtlas.operational_independent _)

example (p : Behavior LF.interface) : theory p ↔ LF.theory p := joint_iff_lf p
example : Admissible exampleTable :=
  ⟨fromOperational_readable _ (LFAssumptionAtlas.operational_readable _),
    fromOperational_local _ (LFAssumptionAtlas.operational_local _)
      (LFAssumptionAtlas.operational_independent _), example_independent⟩

theorem impossible : exampleTable.mass (0,0) (true,false) = 0 := by
  norm_num [exampleTable, fromOperational_mass, LFAssumptionAtlas.prOperational,
    LFAssumptionAtlas.operational, LFAssumptionAtlas.prMixture, LF.prComponent]

example (s : Setting) (o : Outcome) : exampleTable.prob s (true,false) o = 0 :=
  prob_eq_zero_of_mass_zero _ _ _ ((example_independent s (0,0) _).trans impossible) _

example : (conditional exampleTable example_independent (true,false)).prob (0,0) (true,false) = 1 := by
  simp [conditional, impossible, fallback]

-- Impossible events have zero joint mass, not an unnormalized conditional response.
example : True := by
  fail_if_success
    have h : (conditional exampleTable example_independent (true,false)).prob (0,0) (true,false) = 0 := by
      simp [conditional, impossible, fallback]
  trivial

example : ¬ theory RealQuantum.lfBehavior := quantum_excluded
end
end OntologySeparation.Tests.LFJoint
