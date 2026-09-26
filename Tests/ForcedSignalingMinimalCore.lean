import OntologySeparation.Experiments.ForcedSignalingLC4MinimalCore

namespace OntologySeparation.Tests.ForcedSignalingMinimalCore
open ForcedSignalingAssumptionCore ForcedSignalingLC4MinimalCore AdversarySearch

example (law : Assumption) :
    ∃ m, Satisfies Holds (core.erase law) m ∧ Target m ∧ ¬ Holds law m :=
  deletion_witness law

example : ¬ Independent (dependent quantumLaw) := by
  intro h
  exact excludes _ h (dependent_retained _).1 (dependent_retained _).2
    ⟨quantum_matches, quantum_zero_signal⟩

example : ¬ LocalResponses (jointResponse quantumLaw) := by
  intro h
  exact excludes _ (jointResponse_retained _).1 h (jointResponse_retained _).2
    ⟨quantum_matches, quantum_zero_signal⟩

example : ¬ Unfiltered (filtered quantumLaw) := by
  intro h
  exact excludes _ (filtered_retained _).1 (filtered_retained _).2 h
    ⟨quantum_matches, quantum_zero_signal⟩

example (s : Input) : (filtered quantumLaw).rate s = 1/16 := rfl

example (extra : Mechanism HiddenInfluence.VisibleOutcome → Prop) :
    ¬ Nonempty (MinimalCore
      (fun law : Option Assumption => match law with | none => extra | some k => Holds k)
      Target Finset.univ) := no_fourth_premise_core extra

end OntologySeparation.Tests.ForcedSignalingMinimalCore
