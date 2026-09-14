import OntologySeparation

open OntologySeparation

-- Invalid probabilities are excluded by the interface, rather than tolerated by the UI.
example {E : Interface} (p : Behavior E) (s : E.Setting) (o : E.Outcome) :
    ¬ (1 < p.prob s o) := not_lt_of_ge (p.prob_le_one s o)

-- A probability distribution on an empty outcome space is impossible.
example : ¬ Nonempty (Behavior ({ Setting := Unit, Outcome := Fin 0 } : Interface)) := by
  rintro ⟨p⟩
  have h := p.normalized ()
  simp at h

-- All binary combinations can be written; this is not a realizability theorem.
example : binaryProfiles.length = 16 := binaryProfiles_count

-- Explicit negation differs from simply dropping a hypothesis.
example : Stance.unspecified.Holds False := unspecified_is_unconstrained False
example : ¬ Stance.require.Holds False := fun h => h

-- A separation through the generic API actually excludes the alternative witness.
example : ¬ Bell.localTheory Bell.singletBehavior := Bell.quantumSeparation.excludes
example : ¬ LF.theory RealQuantum.lfBehavior := LF.quantumSeparation.excludes

-- Negative-control physics: leakage makes all dephasing strengths agree.
example : Memory.probability Memory.unitary Memory.leakedEcho =
    Memory.probability Memory.collapse Memory.leakedEcho :=
  Memory.leakedEcho_indistinguishable _ _

-- Same core supports an unrelated vocabulary; conflicting predicates yield empty profiles.
def toyVocabulary : Vocabulary Bool :=
  ⟨fun b => b = true, fun b => b = true, fun _ => True, fun _ => True⟩
example : ¬ (AssumptionProfile.mk .require .reject .unspecified .unspecified).Realizable
    toyVocabulary := inconsistent_profile toyVocabulary (fun _ h => h)

-- A real profile has a separately supplied witness.
example : (AssumptionProfile.mk .require .require .require .require).Realizable toyVocabulary :=
  ⟨true, rfl, rfl, True.intro, True.intro⟩
