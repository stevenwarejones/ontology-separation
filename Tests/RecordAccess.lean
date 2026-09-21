import OntologySeparation.Experiments.RecordAccess

open OntologySeparation RecordAccess

example : ¬ Protocol.localOnly (.jointTest recoveryTest) := by simp [Protocol.localOnly]
example : separator.gap = 288 / 625 := rfl
example : ¬ ExperimentAccess.Equivalent predict (fun _ => True) .coherent .dephased :=
  joint_not_equivalent

-- An accessible-only separator would contradict the universally proved equivalence.
example (w : ExperimentAccess.Separator predict Protocol.localOnly .coherent .dephased) :
    False := w.not_equivalent locally_equivalent

-- Every outcome is retained; normalization forbids interpreting successful
-- recovery as a postselected probability of one for both models.
example (law : Law) : ∑ o, recoveryTest.prob law.state o = 1 :=
  recoveryTest.normalized law.state

example : recoveryTest.prob dephased (false,false) ≠ 1 := by
  rw [dephased_recovery]
  norm_num
