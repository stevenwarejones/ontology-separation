import Study
open OntologySeparation MyLaboratory
example : bellBound.kind = "realizedBound" := rfl
example : singletExcluded.kind = "exclusion" := rfl
example : bellBound.statement := bellBound.sound
example : singletExcluded.statement := singletExcluded.sound
-- A class bound cannot be relabeled as an exact prediction without a new equality proof.
example : True := by
  fail_if_success
    have wrong : Bell.score ClassicalWorld.constantWorld.operational.behavior = (0 : ℝ) :=
      ClassicalWorld.chsh_bound ClassicalWorld.constantWorld
  trivial
