import OntologySeparation.Experiments.PathCompatibility
open OntologySeparation OntologySeparation.PathContextuality
example {Λ : Type} [Fintype Λ] (m : Model Λ)
    (hq : m.ResponseCap (16/25)) (hd : m.Disturbance (1/50)) :
    (17/50)*m.pF ≤ m.pPlus := by
  have h := m.positive_bound (16/25) (1/50) (by norm_num) hq hd
  norm_num at h
  exact h

example : ReferenceRegion (16/25) (297/1225) := by norm_num [ReferenceRegion]
example : ¬ ReferenceRegion (16/25) (13/320) := by norm_num [ReferenceRegion]
example : ∃ m : Model Bool, m.ResponseCap (16/25) ∧ m.Disturbance (297/1225) ∧
    m.pF = 49/625 ∧ ObservationallyEquivalent m.observed quantumJoint :=
  reference_disturbance_attained
