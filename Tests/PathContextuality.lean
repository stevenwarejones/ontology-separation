import OntologySeparation.Experiments.PathContextualityCountermodels

open OntologySeparation OntologySeparation.PathContextuality

example : (1/50 : ℝ) < (16/25) := by norm_num
example : (0 : ℝ) < 297/15625 := by norm_num
example : quantumJoint.prob () (false,true) = 1369/15625 := by
  rw [quantum_realizes_table]
  rfl
example : quantumJoint.prob () (true,false) = 7056/15625 := by
  rw [quantum_realizes_table]
  rfl
example : nullModel.pF = 1/4 := null_nonempty.2.2.1
example : nullModel.pMinus = 1/8 := null_nonempty.2.2.2

-- The bound permits stochastic final responses and every finite ontic size.
example (n : ℕ) (m : Model (Fin n)) (hq : m.ResponseCap (16/25))
    (hd : m.Disturbance (1/50)) (hf : m.pF = 49/625) :
    ¬ ObservationallyEquivalent m.observed quantumJoint := quantum_exclusion m hq hd hf
