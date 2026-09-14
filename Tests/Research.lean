import OntologySeparation.Experiments.Research
import OntologySeparation.Models.DephasedSinglet
import OntologySeparation.Catalog.Evidence
open OntologySeparation

-- Boundary cases exercise the proved parameter families, not a copied result table.
example : ∀ (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
    (2 < Bell.score (DephasedSinglet.behavior Bell.alice Bell.bob p h0 h1) ↔
      p < 7/32) := by
  intro p h0 h1
  exact DephasedSinglet.bell_noise_threshold p h0 h1

example : ∀ d : Bool → Rat, Research.oneBitRecovery d = 1/2 := Research.restricted_recovery
example : Research.jointRecovery xor = 1 := Research.joint_recovery
example : ∀ p : Rat, Research.noisyOrder p (fun b => if b then 0 else 1) = 1-p/2 := by
  intro p
  apply Research.noisy_order_probability
  norm_num [Research.normSq]

-- A required law cannot be replaced by an arbitrary raw Boolean tag.
example {M : Type} (v : Vocabulary M)
    (h : ∀ m, v.realism m → v.globalTruth m) :
    ¬ (AssumptionProfile.mk .require .reject .unspecified .unspecified).Realizable v :=
  inconsistent_profile v h
