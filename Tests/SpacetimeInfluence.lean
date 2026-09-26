import OntologySeparation.Experiments.SpacetimeInfluenceBounds

open OntologySeparation SpacetimeInfluence

example : influence sharedBit.observed = 0 := sharedBit.no_influence
example : influence (alternative (3/100) (by norm_num) (by norm_num)) = 3/100 :=
  alternative_gap _ _ _
example : influence (alternative 0 (by norm_num) (by norm_num)) = 0 :=
  alternative_gap _ _ _
example : influence (alternative 1 (by norm_num) (by norm_num)) = 1 :=
  alternative_gap _ _ _
example : ¬ ObservationallyEquivalent sharedBit.observed
    (alternative (3/100) (by norm_num) (by norm_num)) :=
  alternative_excluded _ (by norm_num) (by norm_num) sharedBit
example : ExperimentAccess.Equivalent receiverPredictions (fun _ => True) true false :=
  receiver_access_equivalent
example (p0 p1 : ℝ) (h0 : |p0-1/2| ≤ 1/1000) (h1 : |p1-1/2| ≤ 1/1000) :
    |p1-p0| ≤ 2/1000 := by
  have h := calibrated_gap p0 p1 (1/2) (1/1000) (1/1000) h0 h1
  linarith
example (ta tb : ℝ) (ha : -5 ≤ ta ∧ ta ≤ 20) (hb : 35 ≤ tb ∧ tb ≤ 65) :
    (299792458/1000000000 : ℝ)*|tb-ta| < 289/10 :=
  spacelike_of_budget _ _ _ _ _ _ _ _ _ (by norm_num) le_rfl ha hb (by norm_num)
-- Equality is not spacelike and not a strict statistical rejection.
example : ¬ ((299792458/1000000000 : ℝ)*70 < 299792458/1000000000*70) := lt_irrefl _
example : ¬ ((1/100 : ℝ) < 1/100) := lt_irrefl _
