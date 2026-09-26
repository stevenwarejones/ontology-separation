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
-- Exercise strict_interval_exclusion at both signed rejection branches.
example (d : ℝ) (h : 2/100 ≤ d ∧ d ≤ 3/100) (hn : |d| ≤ 1/100) : False :=
  strict_interval_exclusion d _ _ _ h hn (Or.inl (by norm_num))
example (d : ℝ) (h : -3/100 ≤ d ∧ d ≤ -2/100) (hn : |d| ≤ 1/100) : False :=
  strict_interval_exclusion d _ _ _ h hn (Or.inr (by norm_num))
-- A covered null at equality cannot satisfy the library's strict trigger.
example (h : (1/100 : ℝ) < 1/100 ∨ (2/100 : ℝ) < -(1/100)) : False :=
  strict_interval_exclusion (1/100) (1/100) (2/100) (1/100)
    (by constructor <;> norm_num) (by norm_num) h
-- Non-strict geometry is insufficient: the endpoint pair is lightlike.
example : (1 : ℝ) * max (1-0) (0-1) ≤ 1 ∧
    ¬ (∀ ta tb : ℝ, 0 ≤ ta ∧ ta ≤ 0 → 1 ≤ tb ∧ tb ≤ 1 → |tb-ta| < 1) := by
  constructor
  · norm_num
  · intro h
    have hpoint := h 0 1 (by norm_num) (by norm_num)
    norm_num at hpoint
-- Applying the actual library theorem to that endpoint forces strict budget failure.
example (hbudget : (1 : ℝ) * max (1-0) (0-1) < 1) : False := by
  have h := spacelike_of_budget 1 1 1 0 0 1 1 0 1
    (by norm_num) le_rfl (by norm_num) (by norm_num) hbudget
  norm_num at h
example : influence dependentPreparation.observed = 1 := dependentPreparation_gap
example : influence dependentReceiver.observed = 1 := dependentReceiver_gap
example : influence postselected = 1 := postselection_counterexample.2.2.2
example : selectedSharedBit.acceptance false = 1/2 := selectedSharedBit_acceptance _
