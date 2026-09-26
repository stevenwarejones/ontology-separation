import OntologySeparation.Experiments.PhaseInterventionExamples

open OntologySeparation PhaseIntervention FiniteModels ExperimentAccess

-- A genuine quantum example with a missed real quadrature and nonzero imaginary one.
example : (behavior imaginarySource.state secondMode plusReadout).prob .zero false =
    (behavior imaginarySource.state secondMode plusReadout).prob .half false :=
  two_phases_can_miss_coherence.1

example : ¬ Equivalent (phasePredictions imaginarySource.state secondMode plusReadout)
    (fun _ => True) true false := by
  rw [full_access_equivalent_iff]
  intro h
  have he := h false
  rw [imaginary_coherence] at he
  norm_num [Complex.ext_iff] at he

example : Equivalent (phasePredictions imaginarySource.state secondMode plusReadout)
    (fun p => p = false) true false := restricted_access_equivalent _ _ _

example : PhaseBlind (behavior imaginarySource.state secondMode (QIT.POVM.coordinate Bool)) :=
  insensitive_readout
example : imaginarySource.state ≠ dephase imaginarySource.state secondMode :=
  insensitive_source_not_dephased

-- Both sides of the sharp calibration boundary, including equality.
example : NearBlind (lossy (4/5) (3/5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) (6/25) :=
  (lossy_nearBlind_iff _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr (by norm_num)

example : ¬ NearBlind (lossy (4/5) (3/5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) (23/100) := by
  rw [lossy_nearBlind_iff _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num

-- An arbitrary state/readout, not a hand-enumerated example, passes the bridge.
example {H O : Type} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]
    (ρ : QIT.State H) (R : Region H) (M : QIT.POVM O H) :
    PhaseBlind (behavior (dephase ρ R) R M) := dephased_blind ρ R M

example (η v : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    ObservationallyEquivalent
      (behavior (visibilityState v hv₀ hv₁) secondMode (inefficientReadout η hη₀ hη₁))
      (lossy η v hη₀ hη₁ hv₀ hv₁) := quantum_realizes_lossy _ _ _ _ _ _

-- The observed estimate remains distinct from a physical probability.
example {O : Type} [Fintype O] (p : Behavior (phaseInterface O)) (δ r : ℝ)
    (estimate : Phase → O → ℝ) (he : ∀ s o, |estimate s o - p.prob s o| ≤ r)
    (s t : Phase) (o : O) (h : 2*δ + 2*r < |estimate s o - estimate t o|) :
    ¬ NearBlind p δ := excludes_nearBlind p δ r estimate he s t o h
