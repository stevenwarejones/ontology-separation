import OntologySeparation.Experiments.LocalPhase

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

-- Normalization obstructs a common three-outcome behavior despite passing all pairs.
example : ¬ NearBlind triangle (3/5) := by
  rw [triangle_nearBlind_iff]
  norm_num
example : ∀ s t o, |triangle.prob s o - triangle.prob t o| ≤ 2*(3/5) := by
  intro s t o
  have h := triangle_pairwise (1/10) (by norm_num) s t o
  norm_num at h ⊢
  exact h
example : LocalCompatible (lossy 1 (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) (1/2) := boundary_nonempty
example : ¬ LocalCompatible (lossy 1 (3/5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) (1/2) := explicit_quantum_violation
-- Low efficiency can keep even unit visibility inside the local class.
example : LocalCompatible (lossy (2/5) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) (1/2) := by
  rw [lossy_local_iff]
  norm_num

-- The three dropped-premise constructions apply to the violating quantum table.
example : (allInP (lossy 1 (3/5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num))).occupation = 1 := (drop_occupation _).1
example : ∃ μ : FiniteDistribution (Fin 2),
    (∑ l : Fin 2, if l.val = 0 then μ.mass l else 0) = 1/2 ∧
    ObservationallyEquivalent (mixture (fun _ =>
      lossy 1 (3/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) μ)
      (lossy 1 (3/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :=
  drop_locality _
example : (settingPreparation (lossy 1 (3/5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) .zero).mass (false, 0) ≠
    (settingPreparation (lossy 1 (3/5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) .half).mass (false, 0) := by
  norm_num [settingPreparation, lossy, fringe]
