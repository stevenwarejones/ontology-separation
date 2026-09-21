import OntologySeparation.Recipes.LocalFriendliness

namespace OntologySeparation.LocalFriendlinessRecipe
open TwoQubit

/-- The source is a singlet expressed in the friends' local measurement frames. -/
theorem reference_source : reference.source =
    (Pure.of 0 1 (-1) 0).gate (.readBasis .bob (.of 4 (-3))) := by
  ext <;> norm_num [reference, Pure.of, Pure.gate, Gate.apply, Basis.of]

set_option maxHeartbeats 1600000 in
/-- All 36 probabilities of the actual read/reverse protocol match the LF witness. -/
theorem matches_reference (xy : Fin 3 × Fin 3) (ab : Bool × Bool) :
    (interpret Law.coherent reference).prob xy ab = RealQuantum.lfBehavior.prob xy ab := by
  obtain ⟨x,y⟩ := xy
  obtain ⟨a,b⟩ := ab
  fin_cases x <;> fin_cases y <;> cases a <;> cases b <;>
    norm_num [interpret, probability_correct, probability, recorded, Alternatives.choice,
      FriendProtocol.Choice.basis, reference, readout, State.dephase, State.gate,
      State.probability, Pure.probability, Pure.gate, Pure.of, Gate.apply,
      Amplitudes.entry, Amplitudes.normSq, Basis.of, Basis.z, Law.coherent,
      Recipes.Rate.of, RealQuantum.lfBehavior, RealQuantum.behavior, RealQuantum.probability,
      RealQuantum.Basis.vector, RealQuantum.lfAlice, RealQuantum.lfBob,
      RealQuantum.basis35, RealQuantum.basis45, RealQuantum.basis1517, RealQuantum.zBasis]

theorem reference_behavior : interpret Law.coherent reference = RealQuantum.lfBehavior := by
  have hp : (interpret Law.coherent reference).prob = RealQuantum.lfBehavior.prob := by
    funext xy ab; exact matches_reference xy ab
  cases h1 : interpret Law.coherent reference
  cases h2 : RealQuantum.lfBehavior
  simp only [h1, h2] at hp
  cases hp
  rfl

theorem coherent_score : score Law.coherent reference = 1214656/180625 := by
  have h := RealQuantum.lfBehavior_value
  rw [← reference_behavior, score_correct] at h
  have hq : (score Law.coherent reference : ℝ) = ((1214656/180625 : ℚ) : ℝ) := by
    norm_num
    exact h
  exact_mod_cast hq

theorem coherent_excludes_LF : ¬ LF.theory (interpret Law.coherent reference) :=
  excludes_LF _ _ (by rw [coherent_score]; norm_num)

theorem coherent_excludes_profile {Λ : Type} [Fintype Λ] :
    ¬ profileTheory (FriendRecords.vocabulary (Λ := Λ)) FriendRecords.profile
      FriendRecords.Model.behavior (interpret Law.coherent reference) :=
  excludes_profile _ _ (by rw [coherent_score]; norm_num)

/-- Charlie-record dephasing has an exact affine effect; Debbie stays coherent. -/
theorem charlie_noise_score (p : Recipes.Rate) :
    score ⟨p, Recipes.Rate.of 0⟩ reference = (1214656 - 476928*p.value)/180625 := by
  lf_check
  ring

theorem charlie_noise_threshold (p : Recipes.Rate) :
    6 < score ⟨p, Recipes.Rate.of 0⟩ reference ↔ p.value < 65453/238464 := by
  rw [charlie_noise_score]
  constructor <;> intro h <;> linarith

private def product (l : Bool × Bool) : Pure :=
  match l with
  | (false,false) => .of 1 0 0 0
  | (false,true) => .of 0 1 0 0
  | (true,false) => .of 0 0 1 0
  | (true,true) => .of 0 0 0 1

/-- An explicit classical record model for the fully dephased reference experiment. -/
noncomputable def classicalRecords : FriendRecords.Model (Bool × Bool) where
  preparation _ :=
    { mass := fun l => (reference.source.probability l : ℝ)
      nonneg := fun l => by exact_mod_cast reference.source.nonneg l
      total := by
        have h := reference.source.normalized
        simpa only [Fintype.sum_prod_type, Fintype.sum_bool, Rat.cast_add, Rat.cast_one] using
          congrArg (fun q : ℚ => (q : ℝ)) h }
  response l := interpret Law.coherent { reference with source := product l }
  charlie := Prod.fst
  debbie := Prod.snd

theorem classical_readable : FriendRecords.ReadableRecords classicalRecords := by
  constructor
  · intro l y
    obtain ⟨a,b⟩ := l
    cases a <;> cases b <;> fin_cases y <;>
      norm_num [classicalRecords, interpret, probability_correct, probability, recorded,
        Alternatives.choice, FriendProtocol.Choice.basis, reference, readout,
        State.dephase, State.gate, State.probability, Pure.probability, Pure.gate,
        Pure.of, Gate.apply, Amplitudes.entry, Amplitudes.normSq, Basis.of, Basis.z,
        Law.coherent, Recipes.Rate.of, product]
  · intro l x
    obtain ⟨a,b⟩ := l
    cases a <;> cases b <;> fin_cases x <;>
      norm_num [classicalRecords, interpret, probability_correct, probability, recorded,
        Alternatives.choice, FriendProtocol.Choice.basis, reference, readout,
        State.dephase, State.gate, State.probability, Pure.probability, Pure.gate,
        Pure.of, Gate.apply, Amplitudes.entry, Amplitudes.normSq, Basis.of, Basis.z,
        Law.coherent, Recipes.Rate.of, product]

theorem classical_local : FriendRecords.ConditionalLocality classicalRecords :=
  fun _ => no_signaling _ _
theorem classical_independent : FriendRecords.IndependentPreparation classicalRecords :=
  fun _ _ _ => rfl

set_option maxHeartbeats 1600000 in
theorem fully_dephased_matches (xy : Fin 3 × Fin 3) (ab : Bool × Bool) :
    (interpret (Law.recordDephasing 1 1 1) reference).prob xy ab =
      classicalRecords.behavior.prob xy ab := by
  obtain ⟨x,y⟩ := xy
  obtain ⟨a,b⟩ := ab
  fin_cases x <;> fin_cases y <;> cases a <;> cases b <;>
    norm_num [FriendRecords.Model.behavior, classicalRecords, interpret,
      probability_correct, probability, recorded, Alternatives.choice,
      FriendProtocol.Choice.basis, reference, readout, State.dephase, State.gate,
      State.probability, Pure.probability, Pure.gate, Pure.of, Gate.apply,
      Amplitudes.entry, Amplitudes.normSq, Basis.of, Basis.z, Law.coherent,
      Law.recordDephasing, Recipes.Rate.of, Recipes.Rate.fraction, product,
      Fintype.sum_prod_type]

theorem fully_dephased_behavior : interpret (Law.recordDephasing 1 1 1) reference =
    classicalRecords.behavior := by
  have hp : (interpret (Law.recordDephasing 1 1 1) reference).prob =
      classicalRecords.behavior.prob := by
    funext xy ab; exact fully_dephased_matches xy ab
  cases h1 : interpret (Law.recordDephasing 1 1 1) reference
  cases h2 : classicalRecords.behavior
  simp only [h1, h2] at hp
  cases hp
  rfl

theorem fully_dephased_realizes_profile :
    profileTheory (FriendRecords.vocabulary (Λ := Bool × Bool)) FriendRecords.profile
      FriendRecords.Model.behavior (interpret (Law.recordDephasing 1 1 1) reference) := by
  rw [fully_dephased_behavior]
  exact ⟨classicalRecords, ⟨trivial, classical_readable, classical_local, classical_independent⟩, rfl⟩

end OntologySeparation.LocalFriendlinessRecipe
