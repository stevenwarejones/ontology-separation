import OntologySeparation.Experiments.PhaseInterventionGeometry

/-! Definite-region response models with arbitrary phase action on the occupied
arm and invariant response on its complement. Occupation matching is a separate
premise relating the interference and which-region measurement contexts. -/
namespace OntologySeparation.PhaseIntervention
noncomputable section
open FiniteModels

structure LocalPhaseModel (Λ O : Type) [Fintype Λ] [Fintype O] where
  preparation : FiniteDistribution Λ
  inP : Λ → Bool
  response : Λ → Behavior (phaseInterface O)
  localQ : ∀ l, inP l = false → PhaseBlind (response l)

namespace LocalPhaseModel
variable {Λ O : Type} [Fintype Λ] [Fintype O]
def observed (m : LocalPhaseModel Λ O) := mixture m.response m.preparation
def occupation (m : LocalPhaseModel Λ O) : ℝ :=
  ∑ l, if m.inP l then m.preparation.mass l else 0

theorem contrast_identity (m : LocalPhaseModel Λ O) (s t : Phase) (o : O) :
    (m.observed).prob s o - (m.observed).prob t o =
      ∑ l, if m.inP l then m.preparation.mass l *
        ((m.response l).prob s o - (m.response l).prob t o) else 0 := by
  simp only [observed, mixture, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  cases h : m.inP l
  · simp [m.localQ l h s t o]
  · simp; ring

theorem contrast_le_occupation (m : LocalPhaseModel Λ O) (s t : Phase) (o : O) :
    |m.observed.prob s o - m.observed.prob t o| ≤ m.occupation := by
  have upper (s t : Phase) : m.observed.prob s o - m.observed.prob t o ≤ m.occupation := by
    rw [contrast_identity]
    apply Finset.sum_le_sum
    intro l _
    cases h : m.inP l
    · simp
    · simp only [↓reduceIte]
      have h₁ := (m.response l).prob_le_one s o
      have h₂ := (m.response l).nonneg t o
      have hμ := m.preparation.nonneg l
      nlinarith
  apply abs_le.mpr
  constructor <;> linarith [upper s t, upper t s]

/-- Calibration δ bounds each outcome against an ideal local-phase model;
r bounds estimates of the actual behavior; rw bounds the occupation estimate. -/
theorem robust_bound (m : LocalPhaseModel Λ O) (p : Behavior (phaseInterface O))
    (δ r wHat rw : ℝ) (estimate : Phase → O → ℝ)
    (hcal : ∀ s o, |p.prob s o - m.observed.prob s o| ≤ δ)
    (hstat : ∀ s o, |estimate s o - p.prob s o| ≤ r)
    (hw : |m.occupation - wHat| ≤ rw) (s t : Phase) (o : O) :
    |estimate s o - estimate t o| ≤ wHat + rw + 2*δ + 2*r := by
  obtain ⟨ha, hb⟩ := abs_le.mp (m.contrast_le_occupation s t o)
  obtain ⟨hc, hd⟩ := abs_le.mp (hcal s o)
  obtain ⟨he, hf⟩ := abs_le.mp (hcal t o)
  obtain ⟨hg, hh⟩ := abs_le.mp (hstat s o)
  obtain ⟨hi, hj⟩ := abs_le.mp (hstat t o)
  obtain ⟨hk, hl⟩ := abs_le.mp hw
  apply abs_le.mpr
  constructor <;> linarith

/-- Two arm placements bound one common contrast only if their observable
contrasts are identified, and their occupations are complementary. -/
theorem either_arm {Λ' : Type} [Fintype Λ'] (mP : LocalPhaseModel Λ O)
    (mQ : LocalPhaseModel Λ' O) (hocc : mQ.occupation = 1-mP.occupation)
    (s t u v : Phase) (o : O)
    (hcommon : |mP.observed.prob s o - mP.observed.prob t o| =
      |mQ.observed.prob u o - mQ.observed.prob v o|) :
    |mP.observed.prob s o - mP.observed.prob t o| ≤ min mP.occupation (1-mP.occupation) := by
  apply le_min
  · exact mP.contrast_le_occupation s t o
  · rw [hcommon, ← hocc]
    exact mQ.contrast_le_occupation u v o
end LocalPhaseModel

/-- Whole-table compatibility, allowing any finite hidden-variable space. -/
def LocalCompatible {O : Type} [Fintype O] (p : Behavior (phaseInterface O)) (w : ℝ) : Prop :=
  ∃ (n : ℕ) (m : LocalPhaseModel (Fin n) O), m.occupation = w ∧
    ObservationallyEquivalent m.observed p

theorem localCompatible_bound {O : Type} [Fintype O]
    (p : Behavior (phaseInterface O)) (w : ℝ) (h : LocalCompatible p w)
    (s t : Phase) (o : O) : |p.prob s o - p.prob t o| ≤ w := by
  obtain ⟨n, m, hw, hp⟩ := h
  simpa only [hp s o, hp t o, hw] using m.contrast_le_occupation s t o

/-- Balanced preparation really has quantum which-region probability one half. -/
theorem visibility_occupation (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    ((secondMode.projector * (visibilityState v hv₀ hv₁).matrix).trace).re = 1/2 := by
  norm_num [secondMode, visibilityState, plusReadout, QIT.rankOneMatrix,
    Matrix.vecMulVec, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Fintype.sum_bool]
  ring

theorem lossy_local_necessary (η v : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1)
    (h : LocalCompatible (lossy η v hη₀ hη₁ hv₀ hv₁) (1/2)) : η*v ≤ 1/2 := by
  have hb := localCompatible_bound _ _ h .zero .half 0
  rw [lossy_contrast, abs_of_nonneg (mul_nonneg hη₀ hv₀)] at hb
  exact hb

theorem explicit_quantum_violation :
    ¬ LocalCompatible (lossy 1 (3/5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) (1/2) := by
  intro h
  have hb := lossy_local_necessary _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h
  norm_num at hb

/-- Equal occupation in two regions; the P response is arbitrary and Q is fixed. -/
def balancedModel {O : Type} [Fintype O] (p q : Behavior (phaseInterface O))
    (hq : PhaseBlind q) : LocalPhaseModel (Fin 2) O where
  preparation := ⟨fun _ => 1/2, by intro l; norm_num, by norm_num⟩
  inP l := l.val == 0
  response l := if l.val = 0 then p else q
  localQ l hl := by
    fin_cases l
    · simp at hl
    · simpa using hq

theorem balanced_occupation {O : Type} [Fintype O]
    (p q : Behavior (phaseInterface O)) (hq : PhaseBlind q) :
    (balancedModel p q hq).occupation = 1/2 := by
  norm_num [balancedModel, LocalPhaseModel.occupation, Fin.sum_univ_two]

theorem balanced_probability {O : Type} [Fintype O]
    (p q : Behavior (phaseInterface O)) (hq : PhaseBlind q) (s : Phase) (o : O) :
    (balancedModel p q hq).observed.prob s o = (p.prob s o + q.prob s o)/2 := by
  norm_num [balancedModel, LocalPhaseModel.observed, mixture, Fin.sum_univ_two]
  ring

/-- Every table in the lossy family below the boundary has a finite local model.
The construction uses a blind Q branch and an arbitrary P branch, each of weight 1/2. -/
theorem lossy_local_iff (η v : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    LocalCompatible (lossy η v hη₀ hη₁ hv₀ hv₁) (1/2) ↔ η*v ≤ 1/2 := by
  constructor
  · exact lossy_local_necessary η v hη₀ hη₁ hv₀ hv₁
  · intro hbound
    by_cases he : η ≤ 1/2
    · let p := lossy (2*η) v (by positivity) (by linarith) hv₀ hv₁
      let q := lossy 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hq : PhaseBlind q := by intro s t o; simp [q, lossy]
      refine ⟨2, balancedModel p q hq, balanced_occupation p q hq, ?_⟩
      intro s o
      rw [balanced_probability]
      fin_cases o <;> norm_num [p, q, lossy] <;> ring
    · let p := lossy 1 (2*η*v) (by norm_num) (by norm_num)
        (by positivity) (by linarith)
      let q := lossy (2*η-1) 0 (by linarith) (by linarith) (by norm_num) (by norm_num)
      have hq : PhaseBlind q := by intro s t o; simp [q, lossy]
      refine ⟨2, balancedModel p q hq, balanced_occupation p q hq, ?_⟩
      intro s o
      rw [balanced_probability]
      fin_cases o <;> norm_num [p, q, lossy] <;> ring

/-- The null is nonempty even at the sharp boundary, with nonzero interference. -/
theorem boundary_nonempty :
    LocalCompatible (lossy 1 (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) (1/2) := by
  rw [lossy_local_iff]
  norm_num

/-- Without occupation matching any target is realizable: all preparation weight is in P. -/
def allInP {O : Type} [Fintype O] (p : Behavior (phaseInterface O)) :
    LocalPhaseModel (Fin 1) O where
  preparation := ⟨fun _ => 1, by intro l; norm_num, by simp⟩
  inP _ := true
  response _ := p
  localQ _ h := by simp at h

theorem drop_occupation {O : Type} [Fintype O] (p : Behavior (phaseInterface O)) :
    (allInP p).occupation = 1 ∧ ObservationallyEquivalent (allInP p).observed p := by
  constructor
  · simp [allInP, LocalPhaseModel.occupation]
  · intro s o; simp [allInP, LocalPhaseModel.observed, mixture]

/-- Keeping occupation 1/2 and a fixed preparation but dropping locality permits
both regions to use the target response table. -/
theorem drop_locality {O : Type} [Fintype O] (p : Behavior (phaseInterface O)) :
    ∃ μ : FiniteDistribution (Fin 2),
      (∑ l : Fin 2, if l.val = 0 then μ.mass l else 0) = 1/2 ∧
      ObservationallyEquivalent (mixture (fun _ => p) μ) p := by
  refine ⟨⟨fun _ => 1/2, by intro l; norm_num, by norm_num⟩, ?_, ?_⟩
  · norm_num [Fin.sum_univ_two]
  · intro s o
    norm_num [mixture, Fin.sum_univ_two]
    ring

/-- A fixed deterministic outcome response, blind in both regions. -/
def predetermined {O : Type} [Fintype O] [DecidableEq O] (o : O) :
    Behavior (phaseInterface O) where
  prob _ b := if b = o then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  normalized _ := by simp

/-- Setting-dependent preparation on region × outcome, with equal occupation
at every setting. Responses themselves remain entirely phase-blind. -/
def settingPreparation {O : Type} [Fintype O] (p : Behavior (phaseInterface O))
    (s : Phase) : FiniteDistribution (Bool × O) where
  mass l := p.prob s l.2 / 2
  nonneg l := div_nonneg (p.nonneg s l.2) (by norm_num)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, ← Finset.sum_div, p.normalized]
    norm_num

theorem drop_setting_independence {O : Type} [Fintype O] [DecidableEq O]
    (p : Behavior (phaseInterface O)) :
    (∀ s, (∑ l : Bool × O, if l.1 then (settingPreparation p s).mass l else 0) = 1/2) ∧
    (∀ l : Bool × O, PhaseBlind (predetermined l.2)) ∧
    (∀ s o, (mixture (fun l : Bool × O => predetermined l.2)
      (settingPreparation p s)).prob s o = p.prob s o) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    simp [settingPreparation, Fintype.sum_prod_type,
      ← Finset.sum_div, p.normalized]
  · intro l s t o; rfl
  · intro s o
    simp [mixture, settingPreparation, predetermined, Fintype.sum_prod_type]
    ring

/-- A strict calibrated contrast violation excludes every model satisfying
occupation calibration, local action and setting-independent preparation. -/
theorem excludes_local {O : Type} [Fintype O]
    (p : Behavior (phaseInterface O)) (δ r wHat rw : ℝ) (estimate : Phase → O → ℝ)
    (s t : Phase) (o : O)
    (hgap : wHat + rw + 2*δ + 2*r < |estimate s o - estimate t o|) :
    ¬ ∃ (n : ℕ) (m : LocalPhaseModel (Fin n) O),
      (∀ u b, |p.prob u b - m.observed.prob u b| ≤ δ) ∧
      (∀ u b, |estimate u b - p.prob u b| ≤ r) ∧ |m.occupation-wHat| ≤ rw := by
  rintro ⟨n, m, hc, hs, hw⟩
  exact (not_le_of_gt hgap) (m.robust_bound p δ r wHat rw estimate hc hs hw s t o)

end
end OntologySeparation.PhaseIntervention
