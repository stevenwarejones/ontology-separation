import OntologySeparation.Experiments.PhaseIntervention
import OntologySeparation.Core.Channels

/-! Observable model classes and deterministic uncertainty propagation for the
four-phase intervention. A confidence radius must be justified independently;
these theorems do not turn estimates into true probabilities. -/
namespace OntologySeparation.PhaseIntervention
noncomputable section
open FiniteModels ExperimentAccess
variable {O G : Type} [Fintype O] [Fintype G]

abbrev phaseInterface (O : Type) [Fintype O] : Interface :=
  { Setting := Phase, Outcome := O }

/-- A fixed full outcome distribution, including any losses, across phase settings. -/
def PhaseBlind (p : Behavior (phaseInterface O)) : Prop :=
  ∀ s t o, p.prob s o = p.prob t o

theorem dephased_blind {H : Type} [Fintype H] [DecidableEq H] [DecidableEq O]
    (ρ : QIT.State H) (R : Region H) (M : QIT.POVM O H) :
    PhaseBlind (behavior (dephase ρ R) R M) := by
  intro s t o
  rw [dephased_probability, dephased_probability]

/-- At this fixed detector family, four phases distinguish the original state
from its regional dephasing exactly when some measured cross term is nonzero. -/
theorem coherent_eq_dephased_iff {H : Type} [Fintype H] [DecidableEq H] [DecidableEq O]
    (ρ : QIT.State H) (R : Region H) (M : QIT.POVM O H) :
    ObservationallyEquivalent (behavior ρ R M) (behavior (dephase ρ R) R M) ↔
      ∀ o, coherence ρ R (M.effects o) = 0 := by
  constructor
  · intro h o
    apply (zero_contrasts_iff ρ R M o).mp
    constructor
    · rw [h .zero o, h .half o, dephased_probability, dephased_probability]
    · rw [h .quarter o, h .threeQuarter o, dephased_probability, dephased_probability]
  · intro h s o
    rw [probability_formula, h o, dephased_probability, QIT.POVM.prob_eq_trace_re]
    simp [baseline, dephase]

/-- Access false applies regional dephasing before the phase setting; access true
retains the input. Both laws use the same intervention and detector. -/
def phasePredictions {H : Type} [Fintype H] [DecidableEq H] [DecidableEq O]
    (ρ : QIT.State H) (R : Region H) (M : QIT.POVM O H) :
    Predictions Bool Bool (phaseInterface O) := fun coherentLaw retain =>
  behavior (if coherentLaw && retain then ρ else dephase ρ R) R M

theorem restricted_access_equivalent {H : Type} [Fintype H] [DecidableEq H]
    [DecidableEq O] (ρ : QIT.State H) (R : Region H) (M : QIT.POVM O H) :
    Equivalent (phasePredictions ρ R M) (fun retain => retain = false) true false := by
  intro p hp s o
  subst p
  rfl

theorem full_access_equivalent_iff {H : Type} [Fintype H] [DecidableEq H]
    [DecidableEq O] (ρ : QIT.State H) (R : Region H) (M : QIT.POVM O H) :
    Equivalent (phasePredictions ρ R M) (fun _ => True) true false ↔
      ∀ o, coherence ρ R (M.effects o) = 0 := by
  constructor
  · intro h
    exact (coherent_eq_dephased_iff ρ R M).mp (h true trivial)
  · intro h p _ s o
    cases p
    · rfl
    · exact (coherent_eq_dephased_iff ρ R M).mpr h s o

/-- Mixture weights are independent of the chosen setting. -/
theorem mixture_blind (g : G → Behavior (phaseInterface O))
    (h : ∀ k, PhaseBlind (g k)) (w : FiniteDistribution G) :
    PhaseBlind (mixture g w) := by
  intro s t o
  simp only [mixture]
  exact Finset.sum_congr rfl fun k _ => by rw [h k s t o]

/-- A classical outcome map fixed across settings cannot create phase dependence. -/
def postprocess {O' : Type} [Fintype O'] (p : Behavior (phaseInterface O))
    (channel : Channel O O') : Behavior (phaseInterface O') where
  prob s b := ∑ a, p.prob s a * (channel a).mass b
  nonneg s b := Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg s a) ((channel a).nonneg b)
  normalized s := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteDistribution.total, mul_one]
    exact p.normalized s

theorem postprocess_blind {O' : Type} [Fintype O'] (p : Behavior (phaseInterface O))
    (h : PhaseBlind p) (channel : Channel O O') : PhaseBlind (postprocess p channel) := by
  intro s t o
  simp only [postprocess]
  exact Finset.sum_congr rfl fun a _ => by rw [h s t a]

/-- One common phase-blind behavior approximates every setting and every outcome. -/
def NearBlind (p : Behavior (phaseInterface O)) (δ : ℝ) : Prop :=
  ∃ q : Behavior (phaseInterface O), PhaseBlind q ∧
    ∀ s o, |p.prob s o - q.prob s o| ≤ δ

theorem nearBlind_pair_bound (p : Behavior (phaseInterface O)) (δ : ℝ)
    (h : NearBlind p δ) (s t : Phase) (o : O) :
    |p.prob s o - p.prob t o| ≤ 2 * δ := by
  obtain ⟨q, hq, he⟩ := h
  have h₁ := abs_le.mp (he s o)
  have h₂ := abs_le.mp (he t o)
  have hst := hq s t o
  apply abs_le.mpr
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- All four estimates have an externally supplied simultaneous radius. The
bound holds without treating estimates as normalized probability tables. -/
theorem estimated_pair_bound (p : Behavior (phaseInterface O)) (δ r : ℝ)
    (h : NearBlind p δ) (estimate : Phase → O → ℝ)
    (he : ∀ s o, |estimate s o - p.prob s o| ≤ r) (s t : Phase) (o : O) :
    |estimate s o - estimate t o| ≤ 2 * δ + 2 * r := by
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp (nearBlind_pair_bound p δ h s t o)
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp (he s o)
  obtain ⟨ht₁, ht₂⟩ := abs_le.mp (he t o)
  apply abs_le.mpr
  constructor <;> linarith

/-- Strict violation excludes the whole calibrated null, not merely a finite scan. -/
theorem excludes_nearBlind (p : Behavior (phaseInterface O)) (δ r : ℝ)
    (estimate : Phase → O → ℝ) (he : ∀ s o, |estimate s o - p.prob s o| ≤ r)
    (s t : Phase) (o : O) (hv : 2 * δ + 2 * r < |estimate s o - estimate t o|) :
    ¬ NearBlind p δ := by
  intro hn
  exact (not_lt_of_ge (estimated_pair_bound p δ r hn estimate he s t o)) hv

/-- The finite convex class API receives the same whole-table exclusion. -/
theorem excludes_blind_mixture (g : G → Behavior (phaseInterface O))
    (hg : ∀ k, PhaseBlind (g k)) (p : Behavior (phaseInterface O))
    (s t : Phase) (o : O) (h : p.prob s o ≠ p.prob t o) : ¬ Compatible g p := by
  rintro ⟨w, hw⟩
  exact h ((hw s o).symm.trans ((mixture_blind g hg w s t o).trans (hw t o)))

/-- A common complete readout can be erased; this removes every phase separator. -/
def erase (p : Behavior (phaseInterface O)) : Behavior (phaseInterface Unit) :=
  postprocess p (Channel.deterministic (fun _ => ()))

theorem erase_probability (p : Behavior (phaseInterface O)) (s : Phase) :
    (erase p).prob s () = 1 := by
  simp [erase, postprocess, Channel.deterministic, p.normalized]

theorem erased_equivalent (p q : Behavior (phaseInterface O)) :
    ObservationallyEquivalent (erase p) (erase q) := by
  intro s o
  cases o
  rw [erase_probability, erase_probability]

/-- A stochastic setting-response simulator for any finite observed table. The
single hidden state has no trajectory dynamics or noncontextuality constraints. -/
def contextualResponse (p : Behavior (phaseInterface O)) : Phase → Channel Unit O :=
  fun s _ => { mass := p.prob s, nonneg := p.nonneg s, total := p.normalized s }

theorem contextual_matches (p : Behavior (phaseInterface O)) (s : Phase) (o : O) :
    (contextualResponse p s ()).mass o = p.prob s o := rfl

/-- Four phase positions of a real fringe. -/
def fringe : Phase → ℝ
  | .zero => 1
  | .quarter => 0
  | .half => -1
  | .threeQuarter => 0

/-- Two detected bins and a failure outcome. Both visibility and efficiency have
physical bounds; no postselection normalization enters this behavior. -/
def lossy (η v : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    Behavior (phaseInterface (Fin 3)) where
  prob s o := if o.val = 0 then η * (1 + v * fringe s) / 2
    else if o.val = 1 then η * (1 - v * fringe s) / 2 else 1 - η
  nonneg s o := by
    have hp : 0 ≤ 1 + v * fringe s := by cases s <;> simp [fringe] <;> linarith
    have hm : 0 ≤ 1 - v * fringe s := by cases s <;> simp [fringe] <;> linarith
    split_ifs
    · exact div_nonneg (mul_nonneg hη₀ hp) (by norm_num)
    · exact div_nonneg (mul_nonneg hη₀ hm) (by norm_num)
    · linarith
  normalized s := by
    change (∑ o : Fin 3, _) = _
    simp only [Fin.sum_univ_three]
    norm_num
    ring

theorem lossy_contrast (η v : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    (lossy η v hη₀ hη₁ hv₀ hv₁).prob .zero 0 -
      (lossy η v hη₀ hη₁ hv₀ hv₁).prob .half 0 = η * v := by
  norm_num [lossy, fringe]
  ring

/-- For this lossy family, the phase average is a nearest phase-blind behavior.
The required entrywise budget is exactly half this family’s full contrast. -/
theorem lossy_nearBlind_iff (η v δ : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) (hδ : 0 ≤ δ) :
    NearBlind (lossy η v hη₀ hη₁ hv₀ hv₁) δ ↔ η * v ≤ 2 * δ := by
  constructor
  · intro hn
    have hb := nearBlind_pair_bound _ δ hn .zero .half 0
    rw [lossy_contrast, abs_of_nonneg (mul_nonneg hη₀ hv₀)] at hb
    exact hb
  · intro hb
    refine ⟨lossy η 0 hη₀ hη₁ le_rfl (by norm_num), ?_, ?_⟩
    · intro s t o
      simp [lossy]
    · intro s o
      have hn := mul_nonneg hη₀ hv₀
      fin_cases o <;> cases s <;> norm_num [lossy, fringe] <;> first | exact hδ |
        (apply abs_le.mpr; constructor <;> nlinarith)

end
end OntologySeparation.PhaseIntervention
