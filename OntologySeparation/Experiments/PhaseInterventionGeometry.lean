import OntologySeparation.Experiments.PhaseInterventionExamples

/-! Geometry of a normalized common response. Pairwise tests are exact for two
outcomes but can miss the normalization obstruction with three outcomes. -/
namespace OntologySeparation.PhaseIntervention
noncomputable section

/-- Linear feasibility form: all setting intervals share one nonnegative vector
whose entries sum to one. The inequalities are equivalent to the per-outcome
interval [max_s p(s,o)-δ, min_s p(s,o)+δ], intersected with nonnegative weights. -/
theorem nearBlind_iff_feasible {O : Type} [Fintype O]
    (p : Behavior (phaseInterface O)) (δ : ℝ) :
    NearBlind p δ ↔ ∃ q : O → ℝ, (∀ o, 0 ≤ q o) ∧ (∑ o, q o) = 1 ∧
      ∀ s o, p.prob s o - δ ≤ q o ∧ q o ≤ p.prob s o + δ := by
  constructor
  · rintro ⟨q, hq, he⟩
    refine ⟨q.prob .zero, q.nonneg .zero, q.normalized .zero, ?_⟩
    intro s o
    have h := abs_le.mp (he s o)
    rw [hq s .zero o] at h
    constructor <;> linarith [h.1, h.2]
  · rintro ⟨q, hn, ht, he⟩
    refine ⟨⟨fun _ => q, fun _ => hn, fun _ => ht⟩, ?_, ?_⟩
    · intro s t o; rfl
    · intro s o
      obtain ⟨h₁, h₂⟩ := he s o
      apply abs_le.mpr
      constructor <;> dsimp <;> linarith

def triangle : Behavior (phaseInterface (Fin 3)) where
  prob s o := match s with
    | .zero => if o.val = 0 then 1 else 0
    | .quarter => if o.val = 1 then 1 else 0
    | .half => if o.val = 2 then 1 else 0
    | .threeQuarter => 1/3
  nonneg s o := by cases s <;> split_ifs <;> norm_num
  normalized s := by
    change (∑ o : Fin 3, _) = _
    rw [Fin.sum_univ_three]
    cases s <;> norm_num

theorem triangle_pairwise (ε : ℝ) (hε : 0 ≤ ε) (s t : Phase) (o : Fin 3) :
    |triangle.prob s o - triangle.prob t o| ≤ 2 * (1/2 + ε) := by
  fin_cases o <;> cases s <;> cases t <;> norm_num [triangle] <;> linarith

theorem triangle_nearBlind_iff (δ : ℝ) : NearBlind triangle δ ↔ 2/3 ≤ δ := by
  rw [nearBlind_iff_feasible]
  constructor
  · rintro ⟨q, hn, ht, he⟩
    have h₀ := (he .zero 0).1
    have h₁ := (he .quarter 1).1
    have h₂ := (he .half 2).1
    norm_num [triangle] at h₀ h₁ h₂
    rw [Fin.sum_univ_three] at ht
    linarith
  · intro hδ
    refine ⟨fun _ => 1/3, by intro o; norm_num, ?_, ?_⟩
    · norm_num
    · intro s o
      fin_cases o <;> cases s <;> norm_num [triangle] <;> (try constructor) <;> linarith

theorem triangle_pairwise_not_sufficient (ε : ℝ) (h₀ : 0 ≤ ε) (h₁ : ε < 1/6) :
    (∀ s t o, |triangle.prob s o - triangle.prob t o| ≤ 2 * (1/2 + ε)) ∧
    ¬ NearBlind triangle (1/2 + ε) := by
  refine ⟨triangle_pairwise ε h₀, ?_⟩
  rw [triangle_nearBlind_iff]
  linarith

/-- For two outcomes use the midpoint of the largest and smallest probabilities,
not the average over all four settings (which need not be minimax). -/
theorem binary_nearBlind_iff (p : Behavior (phaseInterface Bool)) (δ : ℝ) :
    NearBlind p δ ↔ ∀ s t o, |p.prob s o - p.prob t o| ≤ 2*δ := by
  constructor
  · intro h s t o
    exact nearBlind_pair_bound p δ h s t o
  · intro hp
    obtain ⟨slo, _, hlo⟩ := Finset.exists_min_image Finset.univ (fun s => p.prob s true)
      (⟨Phase.zero, Finset.mem_univ _⟩ : (Finset.univ : Finset Phase).Nonempty)
    obtain ⟨shi, _, hhi⟩ := Finset.exists_max_image Finset.univ (fun s => p.prob s true)
      (⟨Phase.zero, Finset.mem_univ _⟩ : (Finset.univ : Finset Phase).Nonempty)
    have hext := abs_le.mp (hp shi slo true)
    have norm (s : Phase) : p.prob s false + p.prob s true = 1 := by
      simpa only [Fintype.sum_bool, add_comm] using p.normalized s
    have lo0 := p.nonneg slo true
    have hi0 := p.nonneg shi true
    have lo1 : p.prob slo true ≤ 1 := by linarith [norm slo, p.nonneg slo false]
    have hi1 : p.prob shi true ≤ 1 := by linarith [norm shi, p.nonneg shi false]
    rw [nearBlind_iff_feasible]
    refine ⟨fun o => if o then (p.prob slo true + p.prob shi true)/2
      else 1-(p.prob slo true + p.prob shi true)/2, ?_, ?_, ?_⟩
    · intro o; cases o <;> simp <;> linarith
    · simp
    · intro s o
      have hslo := hlo s (Finset.mem_univ s)
      have hshi := hhi s (Finset.mem_univ s)
      cases o <;> simp <;> constructor <;> linarith [norm s, hext.1, hext.2]

end
end OntologySeparation.PhaseIntervention
