import OntologySeparation.Operational.VCausal

namespace OntologySeparation.VCausal
noncomputable section
open scoped BigOperators
open HiddenInfluence

instance : Inhabited Strategy := ⟨⟨false,false,false,false,false,false⟩⟩

/-- Exact early-law compatibility. This records only early probabilities,
not the desired full response-table distribution. -/
def EarlyMatches {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : EarlyModel order Ω) (q : Early → FiniteDistribution Strategy) : Prop :=
  ∀ e r, (FiniteKernel.map p.shared (fun ω => p.record ω e)).mass r =
    (FiniteKernel.map (q e) Strategy.record).mass r

def conditionalTables {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : EarlyModel order Ω) (q : Early → FiniteDistribution Strategy) (ω : Ω) :
    FiniteDistribution (Early → Strategy) :=
  FiniteKernel.reservoir (fun e => FiniteKernel.condition (q e) Strategy.record (p.record ω e))

/-- Finite gluing construction. The entire reservoir is sampled with the early
seed before any actual setting; selecting a slot is not measurement dependence. -/
def realize {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : EarlyModel order Ω) (q : Early → FiniteDistribution Strategy)
    (hm : EarlyMatches p q) : Protocol order (Ω × (Early → Strategy)) where
  shared := FiniteKernel.joint p.shared (conditionalTables p q)
  table ω e := ω.2 e
  allowed := by
    intro ω hω
    have hw := mul_ne_zero_iff.mp hω
    have he : ∀ e, (ω.2 e).record = p.record ω.1 e := by
      intro e
      have hf : (FiniteKernel.map (q e) Strategy.record).mass (p.record ω.1 e) ≠ 0 := by
        rw [← hm]
        have hh := FiniteKernel.map_single_le p.shared (fun u => p.record u e) ω.1
        have hp := lt_of_le_of_ne (p.shared.nonneg ω.1) (Ne.symm hw.1)
        exact ne_of_gt (lt_of_lt_of_le hp hh)
      have ht : (FiniteKernel.condition (q e) Strategy.record (p.record ω.1 e)).mass (ω.2 e) ≠ 0 := by
        have hprod : (∏ i : Early,
            (FiniteKernel.condition (q i) Strategy.record (p.record ω.1 i)).mass (ω.2 i)) ≠ 0 := hw.2
        exact (Finset.prod_ne_zero_iff.mp hprod) e (Finset.mem_univ e)
      exact FiniteKernel.condition_support _ _ _ _ hf ht
    simpa only [he] using p.allowed ω.1 hw.1

/-- Every original response-table probability is preserved, not only the
observed ABD/ACD projection. -/
theorem realize_strategies {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : EarlyModel order Ω) (q : Early → FiniteDistribution Strategy)
    (hm : EarlyMatches p q) (e : Early) (s : Strategy) :
    ((realize p q hm).strategies e).mass s = (q e).mass s := by
  rw [Protocol.strategies, FiniteKernel.map_mass]
  simp only [realize, FiniteKernel.joint, Fintype.sum_prod_type]
  have hs : ∀ ω, (∑ t : Early → Strategy,
      if t e = s then p.shared.mass ω * (conditionalTables p q ω).mass t else 0) =
      p.shared.mass ω * (FiniteKernel.condition (q e) Strategy.record (p.record ω e)).mass s := by
    intro ω
    calc
      _ = p.shared.mass ω * ∑ t : Early → Strategy,
          (conditionalTables p q ω).mass t * (if t e = s then 1 else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            split <;> simp_all
      _ = _ := by
        rw [conditionalTables, FiniteKernel.reservoir_mean
          (fun i => FiniteKernel.condition (q i) Strategy.record (p.record ω i)) e
          (fun a => if a = s then (1 : ℝ) else 0)]
        simp
  simp_rw [hs]
  rw [← FiniteKernel.map_mean p.shared (fun ω => p.record ω e)
    (fun r => (FiniteKernel.condition (q e) Strategy.record r).mass s)]
  simp_rw [hm e, FiniteKernel.condition_weight]
  simp

/-- The generic converse needs exactly a realizable early law. -/
theorem realize_full_behavior {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : EarlyModel order Ω) (q : Early → FiniteDistribution Strategy)
    (hm : EarlyMatches p q) :
    ObservationallyEquivalent (realize p q hm).toModel.behavior
      (HiddenInfluence.Model.fromStrategies q).behavior := by
  intro setting outcome
  obtain ⟨yz, hyz⟩ := lateFromBool_surjective setting.2
  obtain ⟨o, ho⟩ := VisibleOutcome.toOutcome_surjective outcome
  rcases setting with ⟨e,l⟩
  dsimp at hyz
  rw [← hyz, ← ho]
  simp only [Protocol.toModel, HiddenInfluence.Model.fromStrategies_prob_eq_selectedMass,
    selectedMass, realize_strategies]

/-- A physical protocol already supplies the required early common cause. -/
theorem Protocol.earlyMatches {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) : EarlyMatches p.toEarly p.strategies := by
  intro e r
  have hh := FiniteKernel.map_mean p.shared (fun ω => p.table ω e)
    (fun s => if s.record = r then (1 : ℝ) else 0)
  rw [FiniteKernel.map_mass]
  change (∑ ω, if (p.table ω e).record = r then p.shared.mass ω else 0) = _
  rw [FiniteKernel.map_mass]
  simpa [Protocol.strategies, mul_ite] using hh.symm

/-- Exact fixed-layout characterization, at the level of response-table laws.
The early realization is an independently specified finite causal decomposition.
For disconnected early parties it is the Bell-local early-law condition. -/
theorem realizable_iff_early (order : EarlyOrder) (q : Early → FiniteDistribution Strategy) :
    (∃ (Ω : Type) (_ : Fintype Ω) (p : Protocol order Ω),
      ∀ e s, (p.strategies e).mass s = (q e).mass s) ↔
    (∃ (Ω : Type) (_ : Fintype Ω) (p : EarlyModel order Ω), EarlyMatches p q) := by
  constructor
  · rintro ⟨Ω,inst,p,hp⟩
    letI := inst
    refine ⟨Ω,inst,p.toEarly,?_⟩
    intro e r
    rw [p.earlyMatches e r]
    simp_rw [FiniteKernel.map_mass, hp]
  · rintro ⟨Ω,inst,p,hp⟩
    letI := inst
    exact ⟨Ω × (Early → Strategy), inferInstance, realize p q hp,
      realize_strategies p q hp⟩

end
end OntologySeparation.VCausal
