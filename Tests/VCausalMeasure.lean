import OntologySeparation.Operational.VCausalMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OntologySeparation.Tests.VCausalMeasure
noncomputable section
open scoped BigOperators
open MeasureTheory HiddenInfluence VCausal

private def low : ResponseTable := fun _ => ⟨false,false,false,false,false,false⟩
private def high : ResponseTable := fun _ => ⟨true,false,false,false,false,false⟩
private theorem low_ne_high : low ≠ high := by
  intro h
  have := congrArg (fun t : ResponseTable => (t 0).a) h
  cases this

private def threshold (x : ℝ) : ResponseTable := if x ≤ 1/2 then low else high
private theorem threshold_measurable : Measurable threshold :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const

private def uniform : Measure ℝ := volume.restrict (Set.Icc 0 1)
private instance : IsProbabilityMeasure uniform := ⟨by norm_num [uniform]⟩

/-- A genuinely continuous hidden probability law, with two table fibers. -/
private def continuous : MeasurableProtocol .disconnected ℝ where
  shared := uniform
  probability := inferInstance
  table := threshold
  measurable_table := threshold_measurable
  allowed := Filter.Eventually.of_forall fun x => by
    unfold threshold
    split <;> exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

private theorem threshold_low (x : ℝ) : threshold x = low ↔ x ≤ 1/2 := by
  by_cases h : x ≤ 1/2 <;> simp [threshold, h, Ne.symm low_ne_high]
private theorem threshold_high (x : ℝ) : threshold x = high ↔ 1/2 < x := by
  by_cases h : x ≤ 1/2 <;> simp [threshold, h, low_ne_high]

/-- Exact half-weights, independently computed from interval lengths. -/
example : continuous.distribution.mass low = 1/2 := by
  rw [MeasurableProtocol.atom_mass]
  change uniform.real {x | threshold x = low} = _
  simp only [threshold_low]
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic (1/2)) = _
  rw [measureReal_restrict_apply measurableSet_Iic]
  have he : Set.Iic (1/2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1/2) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · intro h; exact ⟨h.2.1,h.1⟩
    · intro h; exact ⟨h.2,h.1,by linarith [h.2]⟩
  rw [he]
  norm_num [measureReal_def]

example : continuous.distribution.mass high = 1/2 := by
  rw [MeasurableProtocol.atom_mass]
  change uniform.real {x | threshold x = high} = _
  simp only [threshold_high]
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Ioi (1/2)) = _
  rw [measureReal_restrict_apply measurableSet_Ioi]
  have he : Set.Ioi (1/2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1/2) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · intro h; exact ⟨h.1,h.2.2⟩
    · intro h; exact ⟨h.1,by linarith [h.1],h.2⟩
  rw [he]
  norm_num [measureReal_def]

example : ObservationallyEquivalent continuous.behavior continuous.toFinite.toModel.behavior :=
  continuous.observationallyEquivalent

/-- A backwards response table cannot occupy positive probability mass.
This checks that compression did not discard the a.e. early-causal premise. -/
example (p : MeasurableProtocol .aFirst ℝ) :
    p.shared {x | p.table x = backwardsTable} = 0 := by
  apply measure_mono_null (t := {x | ¬ EarlyAllowed .aFirst (fun e => (p.table x e).record)})
  · intro x hx
    have he : p.table x = backwardsTable := hx
    change ¬ EarlyAllowed .aFirst (fun e => (p.table x e).record)
    rw [he]
    exact backwardsTable_not_allowed
  · exact ae_iff.mp p.allowed

example (p : MeasurableProtocol .aFirst ℝ)
    (h : 0 < p.shared {x | p.table x = backwardsTable}) : False := by
  have hz : p.shared {x | p.table x = backwardsTable} = 0 := by
    apply measure_mono_null (t := {x | ¬ EarlyAllowed .aFirst (fun e => (p.table x e).record)})
    · intro x hx
      have he : p.table x = backwardsTable := hx
      change ¬ EarlyAllowed .aFirst (fun e => (p.table x e).record)
      rw [he]
      exact backwardsTable_not_allowed
    · exact ae_iff.mp p.allowed
  simpa [hz] using h

end
end OntologySeparation.Tests.VCausalMeasure
