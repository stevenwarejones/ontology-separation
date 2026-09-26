import OntologySeparation.Operational.VCausal
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Compression of an arbitrary measurable hidden probability space into the
finite set of deterministic response tables. Measurability and setting
independence are explicit. Causal constraints hold almost everywhere; null
hidden states need not satisfy them. No countability assumption is imposed on Ω. -/
namespace OntologySeparation.VCausal
noncomputable section
open scoped BigOperators
open HiddenInfluence MeasureTheory

instance strategyMeasurableSpace : MeasurableSpace Strategy := ⊤
instance strategyMeasurableSingletonClass : MeasurableSingletonClass Strategy :=
  ⟨fun _ => trivial⟩

abbrev ResponseTable := Early → Strategy

structure MeasurableProtocol (order : EarlyOrder) (Ω : Type*) [MeasurableSpace Ω] where
  shared : Measure Ω
  probability : IsProbabilityMeasure shared
  table : Ω → ResponseTable
  measurable_table : Measurable table
  allowed : ∀ᵐ ω ∂shared, EarlyAllowed order (fun e => (table ω e).record)

attribute [instance] MeasurableProtocol.probability

/-- The measure is chosen before settings: there is one common hidden law. -/
def MeasurableProtocol.tableLaw {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) : Measure ResponseTable := p.shared.map p.table

instance {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) : IsProbabilityMeasure p.tableLaw :=
  Measure.isProbabilityMeasure_map p.measurable_table.aemeasurable

/-- Real masses of the pushforward's atoms form a normalized finite law. -/
def MeasurableProtocol.distribution {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) : FiniteDistribution ResponseTable where
  mass t := p.tableLaw.real {t}
  nonneg t := ENNReal.toReal_nonneg
  total := by
    have h := sum_measureReal_singleton (μ := p.tableLaw) (Finset.univ : Finset ResponseTable)
    simpa using h

theorem MeasurableProtocol.atom_mass {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) (t : ResponseTable) :
    p.distribution.mass t = p.shared.real {ω | p.table ω = t} := by
  change (p.shared.map p.table).real {t} = _
  rw [measureReal_map_apply p.measurable_table (measurableSet_singleton t)]
  rfl

/-- A positive atom must obey the a.e. causal law. -/
theorem MeasurableProtocol.atom_allowed {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) (t : ResponseTable) (ht : p.distribution.mass t ≠ 0) :
    EarlyAllowed order (fun e => (t e).record) := by
  by_contra h
  have hz : p.shared {ω | p.table ω = t} = 0 := by
    apply measure_mono_null (t := {ω | ¬ EarlyAllowed order (fun e => (p.table ω e).record)})
    · intro ω hω
      simpa only [Set.mem_setOf_eq, hω] using h
    · exact ae_iff.mp p.allowed
  rw [p.atom_mass, measureReal_def, hz, ENNReal.toReal_zero] at ht
  exact ht rfl

def MeasurableProtocol.toFinite {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) : Protocol order ResponseTable where
  shared := p.distribution
  table t := t
  allowed := p.atom_allowed

/-- Observable event probability in the original (possibly continuous) space. -/
def MeasurableProtocol.mass {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) (e : Early) (y z : Bool) (o : VisibleOutcome) : ℝ :=
  p.shared.real {ω | (p.table ω e).visible y z = o}

/-- Exact finite compression preserves the full outcome table, not merely the
measured ABD/ACD projections or the signaling objective. -/
theorem MeasurableProtocol.full_behavior {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) (e : Early) (y z : Bool) (o : VisibleOutcome) :
    p.toFinite.toModel.behavior.prob (e,lateFromBool y z) o.toOutcome = p.mass e y z o := by
  classical
  rw [Protocol.full_behavior]
  simp only [Protocol.run, FiniteKernel.map_mass, MeasurableProtocol.toFinite,
    MeasurableProtocol.distribution]
  rw [← Finset.sum_filter]
  have h := sum_measureReal_singleton (μ := p.tableLaw)
    (Finset.univ.filter fun t : ResponseTable => (t e).visible y z = o)
  rw [h]
  change (p.shared.map p.table).real _ = _
  rw [measureReal_map_apply p.measurable_table (Set.toFinite _).measurableSet]
  congr 1
  ext ω
  simp [MeasurableProtocol.mass]

end
end OntologySeparation.VCausal
