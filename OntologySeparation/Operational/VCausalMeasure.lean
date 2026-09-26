import OntologySeparation.Operational.VCausal
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
  rw [map_measureReal_apply p.measurable_table (measurableSet_singleton t)]
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
  rw [map_measureReal_apply p.measurable_table (Set.toFinite _).measurableSet]
  change p.shared.real _ = p.shared.real _
  congr 1
  ext ω
  simp

private def decodeY (l : Late) : Bool := decide (l.val / 2 = 1)
private def decodeZ (l : Late) : Bool := decide (l.val % 2 = 1)
private theorem decode_encode (y z : Bool) :
    decodeY (lateFromBool y z) = y ∧ decodeZ (lateFromBool y z) = z := by
  cases y <;> cases z <;> decide

private theorem MeasurableProtocol.decoded_mass {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) (e : Early) (l : Late) (o : Outcome) :
    p.mass e (decodeY l) (decodeZ l) (outcomeToVisible o) =
      p.toFinite.toModel.behavior.prob (e,l) o := by
  obtain ⟨⟨y,z⟩,rfl⟩ := lateFromBool_surjective l
  rw [(decode_encode y z).1, (decode_encode y z).2, ← p.full_behavior,
    VisibleOutcome.toOutcome_outcomeToVisible]

/-- The observed behavior is defined by event measures in the original space. -/
def MeasurableProtocol.behavior {order : EarlyOrder} {Ω : Type*} [MeasurableSpace Ω]
    (p : MeasurableProtocol order Ω) : Behavior interface where
  prob s o := p.mass s.1 (decodeY s.2) (decodeZ s.2) (outcomeToVisible o)
  nonneg _ _ := ENNReal.toReal_nonneg
  normalized s := by
    simp_rw [p.decoded_mass]
    exact p.toFinite.toModel.behavior.normalized s

theorem MeasurableProtocol.observationallyEquivalent {order : EarlyOrder} {Ω : Type*}
    [MeasurableSpace Ω] (p : MeasurableProtocol order Ω) :
    ObservationallyEquivalent p.behavior p.toFinite.toModel.behavior := by
  rintro ⟨e,l⟩ o
  exact p.decoded_mass e l o

/-- Every finite law embeds as a probability measure with the same atom weights. -/
def distributionPMF {Ω : Type} [Fintype Ω] (d : FiniteDistribution Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (d.mass ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => d.nonneg ω), d.total]
    simp)

def Protocol.toMeasurable {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : Protocol order Ω) :
    MeasurableProtocol order Ω where
  shared := (distributionPMF p.shared).toMeasure
  probability := inferInstance
  table := p.table
  measurable_table := measurable_of_countable p.table
  allowed := by
    rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff (Set.toFinite _).measurableSet]
    apply Set.disjoint_left.mpr
    intro ω hω hbad
    apply hbad
    apply p.allowed ω
    intro hz
    simpa [distributionPMF, PMF.mem_support_iff, hz] using hω

/-- The finite embedding retains the entire outcome law. -/
theorem Protocol.toMeasurable_mass {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : Protocol order Ω)
    (e : Early) (y z : Bool) (o : VisibleOutcome) :
    p.toMeasurable.mass e y z o = (p.run e y z).mass o := by
  classical
  simp only [MeasurableProtocol.mass, Protocol.toMeasurable, measureReal_def]
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun ω _ => by
    simp only [Set.indicator_apply, distributionPMF, PMF.ofFintype_apply]
    split <;> simp)]
  simp [Protocol.run, FiniteKernel.map_mass, distributionPMF, Set.indicator_apply,
    p.shared.nonneg]

theorem Protocol.toMeasurable_behavior {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : Protocol order Ω) :
    ObservationallyEquivalent p.toMeasurable.toFinite.toModel.behavior p.toModel.behavior := by
  rintro ⟨e,l⟩ o
  obtain ⟨⟨y,z⟩,rfl⟩ := lateFromBool_surjective l
  obtain ⟨o,rfl⟩ := VisibleOutcome.toOutcome_surjective o
  rw [MeasurableProtocol.full_behavior, Protocol.toMeasurable_mass, Protocol.full_behavior]

/-- Compression of an embedded finite protocol groups the original seed atoms
by their complete tables, including responses at settings not selected. -/
theorem Protocol.toMeasurable_distribution {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : Protocol order Ω) :
    p.toMeasurable.distribution = FiniteKernel.map p.shared p.table := by
  classical
  have hm : ∀ t, p.toMeasurable.distribution.mass t =
      (FiniteKernel.map p.shared p.table).mass t := by
    intro t
    rw [MeasurableProtocol.atom_mass]
    simp only [Protocol.toMeasurable, measureReal_def]
    rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun ω _ => by
      simp only [Set.indicator_apply, distributionPMF, PMF.ofFintype_apply]
      split <;> simp)]
    simp [FiniteKernel.map_mass, distributionPMF, Set.indicator_apply, p.shared.nonneg]
  cases p.toMeasurable.distribution
  cases FiniteKernel.map p.shared p.table
  congr
  exact funext hm

theorem Protocol.toMeasurable_strategies {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : Protocol order Ω) (e : Early) :
    p.toMeasurable.toFinite.strategies e = p.strategies e := by
  classical
  have hm : ∀ s, (p.toMeasurable.toFinite.strategies e).mass s = (p.strategies e).mass s := by
    intro s
    change (FiniteKernel.map p.toMeasurable.distribution (fun t => t e)).mass s = _
    rw [p.toMeasurable_distribution]
    have h := FiniteKernel.map_mean p.shared p.table
      (fun t => if t e = s then (1 : ℝ) else 0)
    simpa [Protocol.strategies, FiniteKernel.map_mass, mul_ite] using h
  cases p.toMeasurable.toFinite.strategies e
  cases p.strategies e
  congr
  exact funext hm

/-- The finite embedding and compression preserve even the packed strategy
model, strengthening observational equivalence and transporting all objectives. -/
theorem Protocol.toMeasurable_toModel {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : Protocol order Ω) :
    p.toMeasurable.toFinite.toModel = p.toModel := by
  unfold Protocol.toModel
  congr 1
  funext e
  exact p.toMeasurable_strategies e

end
end OntologySeparation.VCausal
