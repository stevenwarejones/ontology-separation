import OntologySeparation.Operational.VCausalGeometry
import OntologySeparation.Operational.FiniteCausalKernels

/-! Finite classical protocols on the LC4 causal graph. The exogenous seed is
setting-independent. A/D outputs obey their actual causal order. B/C receive
both early settings and records, their own late input, and the common seed.
This is Bell screening-off at speed v, not a consequence of geometry alone. -/
namespace OntologySeparation.VCausal
noncomputable section
open scoped BigOperators
open HiddenInfluence

abbrev EarlyRecord := Bool × Bool

def xSetting (e : Early) : Bool := decide (e.val / 2 = 1)
def wSetting (e : Early) : Bool := decide (e.val % 2 = 1)
def _root_.OntologySeparation.HiddenInfluence.Strategy.record (s : Strategy) : EarlyRecord := (s.a, s.d)

inductive EarlyOrder | aFirst | dFirst | disconnected deriving DecidableEq

/-- At the deterministic level the earlier outcome cannot depend on the later
choice. Disconnected early parties each use only their own choice and seed. -/
def EarlyAllowed (order : EarlyOrder) (r : Early → EarlyRecord) : Prop :=
  (order ≠ .dFirst → ∀ e f, xSetting e = xSetting f → (r e).1 = (r f).1) ∧
  (order ≠ .aFirst → ∀ e f, wSetting e = wSetting f → (r e).2 = (r f).2)

def GeometryOrder (L : Layout) (v : ℚ) (order : EarlyOrder) : Prop :=
  match order with
  | .aFirst => precedes v (L .A) (L .D)
  | .dFirst => precedes v (L .D) (L .A)
  | .disconnected => ¬ precedes v (L .A) (L .D) ∧ ¬ precedes v (L .D) (L .A)

/-- Finite common-cause realization of just the early law. For disconnected
parties this is exactly a deterministic-strategy Bell-local decomposition. -/
structure EarlyModel (order : EarlyOrder) (Ω : Type) [Fintype Ω] where
  shared : FiniteDistribution Ω
  record : Ω → Early → EarlyRecord
  allowed : ∀ ω, shared.mass ω ≠ 0 → EarlyAllowed order (record ω)

/-- A protocol is sampled once, before the settings. Private random tapes can
be included in this seed. Only positive-mass tapes need obey the causal laws. -/
structure Protocol (order : EarlyOrder) (Ω : Type) [Fintype Ω] where
  shared : FiniteDistribution Ω
  table : Ω → Early → Strategy
  allowed : ∀ ω, shared.mass ω ≠ 0 →
    EarlyAllowed order (fun e => (table ω e).record)

def Protocol.toEarly {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) : EarlyModel order Ω where
  shared := p.shared
  record ω e := (p.table ω e).record
  allowed := p.allowed

/-- The late tables are evaluated only at the party's own setting. -/
def Protocol.run {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) : FiniteDistribution VisibleOutcome :=
  FiniteKernel.map p.shared (fun ω => (p.table ω e).visible y z)

def Protocol.strategies {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) : FiniteDistribution Strategy :=
  FiniteKernel.map p.shared (fun ω => p.table ω e)

def Protocol.toModel {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) : Model := Model.fromStrategies p.strategies

/-- Soundness preserves the complete four-party probability table, including
BC correlations discarded by the measured marginal projection. -/
theorem Protocol.full_behavior {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) (o : VisibleOutcome) :
    p.toModel.behavior.prob (e, lateFromBool y z) o.toOutcome =
      (p.run e y z).mass o := by
  rw [Protocol.toModel, Model.fromStrategies_prob_eq_selectedMass]
  simp only [Protocol.strategies, FiniteKernel.map, selectedMass_bind,
    selectedMass_pure, Protocol.run, FiniteKernel.bind_mass, FiniteKernel.pure_mass]
  apply Finset.sum_congr rfl
  intro ω _
  simp [eq_comm]

/-- Identical local information implies identical output; internal memory
summarized by the same finite seed cannot change this. -/
theorem Protocol.no_backwards_A {Ω : Type} [Fintype Ω]
    (p : Protocol .aFirst Ω) (ω : Ω) (hω : p.shared.mass ω ≠ 0)
    (e f : Early) (h : xSetting e = xSetting f) :
    (p.table ω e).a = (p.table ω f).a :=
  (p.allowed ω hω).1 (by decide) e f h

theorem Protocol.no_backwards_D {Ω : Type} [Fintype Ω]
    (p : Protocol .dFirst Ω) (ω : Ω) (hω : p.shared.mass ω ≠ 0)
    (e f : Early) (h : wSetting e = wSetting f) :
    (p.table ω e).d = (p.table ω f).d :=
  (p.allowed ω hω).2 (by decide) e f h

/-- Explicit counterexample to the unrestricted connected-case equivalence. -/
def backwardsTable (e : Early) : Strategy :=
  ⟨wSetting e, false, false, false, false, false⟩

theorem backwardsTable_not_allowed :
    ¬ EarlyAllowed .aFirst (fun e => (backwardsTable e).record) := by
  intro h
  have hbad := h.1 (by decide) 0 1 (by decide)
  norm_num [backwardsTable, Strategy.record, wSetting] at hbad


/-- The operational earlier marginal is independent of the later setting,
including zero-weight seeds where the table is unconstrained. -/
theorem EarlyModel.no_backwards_A {Ω : Type} [Fintype Ω]
    (p : EarlyModel .aFirst Ω) (e f : Early) (h : xSetting e = xSetting f) (a : Bool) :
    (FiniteKernel.map p.shared (fun ω => (p.record ω e).1)).mass a =
      (FiniteKernel.map p.shared (fun ω => (p.record ω f).1)).mass a := by
  simp only [FiniteKernel.map_mass]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hw : p.shared.mass ω = 0
  · simp [hw]
  · rw [(p.allowed ω hw).1 (by decide) e f h]

theorem EarlyModel.no_backwards_D {Ω : Type} [Fintype Ω]
    (p : EarlyModel .dFirst Ω) (e f : Early) (h : wSetting e = wSetting f) (d : Bool) :
    (FiniteKernel.map p.shared (fun ω => (p.record ω e).2)).mass d =
      (FiniteKernel.map p.shared (fun ω => (p.record ω f).2)).mass d := by
  simp only [FiniteKernel.map_mass]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hw : p.shared.mass ω = 0
  · simp [hw]
  · rw [(p.allowed ω hw).2 (by decide) e f h]

/-- The backwards table cannot be rescued by a different latent decomposition:
its observable A marginal already violates the earlier-party constraint. -/
theorem backwards_marginal_not_realizable :
    ¬ ∃ (Ω : Type) (_ : Fintype Ω) (p : EarlyModel .aFirst Ω),
      ∀ e a, (FiniteKernel.map p.shared (fun ω => (p.record ω e).1)).mass a =
        if (backwardsTable e).a = a then 1 else 0 := by
  rintro ⟨Ω,inst,p,h⟩
  letI := inst
  have hn := p.no_backwards_A 0 1 (by decide) false
  rw [h, h] at hn
  norm_num [backwardsTable,wSetting] at hn

/-- A layout-qualified protocol carries independent geometric and causal
obligations; neither the desired quantum marginals nor a bound is a field. -/
structure Model (L : Layout) (v : ℚ) (order : EarlyOrder)
    (Ω : Type) [Fintype Ω] extends Protocol order Ω where
  layout : LC4Layout L v
  geometry : GeometryOrder L v order

end
end OntologySeparation.VCausal
