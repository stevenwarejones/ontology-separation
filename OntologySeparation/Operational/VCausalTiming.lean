import OntologySeparation.Operational.VCausal

/-! A common finite mechanism for a blind run and either single-party delay.
The undelayed party's response and the initial seed law are shared across
branches. Branches are interventions, not selected hidden-variable subensembles.
These equalities require choices made outside the retained records' v-pasts. -/
namespace OntologySeparation.VCausal
noncomputable section
open scoped BigOperators
open HiddenInfluence

abbrev Triple := Bool × Bool × Bool

def abdRecord (o : VisibleOutcome) : Triple := (o.a,o.b,o.d)
def acdRecord (o : VisibleOutcome) : Triple := (o.a,o.c,o.d)
def withC (o : VisibleOutcome) (c : Bool) : VisibleOutcome := { o with c := c }
def withB (o : VisibleOutcome) (b : Bool) : VisibleOutcome := { o with b := b }


/-- A finite intervention menu. The two choices occur at the original late
events, which are outside the other original late event's v-past. -/
structure TimingLayout (L : Layout) (v : ℚ) where
  blind : LC4Layout L v
  delayedC : Event
  delayedB : Event
  c_after : lightFuture (L .C) delayedC
  b_after : lightFuture (L .B) delayedB
  bc_connected : precedes v (L .B) delayedC
  cb_connected : precedes v (L .C) delayedB

/-- Delayed responses may use the early record, the undelayed outcome, both
late settings, and the initial seed. They cannot change already-produced records. -/
structure TimingProtocol {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) where
  delayedC : Ω → Early → Bool → Bool → Triple → FiniteDistribution Bool
  delayedB : Ω → Early → Bool → Bool → Triple → FiniteDistribution Bool

def TimingProtocol.runC {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    {p : Protocol order Ω} (t : TimingProtocol p) (e : Early) (y z : Bool) :
    FiniteDistribution VisibleOutcome :=
  FiniteKernel.bind p.shared fun ω =>
    let o := (p.table ω e).visible y z
    FiniteKernel.map (t.delayedC ω e y z (abdRecord o)) (withC o)

def TimingProtocol.runB {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    {p : Protocol order Ω} (t : TimingProtocol p) (e : Early) (y z : Bool) :
    FiniteDistribution VisibleOutcome :=
  FiniteKernel.bind p.shared fun ω =>
    let o := (p.table ω e).visible y z
    FiniteKernel.map (t.delayedB ω e y z (acdRecord o)) (withB o)

/-- A probability of a visible record, defined without discarding trials. -/
def recordProb {α : Type} [Fintype α] [DecidableEq α] (d : FiniteDistribution VisibleOutcome)
    (project : VisibleOutcome → α) (r : α) : ℝ :=
  ∑ o, d.mass o * (if project o = r then 1 else 0)

theorem TimingProtocol.delayC_preserves_ABD {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    {p : Protocol order Ω} (t : TimingProtocol p) (e : Early) (y z : Bool) (r : Triple) :
    recordProb (t.runC e y z) abdRecord r = recordProb (p.run e y z) abdRecord r := by
  unfold recordProb TimingProtocol.runC Protocol.run
  rw [FiniteKernel.bind_mean, FiniteKernel.map_mean]
  apply Finset.sum_congr rfl
  intro ω _
  rw [FiniteKernel.map_mean]
  have htotal := (t.delayedC ω e y z (abdRecord ((p.table ω e).visible y z))).total
  simp only [Fintype.sum_bool] at htotal
  simp only [abdRecord, withC, Fintype.sum_bool]
  congr 1
  dsimp only [abdRecord] at htotal
  split_ifs <;> simp_all

theorem TimingProtocol.delayB_preserves_ACD {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    {p : Protocol order Ω} (t : TimingProtocol p) (e : Early) (y z : Bool) (r : Triple) :
    recordProb (t.runB e y z) acdRecord r = recordProb (p.run e y z) acdRecord r := by
  unfold recordProb TimingProtocol.runB Protocol.run
  rw [FiniteKernel.bind_mean, FiniteKernel.map_mean]
  apply Finset.sum_congr rfl
  intro ω _
  rw [FiniteKernel.map_mean]
  have htotal := (t.delayedB ω e y z (acdRecord ((p.table ω e).visible y z))).total
  simp only [Fintype.sum_bool] at htotal
  simp only [acdRecord, withB, Fintype.sum_bool]
  congr 1
  dsimp only [acdRecord] at htotal
  split_ifs <;> simp_all


end
end OntologySeparation.VCausal
