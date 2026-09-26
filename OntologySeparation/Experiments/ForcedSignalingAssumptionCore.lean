import OntologySeparation.Experiments.ForcedSignalingVCausal
import OntologySeparation.Operational.VCausalTiming
import OntologySeparation.Core.AdversarySearch

/-! Assumption deletion for the same forced-signaling target. The model language
allows selection and setting-dependent seeds explicitly. This is a core for
conditional locality, not a claim that every spacetime premise is necessary. -/
namespace OntologySeparation.ForcedSignalingAssumptionCore
noncomputable section
open scoped BigOperators
open HiddenInfluence VCausal ForcedSignalingLC4Witness ForcedSignalingLC4
open AdversarySearch

abbrev Input := Early × Bool × Bool
abbrev LawTable := Input → FiniteDistribution VisibleOutcome

structure Mechanism (Ω : Type) [Fintype Ω] where
  seed : Input → FiniteDistribution Ω
  response : Ω → Input → FiniteDistribution VisibleOutcome
  accept : Input → VisibleOutcome → ℝ
  accept_bounds : ∀ s o, 0 ≤ accept s o ∧ accept s o ≤ 1
  reported : LawTable
  rate : Input → ℝ
  rate_pos : ∀ s, 0 < rate s
  selected : ∀ s o, rate s * (reported s).mass o =
    (FiniteKernel.bind (seed s) (fun ω => response ω s)).mass o * accept s o

def Independent {Ω : Type} [Fintype Ω] (m : Mechanism Ω) : Prop :=
  ∀ s t, m.seed s = m.seed t

def LocalResponses {Ω : Type} [Fintype Ω] (m : Mechanism Ω) : Prop :=
  ∃ table : Ω → Early → Strategy, ∀ ω e y z,
    m.response ω (e,y,z) = FiniteKernel.pure ((table ω e).visible y z)

def Unfiltered {Ω : Type} [Fintype Ω] (m : Mechanism Ω) : Prop :=
  ∀ s o, m.accept s o = 1

theorem unfiltered_rate {Ω : Type} [Fintype Ω] (m : Mechanism Ω)
    (h : Unfiltered m) (s : Input) : m.rate s = 1 := by
  have hs := congrArg (fun f : VisibleOutcome → ℝ => ∑ o, f o) (funext (m.selected s))
  simpa [h s, ← Finset.mul_sum, (m.reported s).total,
    (FiniteKernel.bind (m.seed s) (fun ω => m.response ω s)).total] using hs

theorem unfiltered_report {Ω : Type} [Fintype Ω] (m : Mechanism Ω)
    (h : Unfiltered m) (s : Input) (o : VisibleOutcome) :
    (m.reported s).mass o = (FiniteKernel.bind (m.seed s) (fun ω => m.response ω s)).mass o := by
  simpa [unfiltered_rate m h s, h s o] using m.selected s o

def lateY (l : Late) : Bool := decide (l.val / 2 = 1)
def lateZ (l : Late) : Bool := decide (l.val % 2 = 1)
private theorem late_encode (y z : Bool) :
    lateY (lateFromBool y z) = y ∧ lateZ (lateFromBool y z) = z := by
  cases y <;> cases z <;> decide

def behavior (d : LawTable) : Behavior interface where
  prob s o := (d (s.1, lateY s.2, lateZ s.2)).mass (outcomeToVisible o)
  nonneg s o := (d _).nonneg _
  normalized s := by
    rw [← visibleOutcomeEquiv.sum_comp]
    simpa [visibleOutcomeEquiv] using (d (s.1,lateY s.2,lateZ s.2)).total

theorem behavior_visible (d : LawTable) (e : Early) (y z : Bool) (o : VisibleOutcome) :
    (behavior d).prob (e,lateFromBool y z) o.toOutcome = (d (e,y,z)).mass o := by
  simp [behavior, late_encode, outcomeToVisible_toOutcome]

structure Matches (d : LawTable) : Prop where
  abd : ∀ x y w a b dd,
    recordProb (d (earlyOf x w,y,false)) abdRecord (a,b,dd) =
      Q2.toReal (ForcedSignalingLC4.abd x y w a b dd)
  acd : ∀ x z w a c dd,
    recordProb (d (earlyOf x w,false,z)) acdRecord (a,c,dd) =
      Q2.toReal (ForcedSignalingLC4.acd x z w a c dd)

def Target {Ω : Type} [Fintype Ω] (m : Mechanism Ω) : Prop :=
  Matches m.reported ∧ Within (behavior m.reported) 0

theorem conditional_local {Ω : Type} [Fintype Ω] (m : Mechanism Ω)
    (hi : Independent m) (hl : LocalResponses m) (hu : Unfiltered m) :
    ∃ q : Early → FiniteDistribution Strategy, ∀ e y z o,
      (m.reported (e,y,z)).mass o = selectedMass (q e) y z o := by
  obtain ⟨table, ht⟩ := hl
  refine ⟨fun e => FiniteKernel.map (m.seed (0,false,false)) (fun ω => table ω e), ?_⟩
  intro e y z o
  rw [unfiltered_report m hu, FiniteKernel.bind_mass]
  simp_rw [ht, hi (e,y,z) (0,false,false)]
  have hm := FiniteKernel.map_mean (m.seed (0,false,false)) (fun ω => table ω e)
    (fun s => if s.visible y z = o then (1 : ℝ) else 0)
  rw [show selectedMass (FiniteKernel.map (m.seed (0,false,false)) (fun ω => table ω e)) y z o =
      ∑ ω, (m.seed (0,false,false)).mass ω * (if (table ω e).visible y z = o then 1 else 0) by
    simpa [selectedMass, mul_ite] using hm]
  simp [eq_comm]

private theorem record_model (d : LawTable) (m : HiddenInfluence.Model)
    (h : ∀ e y z o, (d (e,y,z)).mass o = m.behavior.prob (e,lateFromBool y z) o.toOutcome)
    (e : Early) (y z : Bool) (r : Triple) (project : VisibleOutcome → Triple) :
    recordProb (d (e,y,z)) project r =
      mean m.behavior e (lateFromBool y z) (fun o => if project (outcomeToVisible o) = r then 1 else 0) := by
  unfold recordProb mean
  rw [← visibleOutcomeEquiv.sum_comp]
  simp [h, visibleOutcomeEquiv, outcomeToVisible_toOutcome]

set_option maxHeartbeats 0 in
private theorem abd_bits : ∀ (o : Outcome) (a b d : Bool),
    abdRecord (outcomeToVisible o) = (a,b,d) ↔
      o.val / 8 = a.toNat ∧ o.val / 4 % 2 = b.toNat ∧ o.val % 2 = d.toNat := by
  decide +kernel
set_option maxHeartbeats 0 in
private theorem acd_bits : ∀ (o : Outcome) (a c d : Bool),
    acdRecord (outcomeToVisible o) = (a,c,d) ↔
      o.val / 8 = a.toNat ∧ o.val / 2 % 2 = c.toNat ∧ o.val % 2 = d.toNat := by
  decide +kernel

theorem matches_model (d : LawTable) (m : HiddenInfluence.Model)
    (h : ∀ e y z o, (d (e,y,z)).mass o = m.behavior.prob (e,lateFromBool y z) o.toOutcome)
    (hq : Matches d) : ForcedSignalingTheorem2.MatchesCluster m := by
  constructor
  · intro x y w a b dd
    rw [← hq.abd, record_model d m h, mean_eq]
    simp only [modelABD, lateOf, lateFromBool, ite_and, abd_bits]
    rfl
  · intro x z w a c dd
    rw [← hq.acd, record_model d m h, mean_eq]
    simp only [modelACD, lateOf, lateFromBool, ite_and, acd_bits]
    rfl

theorem excludes {Ω : Type} [Fintype Ω] (m : Mechanism Ω)
    (hi : Independent m) (hl : LocalResponses m) (hu : Unfiltered m) : ¬ Target m := by
  rintro ⟨hq,hns⟩
  obtain ⟨q,hq'⟩ := conditional_local m hi hl hu
  let localModel := HiddenInfluence.Model.fromStrategies q
  have he : ∀ e y z o, (m.reported (e,y,z)).mass o =
      localModel.behavior.prob (e,lateFromBool y z) o.toOutcome := by
    intro e y z o
    rw [HiddenInfluence.Model.fromStrategies_prob_eq_selectedMass]
    exact hq' e y z o
  have hm := matches_model m.reported localModel he hq
  have hb : ∀ s o, (behavior m.reported).prob s o = localModel.behavior.prob s o := by
    rintro ⟨e,l⟩ o
    obtain ⟨⟨y,z⟩,rfl⟩ := lateFromBool_surjective l
    obtain ⟨o,rfl⟩ := VisibleOutcome.toOutcome_surjective o
    rw [behavior_visible, he]
  have hns' : Within localModel.behavior 0 := by
    simpa only [Within, tv, difference, marginal, mean, hb] using hns
  have hlo := ForcedSignalingTheorem2.lower_bound hm
  have hhi := (signaling_le_iff localModel 0).mpr hns'
  rw [ForcedSignalingTheorem2.targetDelta_value] at hlo
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

private theorem mass_le_one (d : FiniteDistribution VisibleOutcome) (o : VisibleOutcome) :
    d.mass o ≤ 1 := by
  rw [← d.total]
  exact Finset.single_le_sum (fun x _ => d.nonneg x) (Finset.mem_univ o)

def dependent (d : LawTable) : Mechanism VisibleOutcome where
  seed := d
  response ω _ := FiniteKernel.pure ω
  accept _ _ := 1
  accept_bounds _ _ := by norm_num
  reported := d
  rate _ := 1
  rate_pos _ := by norm_num
  selected s o := by simp [FiniteKernel.bind_mass, mul_ite]

def jointResponse (d : LawTable) : Mechanism VisibleOutcome where
  seed _ := FiniteKernel.pure ⟨false,false,false,false⟩
  response _ s := d s
  accept _ _ := 1
  accept_bounds _ _ := by norm_num
  reported := d
  rate _ := 1
  rate_pos _ := by norm_num
  selected s o := by simp

private def uniformOutputs : FiniteDistribution VisibleOutcome where
  mass _ := 1/16
  nonneg _ := by norm_num
  total := by
    have hc : Fintype.card VisibleOutcome = 16 := by decide
    simp [hc]

def filtered (d : LawTable) : Mechanism VisibleOutcome where
  seed _ := uniformOutputs
  response ω _ := FiniteKernel.pure ω
  accept s o := (d s).mass o
  accept_bounds s o := ⟨(d s).nonneg o, mass_le_one (d s) o⟩
  reported := d
  rate _ := 1/16
  rate_pos _ := by norm_num
  selected s o := by simp [FiniteKernel.bind_mass, mul_ite, uniformOutputs]

private def constantTable (o : VisibleOutcome) : Strategy := ⟨o.a,o.d,o.b,o.b,o.c,o.c⟩
private theorem constant_visible (o : VisibleOutcome) (y z : Bool) :
    (constantTable o).visible y z = o := by
  rcases o with ⟨a,b,c,d⟩
  simp [constantTable, Strategy.visible]

theorem dependent_retained (d : LawTable) : LocalResponses (dependent d) ∧ Unfiltered (dependent d) := by
  exact ⟨⟨fun o _ => constantTable o, fun o e y z => by simp [dependent, constant_visible]⟩,
    fun _ _ => rfl⟩
theorem jointResponse_retained (d : LawTable) : Independent (jointResponse d) ∧ Unfiltered (jointResponse d) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
theorem filtered_retained (d : LawTable) : Independent (filtered d) ∧ LocalResponses (filtered d) := by
  exact ⟨fun _ _ => rfl, ⟨fun o _ => constantTable o,
    fun o e y z => by simp [filtered, constant_visible]⟩⟩

inductive Assumption | independent | localResponses | unfiltered deriving DecidableEq, Fintype

def Holds (law : Assumption) (m : Mechanism VisibleOutcome) : Prop :=
  match law with
  | .independent => Independent m
  | .localResponses => LocalResponses m
  | .unfiltered => Unfiltered m

def core : Finset Assumption := Finset.univ

def certificate (d : LawTable) (hq : Matches d) (hns : Within (behavior d) 0) :
    MinimalCore Holds Target core where
  excludes m hm := excludes m (hm .independent (by simp [core]))
    (hm .localResponses (by simp [core])) (hm .unfiltered (by simp [core]))
  deletionAdversary law _ := by
    cases law
    · refine ⟨dependent d, ?_, hq, hns⟩
      intro law hlaw
      cases law <;> simp_all [core, Holds, (dependent_retained d).1, (dependent_retained d).2]
    · refine ⟨jointResponse d, ?_, hq, hns⟩
      intro law hlaw
      cases law <;> simp_all [core, Holds, (jointResponse_retained d).1, (jointResponse_retained d).2]
    · refine ⟨filtered d, ?_, hq, hns⟩
      intro law hlaw
      cases law <;> simp_all [core, Holds, (filtered_retained d).1, (filtered_retained d).2]

/-- Any fourth premise is redundant for this same target once these three are
retained. Timing/intervention necessity needs a different target or language. -/
theorem no_fourth_premise_core (extra : Mechanism VisibleOutcome → Prop) :
    ¬ Nonempty (MinimalCore
      (fun law : Option Assumption => match law with | none => extra | some k => Holds k)
      Target Finset.univ) := by
  rintro ⟨c⟩
  obtain ⟨m,hm,ht⟩ := c.deletionAdversary none (Finset.mem_univ _)
  apply excludes m ?_ ?_ ?_ ht
  · exact hm (some .independent) (by simp)
  · exact hm (some .localResponses) (by simp)
  · exact hm (some .unfiltered) (by simp)

end
end OntologySeparation.ForcedSignalingAssumptionCore
