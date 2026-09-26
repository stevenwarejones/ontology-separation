import OntologySeparation.Experiments.ForcedSignalingPropositions
import OntologySeparation.Experiments.ForcedSignalingCollectibility

/-! Proposition 2's full layout-dependent minimum. Every nonempty subset of
recipients is indexed: `none` is the full triple, `some s` runs over the three
singles and three pairs, using the same outcome coding as the checked invisible
certificates. Empty or uncollectible families contribute zero. -/
namespace OntologySeparation.ForcedSignalingAccessibleOptimum
noncomputable section
open scoped BigOperators
open HiddenInfluence VCausal ForcedSignalingCollectibility
open ForcedSignalingDirectional ForcedSignalingCertificateModel ForcedSignalingPropositions
open ForcedSignalingPropositionWitnesses

abbrev RecordChoice := Option (Fin 6)

def properParties (a b d : Party) (s : Fin 6) : Finset Party :=
  if s.val = 0 then {a} else if s.val = 1 then {b} else if s.val = 2 then {d}
  else if s.val = 3 then {a,b} else if s.val = 4 then {a,d} else {b,d}

def recordParties (c : Context) : RecordChoice → Finset Party
  | none => if c.val < 8 then {.B,.C,.D} else {.A,.B,.C}
  | some s => if c.val < 8 then properParties .B .C .D s else properParties .A .B .C s

/-- The seven choices enumerate all nonempty recipient sets excluding the sender. -/
theorem recordParties_complete : ∀ (c : Context) (R : Finset Party),
    R.Nonempty → sender c ∉ R → ∃ r : RecordChoice, recordParties c r = R := by
  decide +kernel

def outcomeBit (o : Outcome) : Party → ℕ
  | .A => o.val / 8 | .B => o.val / 4 % 2 | .C => o.val / 2 % 2 | .D => o.val % 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The proper-record code identifies exactly the bits in the named recipient
set; unused single-bit labels in Fin 4 add only zero-probability entries. -/
theorem proper_encoding : ∀ (aSender : Bool) (s : Fin 6) (o o' : Outcome),
    (if aSender then projectAProper s o else projectDProper s o) =
      (if aSender then projectAProper s o' else projectDProper s o') ↔
    ∀ p ∈ (if aSender then properParties .B .C .D s else properParties .A .B .C s),
      outcomeBit o p = outcomeBit o' p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_encoding : ∀ (aSender : Bool) (o o' : Outcome),
    (if aSender then recipientA o else recipientD o) =
      (if aSender then recipientA o' else recipientD o') ↔
    ∀ p ∈ (if aSender then ({.B,.C,.D} : Finset Party) else {.A,.B,.C}),
      outcomeBit o p = outcomeBit o' p := by
  decide +kernel

attribute [local instance] Classical.propDecidable

def properTV (m : Model) (c : Context) (s : Fin 6) : ℝ :=
  (∑ o : Fin 4, |marginal4 m.behavior (contextEarly c false) (contextLate c)
      (if c.val < 8 then projectAProper s else projectDProper s) o -
    marginal4 m.behavior (contextEarly c true) (contextLate c)
      (if c.val < 8 then projectAProper s else projectDProper s) o|) / 2

def recordTV (m : Model) (c : Context) : RecordChoice → ℝ
  | none => tv m.behavior c
  | some s => properTV m c s

def accessible (m : Model) (L : Layout) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun cr : Context × RecordChoice =>
    if Collectible (L (sender cr.1)) ((recordParties cr.1 cr.2).image L)
    then recordTV m cr.1 cr.2 else 0

private theorem recordTV_nonneg (m : Model) (c : Context) (r : RecordChoice) :
    0 ≤ recordTV m c r := by
  cases r <;> simp only [recordTV,properTV,tv] <;> positivity

theorem accessible_nonnegative (m : Model) (L : Layout) : 0 ≤ accessible m L := by
  apply le_trans (b := if Collectible (L (sender 0)) ((recordParties 0 none).image L)
    then recordTV m 0 none else 0)
  · split_ifs <;> first | exact recordTV_nonneg _ _ _ | rfl
  · unfold accessible
    exact Finset.le_sup' (fun cr : Context × RecordChoice =>
      if Collectible (L (sender cr.1)) ((recordParties cr.1 cr.2).image L)
      then recordTV m cr.1 cr.2 else 0) (Finset.mem_univ ((0 : Context), (none : RecordChoice)))

private theorem full_collectible (L : Layout) (c : Context) :
    Collectible (L (sender c)) ((recordParties c none).image L) ↔
      Collectible (L (sender c)) (recipients L c) := by
  by_cases h : c.val < 8 <;> simp [recordParties,recipients,h]

private theorem properTV_zero (m : Model) (h : PairwiseInvisible m)
    (c : Context) (s : Fin 6) : properTV m c s = 0 := by
  have he : ∀ o : Fin 4,
      marginal4 m.behavior (contextEarly c false) (contextLate c)
        (if c.val < 8 then projectAProper s else projectDProper s) o =
      marginal4 m.behavior (contextEarly c true) (contextLate c)
        (if c.val < 8 then projectAProper s else projectDProper s) o := by
    intro o
    fin_cases c
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s false false false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s false false true o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s false true false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s false true true o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s true false false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s true false true o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s true true false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properA s true true true o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s false false false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s false false true o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s false true false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s false true true o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s true false false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s true false true o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s true true false o
    · simpa [contextEarly,contextLate,ForcedSignalingLC4Witness.earlyOf,ForcedSignalingLC4Witness.lateOf] using h.properD s true true true o
  unfold properTV
  simp_rw [he]
  simp

/-- For a pairwise-invisible model only collectible full triples contribute. -/
theorem accessible_invisible (m : Model) (h : PairwiseInvisible m) (L : Layout) :
    accessible m L =
      max (if Collectible (L .A) {L .B,L .C,L .D} then deltaA m else 0)
          (if Collectible (L .D) {L .A,L .B,L .C} then deltaD m else 0) := by
  have hA0 : 0 ≤ if Collectible (L .A) {L .B,L .C,L .D} then deltaA m else 0 := by
    split_ifs <;> first | exact deltaA_nonnegative m | rfl
  have hD0 : 0 ≤ if Collectible (L .D) {L .A,L .B,L .C} then deltaD m else 0 := by
    split_ifs <;> first | exact deltaD_nonnegative m | rfl
  apply le_antisymm
  · apply Finset.sup'_le
    rintro ⟨c,r⟩ _
    cases r with
    | some s =>
      simp only [recordTV,properTV_zero m h,ite_self]
      exact le_trans hA0 (le_max_left _ _)
    | none =>
      rw [full_collectible]
      by_cases hc : c.val < 8
      · let i : Fin 8 := ⟨c.val,hc⟩
        have hi : contextA i = c := by apply Fin.ext; rfl
        simp only [sender,recipients,hc,if_true,if_false,recordTV]
        by_cases hh : Collectible (L .A) {L .B,L .C,L .D}
        · simp only [if_pos hh]
          exact le_trans (by simpa [hi] using tv_le_deltaA m i) (le_max_left _ _)
        · simp only [if_neg hh]
          exact le_max_left _ _
      · let i : Fin 8 := ⟨c.val-8,by omega⟩
        have hi : contextD i = c := by apply Fin.ext; dsimp [contextD,i]; omega
        simp only [sender,recipients,hc,if_true,if_false,recordTV]
        by_cases hh : Collectible (L .D) {L .A,L .B,L .C}
        · simp only [if_pos hh]
          exact le_trans (by simpa [hi] using tv_le_deltaD m i) (le_max_right _ _)
        · simp only [if_neg hh]
          exact le_max_right _ _
  · apply max_le
    · split_ifs with hh
      · apply Finset.sup'_le
        intro i _
        have hc : Collectible (L (sender (contextA i)))
            ((recordParties (contextA i) none).image L) := by
          simpa [sender,recordParties,contextA,i.isLt] using hh
        have := Finset.le_sup' (fun cr : Context × RecordChoice =>
          if Collectible (L (sender cr.1)) ((recordParties cr.1 cr.2).image L)
          then recordTV m cr.1 cr.2 else 0) (Finset.mem_univ (contextA i,none))
        simpa only [hc,if_pos,recordTV] using this
      · exact accessible_nonnegative m L
    · split_ifs with hh
      · apply Finset.sup'_le
        intro i _
        have hn : ¬ (contextD i).val < 8 := by simp [contextD]
        have hc : Collectible (L (sender (contextD i)))
            ((recordParties (contextD i) none).image L) := by
          simpa [sender,recordParties,hn] using hh
        have := Finset.le_sup' (fun cr : Context × RecordChoice =>
          if Collectible (L (sender cr.1)) ((recordParties cr.1 cr.2).image L)
          then recordTV m cr.1 cr.2 else 0) (Finset.mem_univ (contextD i,none))
        simpa only [hc,if_pos,recordTV] using this
      · exact accessible_nonnegative m L

private theorem signaling_le_accessible (m : Model) (L : Layout) (hL : BothCollectible L) :
    m.signaling ≤ accessible m L := by
  apply Finset.sup'_le
  intro c _
  have hc := (full_collectible L c).mpr (both_collectible_context hL c)
  have := Finset.le_sup' (fun cr : Context × RecordChoice =>
    if Collectible (L (sender cr.1)) ((recordParties cr.1 cr.2).image L)
    then recordTV m cr.1 cr.2 else 0) (Finset.mem_univ (c,none))
  simpa only [hc,if_pos,recordTV] using this

/-- The complete piecewise minimum in Proposition 2, with attained minima.
This is a theorem over the finite conditional-local class in rational 1+1
layouts, not a claim about adaptive or repeated communication tasks. -/
theorem proposition2_layout_minimum (L : Layout) :
    (∀ m : Model, ForcedSignalingTheorem2.MatchesCluster m →
      (if BothCollectible L then (Real.sqrt 2-1)/4 else 0) ≤ accessible m L) ∧
    ∃ m : Model, ForcedSignalingTheorem2.MatchesCluster m ∧
      accessible m L = if BothCollectible L then (Real.sqrt 2-1)/4 else 0 := by
  constructor
  · intro m hm
    split_ifs with hL
    · have hb := ForcedSignalingTheorem2.lower_bound hm
      rw [ForcedSignalingTheorem2.targetDelta_value] at hb
      exact le_trans hb (signaling_le_accessible m L hL)
    · exact accessible_nonnegative m L
  · by_cases hL : BothCollectible L
    · refine ⟨InvisibleBalanced.model,InvisibleBalanced.matchesCluster,?_⟩
      rw [accessible_invisible _ invisibleBalanced, if_pos hL,
        if_pos hL.1, if_pos hL.2, InvisibleBalanced.deltaA_exact,
        InvisibleBalanced.deltaD_exact, InvisibleBalanced.delta_value, max_self]
    · rw [if_neg hL]
      by_cases hA : Collectible (L .A) {L .B,L .C,L .D}
      · have hD : ¬ Collectible (L .D) {L .A,L .B,L .C} := fun hD => hL ⟨hA,hD⟩
        refine ⟨InvisibleD.model,InvisibleD.matchesCluster,?_⟩
        rw [accessible_invisible _ invisibleD, if_pos hA, if_neg hD, InvisibleD.deltaA_exact]
        norm_num
      · refine ⟨InvisibleA.model,InvisibleA.matchesCluster,?_⟩
        rw [accessible_invisible _ invisibleA, if_neg hA, InvisibleA.deltaD_exact]
        split_ifs <;> norm_num

/-- The same attained minimum for the full finite stochastic conditional-local
class, through its behavior-preserving determinization. -/
theorem stochastic_layout_minimum (L : Layout) :
    (∀ (Ω : Type) [Fintype Ω] (m : StochasticModel Ω),
      ForcedSignalingTheorem2.StochasticMatchesCluster m →
      (if BothCollectible L then (Real.sqrt 2-1)/4 else 0) ≤ accessible m.determinize L) ∧
    ∃ m : StochasticModel Strategy,
      ForcedSignalingTheorem2.StochasticMatchesCluster m ∧
      accessible m.determinize L = if BothCollectible L then (Real.sqrt 2-1)/4 else 0 := by
  constructor
  · intro Ω _ m hm
    exact (proposition2_layout_minimum L).1 m.determinize hm.toMatchesCluster
  · obtain ⟨m,hm,ha⟩ := (proposition2_layout_minimum L).2
    let sm := StochasticModel.ofStrategies m.toStrategies
    have ext : ∀ m n : Model, (∀ j, m.weight j = n.weight j) → m = n := by
      rintro ⟨a,ha,ta⟩ ⟨b,hb,tb⟩ h
      have he : a = b := funext h
      cases he
      rfl
    have he : sm.determinize = m := ext _ _ m.stochastic_roundtrip_weight
    refine ⟨sm,?_,?_⟩
    · constructor
      · intro x y w a b d
        change ForcedSignalingLC4Witness.modelABD sm.determinize x y w a b d = _
        rw [he]
        exact hm.abd x y w a b d
      · intro x z w a c d
        change ForcedSignalingLC4Witness.modelACD sm.determinize x z w a c d = _
        rw [he]
        exact hm.acd x z w a c d
    · rw [he]
      exact ha

end
end OntologySeparation.ForcedSignalingAccessibleOptimum
