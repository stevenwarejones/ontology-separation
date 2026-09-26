import OntologySeparation.Experiments.ForcedSignalingAssumptionCore
import OntologySeparation.Experiments.LC4FullDistribution

namespace OntologySeparation.ForcedSignalingLC4MinimalCore
noncomputable section
open scoped BigOperators
open HiddenInfluence VCausal ForcedSignalingLC4Witness ForcedSignalingLC4
open ForcedSignalingAssumptionCore LC4FullDistribution AdversarySearch

def quantumLaw : LawTable := fun s => quantum s.1 s.2.1 s.2.2

theorem quantum_matches : Matches quantumLaw := by
  constructor
  · intro x y z w a b d
    simpa [quantumLaw, FiniteKernel.map_mass, recordProb, mul_ite] using quantum_abd x y z w a b d
  · intro x y z w a c d
    simpa [quantumLaw, FiniteKernel.map_mass, recordProb, mul_ite] using quantum_acd x y z w a c d

set_option maxHeartbeats 0 in
private theorem marginal_A (d : LawTable) (e : Early) (y z : Bool) (r : Recipient) :
    marginal (behavior d) e (lateFromBool y z) recipientA r =
      ∑ a : Bool, (d (e,y,z)).mass ⟨a,decide (r.val / 4 = 1),
        decide (r.val / 2 % 2 = 1),decide (r.val % 2 = 1)⟩ := by
  have hl : lateY (lateFromBool y z) = y ∧ lateZ (lateFromBool y z) = z := by
    cases y <;> cases z <;> decide
  fin_cases r <;>
    norm_num [marginal, mean, behavior, hl, interface, Outcome, Fin.sum_univ_succ,
      recipientA, outcomeToVisible, Fintype.sum_bool, add_comm] <;>
    (simp only [Fin.sum_univ_succ]; norm_num [Fin.sum_univ_succ])

set_option maxHeartbeats 0 in
private theorem marginal_D (d : LawTable) (e : Early) (y z : Bool) (r : Recipient) :
    marginal (behavior d) e (lateFromBool y z) recipientD r =
      ∑ dd : Bool, (d (e,y,z)).mass ⟨decide (r.val / 4 = 1),
        decide (r.val / 2 % 2 = 1),decide (r.val % 2 = 1),dd⟩ := by
  have hl : lateY (lateFromBool y z) = y ∧ lateZ (lateFromBool y z) = z := by
    cases y <;> cases z <;> decide
  fin_cases r <;>
    norm_num [marginal, mean, behavior, hl, interface, Outcome, Fin.sum_univ_succ,
      recipientD, outcomeToVisible, Fintype.sum_bool, add_comm] <;>
    (simp only [Fin.sum_univ_succ]; norm_num [Fin.sum_univ_succ])

theorem quantum_zero_signal : Within (behavior quantumLaw) 0 := by
  have hA : ∀ y z w r,
      marginal (behavior quantumLaw) (earlyOf false w) (lateFromBool y z) recipientA r =
      marginal (behavior quantumLaw) (earlyOf true w) (lateFromBool y z) recipientA r := by
    intro y z w r
    simp only [marginal_A, quantumLaw, quantum_noSignalA]
  have hD : ∀ x y z r,
      marginal (behavior quantumLaw) (earlyOf x false) (lateFromBool y z) recipientD r =
      marginal (behavior quantumLaw) (earlyOf x true) (lateFromBool y z) recipientD r := by
    intro x y z r
    simp only [marginal_D, quantumLaw, quantum_noSignalD]
  have hd : ∀ c r, difference (behavior quantumLaw) c r = 0 := by
    intro c r
    fin_cases c
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA false false false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA false true false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA true false false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA true true false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA false false true r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA false true true r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA true false true r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hA true true true r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD false false false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD false false true r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD false true false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD false true true r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD true false false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD true false true r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD true true false r)
    · simpa [difference, contextEarly, contextLate, project, earlyOf, lateFromBool] using sub_eq_zero.mpr (hD true true true r)
  intro c
  simp [tv, hd]

/-- Each of the three premises is necessary for the exact LC4 marginal target
with zero A/D recipient TV. All three countermodels report the full Born law. -/
def minimalCore : MinimalCore Holds Target core :=
  certificate quantumLaw quantum_matches quantum_zero_signal

theorem deletion_witness (law : Assumption) :
    ∃ m, Satisfies Holds (core.erase law) m ∧ Target m ∧ ¬ Holds law m := by
  obtain ⟨m,hm,ht⟩ := minimalCore.deletionAdversary law (by simp [core])
  refine ⟨m,hm,ht,?_⟩
  intro hl
  apply minimalCore.excludes m ?_ ht
  intro k hk
  by_cases h : k = law
  · simpa [h] using hl
  · exact hm k (Finset.mem_erase.mpr ⟨h,hk⟩)

end
end OntologySeparation.ForcedSignalingLC4MinimalCore
