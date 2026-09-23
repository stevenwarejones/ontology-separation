import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Experiments.PartialLeakage

/-! A first consensus/objectivity benchmark with redundant inaccessible records.

Each record contributes an overlap in [0,1].  Independent record leakage composes
multiplicatively, using the already checked sequential-dephasing mechanism.  This
is a restricted branching/decoherence model, not a general theorem about quantum
Darwinism. -/
namespace OntologySeparation.ConsensusRecords
open AdversarySearch
open Recipes

/-- Effective visibility left after all inaccessible record fragments. -/
def aggregateVisibility : List Rate → Rate
  | [] => Rate.of 1
  | r :: rs => PartialLeakage.Rate.mul r (aggregateVisibility rs)

@[simp] theorem aggregateVisibility_nil :
    (aggregateVisibility []).value = 1 := rfl

@[simp] theorem aggregateVisibility_cons (r : Rate) (rs : List Rate) :
    (aggregateVisibility (r :: rs)).value =
      r.value * (aggregateVisibility rs).value := rfl

theorem aggregateVisibility_append (xs ys : List Rate) :
    (aggregateVisibility (xs ++ ys)).value =
      (aggregateVisibility xs).value * (aggregateVisibility ys).value := by
  induction xs with
  | nil => simp [aggregateVisibility]
  | cons x xs ih =>
      simp [aggregateVisibility, PartialLeakage.Rate.mul, ih, mul_assoc]

/-- One perfectly distinguishing inaccessible record kills the residual
coherence, regardless of all other record qualities. -/
theorem perfect_record_zero (before after : List Rate) :
    (aggregateVisibility (before ++ Rate.of 0 :: after)).value = 0 := by
  rw [aggregateVisibility_append]
  simp [aggregateVisibility, PartialLeakage.Rate.mul, Rate.of]

structure Mechanism where
  records : List Rate
  recovery : Rate

def Mechanism.asLeakage (m : Mechanism) : PartialLeakage.Mechanism where
  visibility := aggregateVisibility m.records
  recovery := m.recovery

/-- Exact recoverable interference gap in the existing physical recipe backend. -/
def gap (m : Mechanism) : ℚ :=
  (aggregateVisibility m.records).value * m.recovery.value / 2

theorem gap_is_physical (m : Mechanism) :
    probability m.asLeakage.wignerLaw coherenceProbe -
      probability PartialLeakage.friendLaw coherenceProbe = gap m := by
  simpa [Mechanism.asLeakage, gap] using
    PartialLeakage.recovery_gap m.asLeakage

theorem perfect_record_zero_gap (m : Mechanism) (before after : List Rate)
    (h : m.records = before ++ Rate.of 0 :: after) :
    gap m = 0 := by
  rw [gap, h, perfect_record_zero]
  ring

def noCopies : Mechanism where
  records := []
  recovery := Rate.of 1

theorem noCopies_gap : gap noCopies = 1 / 2 := by
  norm_num [gap, noCopies, aggregateVisibility, Rate.of]

/-- The assumption tested by the first adversary pass: at least one inaccessible
fragment carries a perfectly distinguishing record. Access is fixed to the
laboratory-only model encoded by PartialLeakage. -/
inductive Law where
  | perfectHiddenRecord
  deriving DecidableEq, Repr

def Holds : Law → Mechanism → Prop
  | .perfectHiddenRecord, m =>
      ∃ before after, m.records = before ++ Rate.of 0 :: after

def Target (m : Mechanism) : Prop := 0 < gap m

def core : Finset Law := {.perfectHiddenRecord}

/-- Within the stated laboratory-only mechanism class, the perfect-hidden-record
premise is deletion-minimal for excluding a positive recovery fringe. -/
def certificate : MinimalCore Holds Target core where
  excludes := by
    intro m hm ht
    have hmem : Law.perfectHiddenRecord ∈ core := by simp [core]
    obtain ⟨before, after, hrecords⟩ := hm .perfectHiddenRecord hmem
    have hz := perfect_record_zero_gap m before after hrecords
    unfold Target at ht
    rw [hz] at ht
    exact (lt_irrefl 0) ht
  deletionAdversary := by
    intro law hlaw
    cases law with
    | perfectHiddenRecord =>
        refine ⟨noCopies, ?_, ?_⟩
        · intro kept hkept
          cases kept
          simp [core] at hkept
        · unfold Target
          rw [noCopies_gap]
          norm_num

theorem perfect_record_core :
    (∀ m, Satisfies Holds core m → ¬ Target m) ∧
    (∃ m, Satisfies Holds (core.erase .perfectHiddenRecord) m ∧ Target m) := by
  constructor
  · exact certificate.excludes
  · exact certificate.deletionAdversary .perfectHiddenRecord (by simp [core])

end OntologySeparation.ConsensusRecords
