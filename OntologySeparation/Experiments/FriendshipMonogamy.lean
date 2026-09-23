import OntologySeparation.Experiments.ConsensusAccess

/-! Access-relative recovery monogamy for a shared durable friend record.

This is deliberately narrower than generic LF monogamy, which is established prior
art.  Here two superobservers compete for coherent access to the *same* finite set
of durable record fragments.  A perfectly distinguishing record that cannot be
coherently shared makes simultaneous positive recovery impossible.

The result lives in the effective independent-overlap model of ConsensusAccess;
it is not yet a many-register Hilbert-space theorem. -/

namespace OntologySeparation.FriendshipMonogamy
noncomputable section

open AdversarySearch
open Recipes

variable {ι : Type} [Fintype ι] [DecidableEq ι]

structure Model (ι : Type) [Fintype ι] [DecidableEq ι] where
  overlap : ι → Rate
  accessA : Finset ι
  accessB : Finset ι
  recoveryA : Rate
  recoveryB : Rate

def residual (m : Model ι) (access : Finset ι) : ℚ :=
  ∏ i : ι, if i ∈ access then 1 else (m.overlap i).value

def gapFor (m : Model ι) (access : Finset ι) (recovery : Rate) : ℚ :=
  residual m access * recovery.value / 2

def gapA (m : Model ι) : ℚ := gapFor m m.accessA m.recoveryA
def gapB (m : Model ι) : ℚ := gapFor m m.accessB m.recoveryB

theorem residual_zero_of_perfect_inaccessible
    (m : Model ι) (access : Finset ι) (k : ι)
    (hk : (m.overlap k).value = 0) (hka : k ∉ access) :
    residual m access = 0 := by
  unfold residual
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hka, hk]

theorem gap_zero_of_perfect_inaccessible
    (m : Model ι) (access : Finset ι) (recovery : Rate) (k : ι)
    (hk : (m.overlap k).value = 0) (hka : k ∉ access) :
    gapFor m access recovery = 0 := by
  unfold gapFor
  rw [residual_zero_of_perfect_inaccessible m access k hk hka]
  ring

/-- With disjoint coherent-control sets, a perfect durable record forces at least
one superobserver's recovery fringe to vanish. -/
theorem disjoint_access_monogamy
    (m : Model ι)
    (hperfect : ∃ k, (m.overlap k).value = 0)
    (hdisjoint : Disjoint m.accessA m.accessB) :
    gapA m = 0 ∨ gapB m = 0 := by
  obtain ⟨k, hk⟩ := hperfect
  by_cases hA : k ∈ m.accessA
  · have hB : k ∉ m.accessB := by
      intro hkB
      exact Finset.disjoint_left.mp hdisjoint hA hkB
    right
    exact gap_zero_of_perfect_inaccessible m m.accessB m.recoveryB k hk hB
  · left
    exact gap_zero_of_perfect_inaccessible m m.accessA m.recoveryA k hk hA

inductive Law where
  | perfectDurableRecord
  | disjointCoherentAccess
  deriving DecidableEq, Repr

def Holds : Law → Model ι → Prop
  | .perfectDurableRecord, m => ∃ k, (m.overlap k).value = 0
  | .disjointCoherentAccess, m => Disjoint m.accessA m.accessB

def Target (m : Model ι) : Prop := 0 < gapA m ∧ 0 < gapB m

def core : Finset Law := {.perfectDurableRecord, .disjointCoherentAccess}

/-- Two fragments make the premise-deletion adversaries explicit. -/
abbrev WitnessIndex := Fin 2

def sharedPerfect : Model WitnessIndex where
  overlap := fun i => if i = 0 then Rate.of 0 else Rate.of 1
  accessA := {0}
  accessB := {0}
  recoveryA := Rate.of 1
  recoveryB := Rate.of 1

def disjointNoPerfect : Model WitnessIndex where
  overlap := fun _ => Rate.of 1
  accessA := {0}
  accessB := {1}
  recoveryA := Rate.of 1
  recoveryB := Rate.of 1

theorem sharedPerfect_target : Target sharedPerfect := by
  constructor <;>
    norm_num [Target, gapA, gapB, gapFor, residual, sharedPerfect,
      Rate.of, PartialLeakage.Rate.mul]

theorem sharedPerfect_has_perfect : Holds .perfectDurableRecord sharedPerfect := by
  refine ⟨0, ?_⟩
  norm_num [Holds, sharedPerfect, Rate.of]

theorem disjointNoPerfect_target : Target disjointNoPerfect := by
  constructor <;>
    norm_num [Target, gapA, gapB, gapFor, residual, disjointNoPerfect,
      Rate.of, PartialLeakage.Rate.mul]

theorem disjointNoPerfect_disjoint :
    Holds .disjointCoherentAccess disjointNoPerfect := by
  simp [Holds, disjointNoPerfect, Finset.disjoint_left]

/-- The two-law access-relative monogamy obstruction is deletion-minimal in this
effective record model. -/
def certificate : MinimalCore (Holds (ι := WitnessIndex)) Target core where
  excludes := by
    intro m hm ht
    have hp : Holds .perfectDurableRecord m :=
      hm .perfectDurableRecord (by simp [core])
    have hd : Holds .disjointCoherentAccess m :=
      hm .disjointCoherentAccess (by simp [core])
    have hz := disjoint_access_monogamy m hp hd
    unfold Target at ht
    rcases hz with hA | hB
    · rw [hA] at ht
      exact (lt_irrefl 0) ht.1
    · rw [hB] at ht
      exact (lt_irrefl 0) ht.2
  deletionAdversary := by
    intro law hlaw
    cases law with
    | perfectDurableRecord =>
        refine ⟨disjointNoPerfect, ?_, disjointNoPerfect_target⟩
        intro kept hkept
        cases kept with
        | perfectDurableRecord => simp [core] at hkept
        | disjointCoherentAccess => exact disjointNoPerfect_disjoint
    | disjointCoherentAccess =>
        refine ⟨sharedPerfect, ?_, sharedPerfect_target⟩
        intro kept hkept
        cases kept with
        | perfectDurableRecord => exact sharedPerfect_has_perfect
        | disjointCoherentAccess => simp [core] at hkept

theorem access_monogamy_minimal :
    (∀ m, Satisfies (Holds (ι := WitnessIndex)) core m → ¬ Target m) ∧
    (∃ m, Satisfies (Holds (ι := WitnessIndex))
      (core.erase .perfectDurableRecord) m ∧ Target m) ∧
    (∃ m, Satisfies (Holds (ι := WitnessIndex))
      (core.erase .disjointCoherentAccess) m ∧ Target m) := by
  refine ⟨certificate.excludes, ?_, ?_⟩
  · exact certificate.deletionAdversary .perfectDurableRecord (by simp [core])
  · exact certificate.deletionAdversary .disjointCoherentAccess (by simp [core])

end
end OntologySeparation.FriendshipMonogamy
