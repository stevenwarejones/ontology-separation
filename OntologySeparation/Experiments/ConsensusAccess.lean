import OntologySeparation.Experiments.ConsensusRecords

/-! Access accounting for redundant record fragments.

The accessible list records fragments the superobserver can coherently control.
Only inaccessible branch records suppress the recoverable fringe. Moving one
fragment from the inaccessible list to the accessible list removes exactly that
fragment's overlap factor from the residual visibility. This is still the
effective independent-record model; an explicit many-register quantum bridge is
a later milestone. -/
namespace OntologySeparation.ConsensusAccess
open Recipes

structure AccessModel where
  accessible : List Rate
  inaccessible : List Rate
  recovery : Rate

def residualVisibility (m : AccessModel) : ℚ :=
  (ConsensusRecords.aggregateVisibility m.inaccessible).value

def gap (m : AccessModel) : ℚ :=
  residualVisibility m * m.recovery.value / 2

def exposeOne (r : Rate) (visible hidden : List Rate) (recovery : Rate) : AccessModel where
  accessible := visible
  inaccessible := r :: hidden
  recovery := recovery

def recoverOne (r : Rate) (visible hidden : List Rate) (recovery : Rate) : AccessModel where
  accessible := r :: visible
  inaccessible := hidden
  recovery := recovery

/-- Moving one fragment under coherent control removes exactly its overlap
factor from the residual visibility. -/
theorem residual_before_eq_overlap_mul_after
    (r : Rate) (visible hidden : List Rate) (recovery : Rate) :
    residualVisibility (exposeOne r visible hidden recovery) =
      r.value * residualVisibility (recoverOne r visible hidden recovery) := by
  rfl

/-- The same exact relation holds for the physical recovery gap. -/
theorem gap_before_eq_overlap_mul_after
    (r : Rate) (visible hidden : List Rate) (recovery : Rate) :
    gap (exposeOne r visible hidden recovery) =
      r.value * gap (recoverOne r visible hidden recovery) := by
  unfold gap
  rw [residual_before_eq_overlap_mul_after]
  ring

/-- A perfectly distinguishing record left outside coherent control kills the
fringe regardless of all other hidden records and recovery quality. -/
theorem inaccessible_perfect_record_zero
    (visible before after : List Rate) (recovery : Rate) :
    gap {
      accessible := visible
      inaccessible := before ++ Rate.of 0 :: after
      recovery := recovery
    } = 0 := by
  unfold gap residualVisibility
  rw [ConsensusRecords.perfect_record_zero]
  ring

/-- If the only inaccessible perfect record is brought under coherent control
and recovery is perfect, the ideal 1/2 fringe is restored. -/
theorem recover_last_perfect_record :
    gap (recoverOne (Rate.of 0) [] [] (Rate.of 1)) = 1 / 2 := by
  norm_num [gap, residualVisibility, recoverOne,
    ConsensusRecords.aggregateVisibility, Rate.of]

/-- Conversely, before recovering that same final perfect record the fringe is
exactly zero. -/
theorem before_recover_last_perfect_record :
    gap (exposeOne (Rate.of 0) [] [] (Rate.of 1)) = 0 := by
  norm_num [gap, residualVisibility, exposeOne,
    ConsensusRecords.aggregateVisibility, Rate.of]

/-- If every inaccessible fragment is a perfect record, positive visibility is
possible exactly when there are no inaccessible fragments left. -/
theorem perfect_hidden_positive_iff_empty
    (hidden : List Rate)
    (hperfect : ∀ r ∈ hidden, r.value = 0) :
    0 < (ConsensusRecords.aggregateVisibility hidden).value ↔ hidden = [] := by
  constructor
  · intro hpos
    cases hidden with
    | nil => rfl
    | cons r rs =>
        have hr : r.value = 0 := hperfect r (by simp)
        simp [ConsensusRecords.aggregateVisibility, PartialLeakage.Rate.mul, hr] at hpos
  · intro hempty
    subst hidden
    norm_num [ConsensusRecords.aggregateVisibility]

/-- In the perfect-record limit, a positive laboratory fringe requires that the
inaccessible record list be empty. -/
theorem perfect_hidden_gap_positive_implies_empty
    (m : AccessModel)
    (hperfect : ∀ r ∈ m.inaccessible, r.value = 0)
    (hrecovery : 0 < m.recovery.value)
    (hgap : 0 < gap m) :
    m.inaccessible = [] := by
  have hvis : 0 < residualVisibility m := by
    unfold gap at hgap
    unfold residualVisibility
    by_contra hn
    have hz : (ConsensusRecords.aggregateVisibility m.inaccessible).value = 0 := by
      have hnonneg := (ConsensusRecords.aggregateVisibility m.inaccessible).nonneg
      push_neg at hn
      linarith
    rw [hz] at hgap
    norm_num at hgap
  exact (perfect_hidden_positive_iff_empty m.inaccessible hperfect).mp hvis

end OntologySeparation.ConsensusAccess
