import OntologySeparation.LocalFriendliness

open OntologySeparation
open OntologySeparation.LocalFriendlinessRecipe

example : score Law.coherent reference = 1214656/180625 := coherent_score
example : ¬ LF.theory (interpret Law.coherent reference) := coherent_excludes_LF
example : profileTheory (FriendRecords.vocabulary (Λ := Bool × Bool)) FriendRecords.profile
    FriendRecords.Model.behavior (interpret (Law.recordDephasing 1 1 1) reference) :=
  fully_dephased_realizes_profile

example : score (Law.recordDephasing 1 0 4) reference = 1095424/180625 := by
  change score ⟨Recipes.Rate.fraction 1 4, Recipes.Rate.fraction 0 4⟩ reference = _
  rw [show Recipes.Rate.fraction 0 4 = Recipes.Rate.of 0 by norm_num [Recipes.Rate.fraction, Recipes.Rate.of], charlie_noise_score]
  norm_num [Recipes.Rate.fraction]

-- Explicit four-register operations recover the input and preserve its norm.
example (v : TwoQubit.Pure) : FriendProtocol.copyA (FriendProtocol.copyB (FriendProtocol.encode v.vector)) =
    FriendProtocol.blank v.vector := FriendProtocol.undo_friends _
example (v : TwoQubit.Pure) (a b : Bool) : FriendProtocol.encode v.vector (a,b,!a,b) = 0 := by
  cases a <;> simp [FriendProtocol.encode_entry]

-- Reading both records preserves populations, even when phases are lost.
example : probability Law.coherent reference (0,0) (false,false) = 9/50 := by lf_check
example : probability (Law.recordDephasing 1 1 1) reference (0,0) (false,false) = 9/50 := by lf_check
-- A mixed read/reverse branch is checked independently of the total LF score.
example : physicalProbability Law.coherent reference (0,1) (false,false) = 0 := by
  rw [probability_correct]
  lf_check
-- Reversing a dephased record cannot recover the lost interference.
example : probability (Law.recordDephasing 1 0 2) reference (1,2) (false,false) ≠
    probability Law.coherent reference (1,2) (false,false) := by lf_check
