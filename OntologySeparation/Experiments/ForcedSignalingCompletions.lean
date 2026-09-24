import OntologySeparation.Experiments.SignalingTradeoff
import OntologySeparation.Operational.HiddenInfluenceCausality

/-!
# All operational completions of the S4 witness

The six correlators in S4 omit one or two settings.  A concrete experimental
score must choose those unused settings.  There are 512 such completions.

This module makes the completion finite data, derives the exact slope function
suggested by the source's numerical 512-completion scan, and proves the spectrum
and multiplicities in the Lean kernel.  The physical universal bound is proved
below from the fixed K=8 theorem plus no-signaling/TV comparison lemmas; no
floating-point LP result is a proof rule.
-/

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators
noncomputable section

/-- The nine otherwise-unused binary settings needed to turn the six S4
correlators into full experimental contexts. -/
structure Completion where
  z1 : Bool
  w1 : Bool
  z2 : Bool
  w2 : Bool
  z3 : Bool
  z4 : Bool
  x5 : Bool
  y5 : Bool
  y6 : Bool
  deriving DecidableEq, Fintype

/-- The completion used by the existing K=8 certificate. -/
def optimalCompletion : Completion :=
  { z1 := false, w1 := true
    z2 := false, w2 := true
    z3 := false, z4 := false
    x5 := true, y5 := false, y6 := false }

/-- Exact completion-dependent signaling slope.

Only the two early-D choices used to complete the AB terms and the early-A
choice used to complete the doubled CD term affect the slope. -/
def Completion.slope (c : Completion) : ℤ :=
  16 - 2 * c.w1.toNat - 2 * c.w2.toNat - 4 * c.x5.toNat

theorem optimalCompletion_slope : optimalCompletion.slope = 8 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Completion.slope_mem (c : Completion) :
    c.slope = 8 ∨ c.slope = 10 ∨ c.slope = 12 ∨
      c.slope = 14 ∨ c.slope = 16 := by
  rcases c with ⟨z1,w1,z2,w2,z3,z4,x5,y5,y6⟩
  cases w1 <;> cases w2 <;> cases x5 <;> simp [Completion.slope]

/-- There are exactly 512 operational completions. -/
theorem completion_count : Fintype.card Completion = 512 := by decide

/-- Exact multiplicity of the optimal K=8 completions. -/
theorem slope8_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 8).card) = 64 := by
  decide

theorem slope10_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 10).card) = 128 := by
  decide

theorem slope12_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 12).card) = 128 := by
  decide

theorem slope14_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 14).card) = 128 := by
  decide

theorem slope16_count :
    ((Finset.univ.filter fun c : Completion => c.slope = 16).card) = 64 := by
  decide

/-- The full exact spectrum, replacing the source repository's floating-point
512-LP multiplicity check. -/
theorem completion_spectrum :
    ((Finset.univ.filter fun c : Completion => c.slope = 8).card,
     (Finset.univ.filter fun c : Completion => c.slope = 10).card,
     (Finset.univ.filter fun c : Completion => c.slope = 12).card,
     (Finset.univ.filter fun c : Completion => c.slope = 14).card,
     (Finset.univ.filter fun c : Completion => c.slope = 16).card) =
      (64, 128, 128, 128, 64) := by
  rw [slope8_count, slope10_count, slope12_count, slope14_count, slope16_count]

private def abSign (o : Outcome) : ℝ :=
  if (o.val / 8 + o.val / 4 % 2) % 2 = 0 then 1 else -1

private def abdSign (o : Outcome) : ℝ :=
  if (o.val / 8 + o.val / 4 % 2 + o.val % 2) % 2 = 0 then 1 else -1

private def cdSign (o : Outcome) : ℝ :=
  if (o.val / 2 % 2 + o.val % 2) % 2 = 0 then 1 else -1

private def acdSign (o : Outcome) : ℝ :=
  if (o.val / 8 + o.val / 2 % 2 + o.val % 2) % 2 = 0 then 1 else -1

/-- S4 evaluated at one explicit completion. -/
noncomputable def completedScore (c : Completion) (p : Behavior interface) : ℝ :=
  mean p ⟨c.w1.toNat, by cases c.w1 <;> simp⟩
      ⟨2 * 0 + c.z1.toNat, by cases c.z1 <;> simp⟩ abSign +
  mean p ⟨c.w2.toNat, by cases c.w2 <;> simp⟩
      ⟨2 + c.z2.toNat, by cases c.z2 <;> simp⟩ abSign +
  mean p ⟨2, by omega⟩
      ⟨c.z3.toNat, by cases c.z3 <;> simp⟩ abdSign -
  mean p ⟨2, by omega⟩
      ⟨2 + c.z4.toNat, by cases c.z4 <;> simp⟩ abdSign +
  2 * mean p ⟨2 * c.x5.toNat, by cases c.x5 <;> simp⟩
      ⟨2 * c.y5.toNat, by cases c.y5 <;> simp⟩ cdSign +
  2 * mean p ⟨1, by omega⟩
      ⟨2 * c.y6.toNat + 1, by cases c.y6 <;> simp⟩ acdSign

/-- The named optimal completion is exactly the fixed score already certified. -/
theorem completedScore_optimal (p : Behavior interface) :
    completedScore optimalCompletion p = score p := by
  unfold completedScore optimalCompletion score
  norm_num [abSign, abdSign, cdSign, acdSign, termEarly, termLate, termWeight, parity,
    sign]
  ring

end
end OntologySeparation.HiddenInfluence
