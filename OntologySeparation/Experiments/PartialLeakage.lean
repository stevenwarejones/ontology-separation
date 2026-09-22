import OntologySeparation.Recipes.Separation
import Mathlib.Tactic

/-! A mechanistic partial-information-leakage model for the single-qubit
Wigner/friend showcase.

The product law is an explicit modeling assumption, realized below by
sequential dephasing channels. Visibility is the coherence/which-outcome visibility retained
after information leaks from the friend's record, while recovery is the
fraction of that retained coherence accessible to the superobserver's reversal.
Their product determines the recoverable coherence. -/
namespace OntologySeparation.PartialLeakage
open Recipes RecipeSeparation

/-- Product of two physical rates remains a physical rate. -/
def Rate.mul (a b : Rate) : Rate where
  value := a.value * b.value
  nonneg := mul_nonneg a.nonneg b.nonneg
  le_one := by nlinarith [a.nonneg, a.le_one, b.nonneg, b.le_one]

/-- Complement of a physical rate. -/
def Rate.complement (a : Rate) : Rate where
  value := 1 - a.value
  nonneg := sub_nonneg.mpr a.le_one
  le_one := by linarith [a.nonneg]

/-- Partial leakage plus imperfect coherent recovery.

Visibility 1 means no which-outcome information has leaked; visibility 0 means
the relevant coherence is completely unavailable. Recovery 1 means the
available coherence is fully used by the recovery operation; recovery 0 means
none of it is recovered. -/
structure Mechanism where
  visibility : Rate
  recovery : Rate

def Mechanism.recoverableCoherence (m : Mechanism) : Rate :=
  Rate.mul m.visibility m.recovery

/-- The existing dephasing law sees the complement of recoverable coherence as
effective exposure. This connects the mechanism to the already-proved physical
real-qubit recipe semantics rather than defining a new probability rule. -/
def Mechanism.wignerLaw (m : Mechanism) : Law :=
  ⟨Rate.complement m.recoverableCoherence⟩

/-- The friend's collapsed prediction is the fully dephased law. -/
def friendLaw : Law := Law.dephasing 1 1

theorem recoverableCoherence_value (m : Mechanism) :
    m.recoverableCoherence.value = m.visibility.value * m.recovery.value := rfl

theorem effective_exposure (m : Mechanism) :
    m.wignerLaw.exposure.value =
      1 - m.visibility.value * m.recovery.value := rfl

/-- The calibration experiment remains insensitive to leakage and recovery. -/
theorem calibration_agreement (m : Mechanism) :
    probability m.wignerLaw calibrationProbe = probability friendLaw calibrationProbe := by
  rw [calibration_probability, calibration_probability]

/-- The recovery-probe probability is derived from the existing exact recipe
semantics. It is not inserted as a separate phenomenological formula. -/
theorem recovery_probability (m : Mechanism) :
    probability m.wignerLaw coherenceProbe =
      (1 + m.visibility.value * m.recovery.value) / 2 := by
  rw [coherence_probability]
  simp [Mechanism.wignerLaw, Mechanism.recoverableCoherence, Rate.complement, Rate.mul]
  ring

theorem friend_probability :
    probability friendLaw coherenceProbe = 1 / 2 := by
  rw [coherence_probability]
  norm_num [friendLaw, Law.dephasing, Rate.fraction]

/-- Exact oriented gap between the Wigner/recovery prediction and the friend's
fully dephased prediction. -/
theorem recovery_gap (m : Mechanism) :
    probability m.wignerLaw coherenceProbe - probability friendLaw coherenceProbe =
      (m.visibility.value * m.recovery.value) / 2 := by
  rw [recovery_probability, friend_probability]
  ring

/-- Explicit realization of the assumed product law as two sequential dephasing
channels. This models coherence attenuation, not an optimized recovery protocol. -/
theorem sequential_attenuation (m : Mechanism) :
    (Qubit.experiment ((Qubit.dephase (Rate.complement m.visibility).toNoise).thenDo
      (Qubit.dephase (Rate.complement m.recovery).toNoise))).behavior.prob () true =
      (probability m.wignerLaw coherenceProbe : ℝ) := by
  rw [Qubit.twice_dephased, recovery_probability]
  simp [Rate.complement, Recipes.Rate.toNoise]
  ring

/-- No information leakage and perfect recovery reproduce the coherent limit. -/
def ideal : Mechanism :=
  ⟨Rate.of 1, Rate.of 1⟩

/-- Complete leakage removes the recovery signal even with a perfect reversal. -/
def completeLeakage : Mechanism :=
  ⟨Rate.of 0, Rate.of 1⟩

/-- Zero recovery removes the signal even when coherence remains available. -/
def noRecovery : Mechanism :=
  ⟨Rate.of 1, Rate.of 0⟩

example : probability ideal.wignerLaw coherenceProbe = 1 := by
  norm_num [recovery_probability, ideal, Rate.of]

example : probability completeLeakage.wignerLaw coherenceProbe = 1 / 2 := by
  norm_num [recovery_probability, completeLeakage, Rate.of]

example : probability noRecovery.wignerLaw coherenceProbe = 1 / 2 := by
  norm_num [recovery_probability, noRecovery, Rate.of]

end OntologySeparation.PartialLeakage
