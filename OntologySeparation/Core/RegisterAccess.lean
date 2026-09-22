import Mathlib.Data.Fintype.Basic

/-! Theory-independent named-register access policies.

A protocol's register footprint is derived from its protocol data by a supplied
footprint function. Access is then the checked subset relation between that
derived footprint and the registers granted by the policy. Human-readable labels
do not participate in the proof. -/
namespace OntologySeparation.RegisterAccess

variable {R P : Type} [DecidableEq R]

/-- Derive the physical registers touched by a protocol. Concrete experiment
modules provide this function by pattern matching on their protocol data. -/
structure Footprint (R P : Type) [DecidableEq R] where
  registers : P → Finset R

/-- Registers granted to an experimenter. -/
structure Policy (R : Type) [DecidableEq R] where
  available : Finset R

def Allowed (footprint : Footprint R P) (policy : Policy R) (protocol : P) : Prop :=
  footprint.registers protocol ⊆ policy.available

theorem allowed_mono (footprint : Footprint R P) {narrow wide : Policy R}
    (h : narrow.available ⊆ wide.available) {protocol : P}
    (allowed : Allowed footprint narrow protocol) :
    Allowed footprint wide protocol :=
  fun r hr => h (allowed hr)

def emptyPolicy : Policy R := ⟨∅⟩

def fullPolicy [Fintype R] : Policy R := ⟨Finset.univ⟩

@[simp] theorem allowed_full [Fintype R] (footprint : Footprint R P) (protocol : P) :
    Allowed footprint (fullPolicy : Policy R) protocol := by
  intro r hr
  simp [fullPolicy]

@[simp] theorem allowed_empty_iff (footprint : Footprint R P) (protocol : P) :
    Allowed footprint (emptyPolicy : Policy R) protocol ↔
      footprint.registers protocol = ∅ := by
  simp [Allowed, emptyPolicy]

/-- A protocol touching a register not granted by the policy is rejected. -/
theorem not_allowed_of_missing (footprint : Footprint R P) (policy : Policy R)
    (protocol : P) {register : R}
    (touches : register ∈ footprint.registers protocol)
    (missing : register ∉ policy.available) :
    ¬ Allowed footprint policy protocol := by
  intro h
  exact missing (h touches)

end OntologySeparation.RegisterAccess
