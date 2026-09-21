import OntologySeparation.Core.Procedure
import OntologySeparation.Core.Certified
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Real single-qubit Bloch disk: rho = [[(1+z)/2,x/2],[x/2,(1-z)/2]].
These are specified physical channels, not a model of consciousness or collapse. -/
namespace OntologySeparation.Qubit
noncomputable section
structure State where
  x : ℝ
  z : ℝ
  physical : x*x + z*z ≤ 1
structure Noise where
  strength : ℝ
  nonneg : 0 ≤ strength
  le_one : strength ≤ 1
def plus : State := ⟨1, 0, by norm_num⟩
def zero : State := ⟨0, 1, by norm_num⟩
theorem State.x_bounds (s : State) : -1 ≤ s.x ∧ s.x ≤ 1 := by
  have h := s.physical
  constructor <;> nlinarith [sq_nonneg s.z, sq_nonneg (s.x+1), sq_nonneg (s.x-1)]
theorem State.z_bounds (s : State) : -1 ≤ s.z ∧ s.z ≤ 1 := by
  have h := s.physical
  constructor <;> nlinarith [sq_nonneg s.x, sq_nonneg (s.z+1), sq_nonneg (s.z-1)]
theorem density_invariants (s : State) :
    (1+s.z)/2 + (1-s.z)/2 = 1 ∧ 0 ≤ (1+s.z)/2 ∧ 0 ≤ (1-s.z)/2 ∧
    0 ≤ ((1+s.z)/2)*((1-s.z)/2) - (s.x/2)*(s.x/2) := by
  have h := s.physical
  have hz := s.z_bounds
  constructor
  · ring
  constructor
  · linarith [hz.1]
  constructor
  · linarith [hz.2]
  nlinarith
def hadamard : Procedure State State := ⟨fun s => ⟨s.z, s.x, by nlinarith [s.physical]⟩⟩
def phaseFlip : Procedure State State := ⟨fun s => ⟨-s.x, s.z, by nlinarith [s.physical]⟩⟩
def dephase (noise : Noise) : Procedure State State := ⟨fun s =>
  ⟨(1-noise.strength)*s.x, s.z, by
    have h0 : 0 ≤ 1-noise.strength := by linarith [noise.le_one]
    have h1 : 1-noise.strength ≤ 1 := by linarith [noise.nonneg]
    have hsq : (1-noise.strength)*(1-noise.strength) ≤ 1 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (mul_self_nonneg s.x)
    nlinarith [s.physical]⟩⟩
/-- Public X readout: true denotes +. -/
def readX (s : State) : FiniteDistribution Bool where
  mass b := if b then (1+s.x)/2 else (1-s.x)/2
  nonneg b := by cases b <;> simp <;> linarith [s.x_bounds.1, s.x_bounds.2]
  total := by simp; ring
def experiment (p : Procedure State State) : Experiment Unit State State Bool :=
  ⟨fun _ => plus, p, readX⟩
def question : Question := ⟨binaryInterface, fun p => p.prob () true⟩
def prediction (noise : Noise) : Prediction question (experiment (dephase noise)).behavior where
  value := 1-noise.strength/2
  correct := by simp [question, experiment, Experiment.behavior, dephase, plus, readX]; ring
theorem twice_dephased (a b : Noise) :
    (experiment ((dephase a).thenDo (dephase b))).behavior.prob () true =
      (1 + (1-b.strength)*(1-a.strength))/2 := by
  simp [experiment, Experiment.behavior, Procedure.thenDo, dephase, plus, readX]
theorem phase_then_dephase (noise : Noise) :
    (experiment (phaseFlip.thenDo (dephase noise))).behavior.prob () true = noise.strength/2 := by
  simp [experiment, Experiment.behavior, Procedure.thenDo, phaseFlip, dephase, plus, readX]
theorem protected_dephasing (noise : Noise) :
    (experiment ((hadamard.thenDo (dephase noise)).thenDo hadamard)).behavior.prob () true = 1 := by
  norm_num [experiment, Experiment.behavior, Procedure.thenDo, hadamard, dephase, plus, readX]
theorem hadamard_twice (s : State) : (hadamard.thenDo hadamard).evolve s = s := by
  cases s
  rfl
end
end OntologySeparation.Qubit
