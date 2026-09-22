import OntologySeparation.Core.Scenario
import OntologySeparation.Operational.Qubit
import Mathlib.Tactic.NormNum

/-! Explicit recipes with an exact evaluator proved against real-qubit semantics.
Only exposure depends on the model. The prepared state, fixed operations, ordering,
and readout are shared data, not model-dependent callbacks. -/
namespace OntologySeparation.Recipes
/-- A physical rational dephasing strength. -/
structure Rate where
  value : ℚ
  nonneg : 0 ≤ value
  le_one : value ≤ 1
/-- Routine bounds are proved automatically for concrete rational inputs. -/
def Rate.of (value : ℚ) (nonneg : 0 ≤ value := by norm_num)
    (le_one : value ≤ 1 := by norm_num) : Rate := ⟨value, nonneg, le_one⟩
noncomputable def Rate.toNoise (r : Rate) : Qubit.Noise :=
  ⟨(r.value : ℝ), by exact_mod_cast r.nonneg, by exact_mod_cast r.le_one⟩
/-- This backend varies one explicit effective channel law per exposure. -/
structure Law where
  exposure : Rate
/-- Explicit denominator validation avoids Lean's totalized division-by-zero convention. -/
def Rate.fraction (numerator denominator : Nat)
    (positive : 0 < denominator := by decide)
    (bounded : numerator ≤ denominator := by decide) : Rate where
  value := (numerator : ℚ) / (denominator : ℚ)
  nonneg := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  le_one := (div_le_one (by exact_mod_cast positive)).2 (by exact_mod_cast bounded)
def Law.dephasing (numerator denominator : Nat)
    (positive : 0 < denominator := by decide)
    (bounded : numerator ≤ denominator := by decide) : Law :=
  ⟨Rate.fraction numerator denominator positive bounded⟩
inductive Preparation where
  | plus | zero
  deriving DecidableEq
inductive Readout where
  | x | z
  deriving DecidableEq
inductive Operation where
  | expose | hadamard | phaseFlip | dephase (rate : Rate)
/-- The whole experiment is data; it cannot inspect the selected law. -/
structure Recipe where
  prepare : Preparation
  steps : List Operation
  measure : Readout
private def initial : Preparation → ℚ × ℚ
  | .plus => (1, 0)
  | .zero => (0, 1)
private noncomputable def initialReal : Preparation → Qubit.State
  | .plus => Qubit.plus
  | .zero => Qubit.zero
private def step (m : Law) : Operation → (ℚ × ℚ) → ℚ × ℚ
  | .expose, (x,z) => ((1-m.exposure.value)*x,z)
  | .hadamard, (x,z) => (z,x)
  | .phaseFlip, (x,z) => (-x,z)
  | .dephase r, (x,z) => ((1-r.value)*x,z)
private noncomputable def stepReal (m : Law) : Operation → Qubit.State → Qubit.State
  | .expose => (Qubit.dephase m.exposure.toNoise).evolve
  | .hadamard => Qubit.hadamard.evolve
  | .phaseFlip => Qubit.phaseFlip.evolve
  | .dephase r => (Qubit.dephase r.toNoise).evolve
private def run (m : Law) : List Operation → (ℚ × ℚ) → ℚ × ℚ
  | [], s => s
  | op :: rest, s => run m rest (step m op s)
private noncomputable def runReal (m : Law) : List Operation → Qubit.State → Qubit.State
  | [], s => s
  | op :: rest, s => runReal m rest (stepReal m op s)
private theorem step_sound (m : Law) (op : Operation) (s : Qubit.State) (q : ℚ × ℚ)
    (hx : s.x = (q.1 : ℝ)) (hz : s.z = (q.2 : ℝ)) :
    (stepReal m op s).x = ((step m op q).1 : ℝ) ∧
    (stepReal m op s).z = ((step m op q).2 : ℝ) := by
  cases op <;> simp [stepReal, step, Qubit.dephase, Qubit.hadamard,
    Qubit.phaseFlip, Rate.toNoise, hx, hz]
private theorem run_sound (m : Law) (ops : List Operation) (s : Qubit.State) (q : ℚ × ℚ)
    (hx : s.x = (q.1 : ℝ)) (hz : s.z = (q.2 : ℝ)) :
    (runReal m ops s).x = ((run m ops q).1 : ℝ) ∧
    (runReal m ops s).z = ((run m ops q).2 : ℝ) := by
  induction ops generalizing s q with
  | nil => exact ⟨hx, hz⟩
  | cons op rest ih =>
    have h := step_sound m op s q hx hz
    exact ih (stepReal m op s) (step m op q) h.1 h.2
/-- Every recipe denotes a normalized experiment in the existing physical backend. -/
noncomputable def interpret (m : Law) (r : Recipe) : Behavior binaryInterface :=
  (Experiment.mk (fun _ : Unit => initialReal r.prepare)
    (Procedure.mk (runReal m r.steps))
    (fun s => Qubit.readX (match r.measure with
      | .x => s | .z => Qubit.hadamard.evolve s))).behavior
/-- Exact P(+) for the explicitly selected X or Z readout. -/
def probability (m : Law) (r : Recipe) : ℚ :=
  let state := run m r.steps (initial r.prepare)
  (1 + (match r.measure with | .x => state.1 | .z => state.2))/2
/-- Universal correctness: all laws and operation lists, not just the example cells. -/
theorem probability_correct (m : Law) (r : Recipe) :
    (interpret m r).prob () true = (probability m r : ℝ) := by
  have hi : (initialReal r.prepare).x = ((initial r.prepare).1 : ℝ) ∧
      (initialReal r.prepare).z = ((initial r.prepare).2 : ℝ) := by
    cases r.prepare <;> norm_num [initialReal, initial, Qubit.plus, Qubit.zero]
  have h := run_sound m r.steps (initialReal r.prepare) (initial r.prepare) hi.1 hi.2
  cases hm : r.measure <;>
    simp [interpret, probability, Experiment.behavior, Qubit.readX,
      Qubit.hadamard, hm, h.1, h.2]
noncomputable def scenario : Scenario Law Recipe := ⟨Qubit.question, interpret⟩
/-- Users receive the proof family automatically; no handwritten predicted table. -/
def predictions : Scenario.ExactPredictions scenario := ⟨probability, probability_correct⟩
theorem probability_bounds (m : Law) (r : Recipe) :
    0 ≤ probability m r ∧ probability m r ≤ 1 := by
  have h0 := (interpret m r).nonneg () true
  have h1 := (interpret m r).prob_le_one () true
  rw [probability_correct] at h0 h1
  constructor
  · exact_mod_cast h0
  · exact_mod_cast h1
def Law.label (m : Law) : String := s!"Exposure dephasing p={m.exposure.value}"
def Preparation.label : Preparation → String
  | .plus => "prepare |+>"
  | .zero => "prepare |0>"
def Operation.label : Operation → String
  | .expose => "exposure"
  | .hadamard => "H"
  | .phaseFlip => "phase flip (Z)"
  | .dephase r => s!"fixed dephasing p={r.value}"
def Readout.label : Readout → String
  | .x => "P(X=+)"
  | .z => "P(Z=+)"
def Recipe.label (r : Recipe) : String :=
  String.intercalate "; " ([r.prepare.label] ++ r.steps.map Operation.label ++ [r.measure.label])
/-- Physical descriptions are generated, never independently entered labels. -/
def compare (title : String) (laws : List Law) (recipes : List Recipe)
    (hm : laws ≠ [] := by simp) (hp : recipes ≠ [] := by simp) :
    Scenario.Comparison scenario where
  title := title
  description := "Exact probability of the + outcome for the stated preparation, ordered operations and readout. Only exposure uses the row's law: (x,z) maps to ((1-p)x,z). Fixed operations do not vary between rows. These are effective real-qubit channel models, not classifications of entire quantum interpretations."
  models := laws.map fun m => (m.label, m)
  protocols := recipes.map fun r => (r.label, r)
  models_nonempty := by simpa using hm
  protocols_nonempty := by simpa using hp
  predictions := predictions
/-- A calibration probe that is insensitive to exposure dephasing:
prepare |0>, expose once, then read Z. -/
def calibrationProbe : Recipe :=
  { prepare := .zero, steps := [.expose], measure := .z }

/-- A coherence probe whose X signal decreases with exposure dephasing:
prepare |+>, expose once, then read X. -/
def coherenceProbe : Recipe :=
  { prepare := .plus, steps := [.expose], measure := .x }

theorem calibration_probability (m : Law) :
    probability m calibrationProbe = 1 := by
  simp [probability, run, step, initial, calibrationProbe]

theorem coherence_probability (m : Law) :
    probability m coherenceProbe = 1 - m.exposure.value / 2 := by
  simp [probability, run, step, initial, coherenceProbe]
  ring

/-- Optional exact assertion tactic; ordinary studies need no user-written proof. -/
macro "recipe_check" : tactic =>
  `(tactic| norm_num [probability, run, step, initial, Law.dephasing, Rate.fraction, Rate.of])
end OntologySeparation.Recipes
