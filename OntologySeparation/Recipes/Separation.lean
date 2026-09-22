import OntologySeparation.Recipes.Qubit
import OntologySeparation.Core.Comparison
import OntologySeparation.Core.FiniteComparison

/-! Operational adapter from the exact single-qubit recipe backend into the
common access-relative comparison vocabulary. This uses the backend's existing
proved real-qubit semantics; it does not claim correspondence for other backends. -/
namespace OntologySeparation.RecipeSeparation

open ExperimentAccess
open Comparison
open Recipes

abbrev predict : Predictions Law Recipe binaryInterface := interpret

/-- Exact probability for either Boolean outcome. The existing recipe evaluator
computes P(+); normalization supplies the complementary outcome. -/
def outcomeProbability (m : Law) (r : Recipe) (o : Bool) : ℚ :=
  if o then probability m r else 1 - probability m r

theorem outcomeProbability_correct (m : Law) (r : Recipe) (o : Bool) :
    (predict m r).prob () o = (outcomeProbability m r o : ℝ) := by
  cases o with
  | false =>
      have hnorm := (interpret m r).normalized ()
      rw [Fintype.sum_bool, probability_correct] at hnorm
      have hcast : ((1 - probability m r : ℚ) : ℝ) = 1 - (probability m r : ℝ) := by
        norm_num
      simp only [predict, outcomeProbability, Bool.false_eq_true, if_false]
      rw [hcast]
      linarith
  | true =>
      simpa [predict, outcomeProbability] using probability_correct m r

/-- Equality of the exact Boolean distribution is enough to obtain the common
behavior-level equivalence used by ExperimentAccess. -/
theorem equivalent_of_outcome_probabilities
    (a b : Law) (r : Recipe)
    (h : ∀ o, outcomeProbability a r o = outcomeProbability b r o) :
    ObservationallyEquivalent (predict a r) (predict b r) := by
  intro s o
  rw [outcomeProbability_correct, outcomeProbability_correct, h o]

def calibrationOnly (r : Recipe) : Prop := r = calibrationProbe

def calibrationAndCoherence (r : Recipe) : Prop :=
  r = calibrationProbe ∨ r = coherenceProbe

/-- Every exposure law gives the same full Boolean distribution on the calibration probe. -/
theorem calibration_equivalent (a b : Law) :
    ObservationallyEquivalent (predict a calibrationProbe) (predict b calibrationProbe) := by
  apply equivalent_of_outcome_probabilities
  intro o
  cases o <;> simp [outcomeProbability, calibration_probability]

theorem restricted_equivalent (a b : Law) :
    Equivalent predict calibrationOnly a b := by
  intro r hr
  subst r
  exact calibration_equivalent a b

/-- If b has strictly more exposure dephasing than a, the coherence probe is a
checked separator. The gap is derived from the actual law parameters. -/
def coherenceSeparator (a b : Law) (h : a.exposure.value < b.exposure.value) :
    Separator predict (fun r => r = coherenceProbe) a b where
  protocol := coherenceProbe
  accessible := rfl
  setting := ()
  outcome := true
  gap := (((b.exposure.value - a.exposure.value) / 2 : ℚ) : ℝ)
  positive := by
    exact_mod_cast (div_pos (sub_pos.mpr h) (by norm_num : (0 : ℚ) < 2))
  difference := by
    rw [probability_correct a coherenceProbe, probability_correct b coherenceProbe]
    rw [coherence_probability, coherence_probability]
    push_cast
    ring

def expandedSeparator (a b : Law) (h : a.exposure.value < b.exposure.value) :
    Separator predict calibrationAndCoherence a b :=
  (coherenceSeparator a b h).enlarge (by
    intro r hr
    exact Or.inr hr)

/-- A proof-bearing exact claim for the coherence-probe + outcome. This is useful
in editable studies because its quantity visibly changes when the law changes. -/
def coherenceClaim (m : Law) : Claim :=
  .exact ((predict m coherenceProbe).prob () true) (probability m coherenceProbe)
    (by simpa [predict] using probability_correct m coherenceProbe)

/-- Finite supported menu for the automatic exact checker. The enum is the
protocol type; its mapping to physical recipes is explicit and total. -/
inductive Probe where
  | calibration
  | coherence
  deriving DecidableEq, Fintype

def Probe.recipe : Probe → Recipe
  | .calibration => calibrationProbe
  | .coherence => coherenceProbe

def finitePredict (m : Law) (p : Probe) : Behavior binaryInterface :=
  predict m p.recipe

def finiteOutcomeProbability (m : Law) (p : Probe) (s : Unit) (o : Bool) : ℚ :=
  outcomeProbability m p.recipe o

def finiteEvaluator : FiniteComparison.ExactEvaluator finitePredict where
  value := finiteOutcomeProbability
  correct := by
    intro m p s o
    exact outcomeProbability_correct m p.recipe o

def allProbes (_ : Probe) : Prop := True

def allProbesNonempty : ∃ p, allProbes p := ⟨.calibration, trivial⟩

def automaticComparison (a b : Law) :
    FiniteComparison.Result finitePredict allProbes a b :=
  FiniteComparison.compare finiteEvaluator allProbes a b

def automaticClaim (a b : Law) : Claim :=
  (automaticComparison a b).claim allProbesNonempty

end OntologySeparation.RecipeSeparation
