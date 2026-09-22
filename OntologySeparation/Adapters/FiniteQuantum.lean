import OntologySeparation.Core.ExperimentAccess
import QIT.Core.POVMProbability

/-! General finite complex quantum semantics, directly using the pinned Lean-QIT
state/channel/POVM definitions. No replacement positivity axioms or numerical solver. -/
namespace OntologySeparation.FiniteQuantum
noncomputable section

variable {A B C O S : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype O] [DecidableEq O]

/-- A terminal experiment: a physical evolution followed by a complete readout.
The index types may be products of arbitrarily many finite named registers. -/
structure Test (A B O : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype O] where
  evolution : QIT.Channel A B
  readout : QIT.POVM O B

def Test.prob (t : Test A B O) (ρ : QIT.State A) (o : O) : ℝ :=
  (t.readout.prob (t.evolution.applyState ρ) o : ℝ)

theorem Test.normalized (t : Test A B O) (ρ : QIT.State A) : ∑ o, t.prob ρ o = 1 := by
  unfold Test.prob
  exact_mod_cast t.readout.sum_prob (t.evolution.applyState ρ)

def behavior (ρ : QIT.State A) (tests : S → Test A B O) :
    Behavior { Setting := S, Outcome := O } where
  prob s o := (tests s).prob ρ o
  nonneg s o := (tests s).readout.prob ( (tests s).evolution.applyState ρ) o |>.property
  normalized s := (tests s).normalized ρ

/-- Prefix a test by another physical channel; type checking enforces register sizes. -/
def Test.prepend (t : Test B C O) (channel : QIT.Channel A B) : Test A C O :=
  ⟨t.evolution.comp channel, t.readout⟩

theorem Test.prepend_prob (t : Test B C O) (channel : QIT.Channel A B)
    (ρ : QIT.State A) (o : O) :
    (t.prepend channel).prob ρ o = t.prob (channel.applyState ρ) o := by
  simp only [Test.prob, Test.prepend, QIT.Channel.applyState_comp]

/-- A named constructor for one explicit physical evolution followed by one
complete POVM readout. This is the supported one-step intervention shape; it is
still exactly the existing Test semantics rather than a parallel model. -/
def oneStep (evolution : QIT.Channel A B) (readout : QIT.POVM O B) : Test A B O :=
  ⟨evolution, readout⟩

@[simp] theorem oneStep_prob (evolution : QIT.Channel A B) (readout : QIT.POVM O B)
    (ρ : QIT.State A) (o : O) :
    (oneStep evolution readout).prob ρ o =
      (readout.prob (evolution.applyState ρ) o : ℝ) := rfl

/-- Direct measurement is a test with identity evolution. -/
def measure (readout : QIT.POVM O A) : Test A A O :=
  oneStep (QIT.Channel.idChannel A) readout

/-- An isometry followed by a POVM can be represented exactly by pulling the
POVM back along the isometry. The isometry proof is part of the constructor. -/
def measureAfterIsometry (readout : QIT.POVM O B) (V : Matrix B A ℂ)
    (isometry : Matrix.conjTranspose V * V = 1) : Test A A O :=
  measure (readout.compressByIsometry V isometry)

@[simp] theorem measureAfterIsometry_prob (readout : QIT.POVM O B)
    (V : Matrix B A ℂ) (isometry : Matrix.conjTranspose V * V = 1)
    (ρ : QIT.State A) (o : O) :
    (measureAfterIsometry readout V isometry).prob ρ o =
      ((readout.compressByIsometry V isometry).prob ρ o : ℝ) := by
  change ((readout.compressByIsometry V isometry).prob
    ((QIT.Channel.idChannel A).applyState ρ) o : ℝ) =
      ((readout.compressByIsometry V isometry).prob ρ o : ℝ)
  rw [QIT.State.idChannel_applyState]

/-- The helper has the intended physical semantics: it gives exactly the Born
probability obtained by first lifting the state through the isometry and then
measuring the original POVM. -/
theorem measureAfterIsometry_prob_eq_lift (readout : QIT.POVM O B)
    (V : Matrix B A ℂ) (isometry : Matrix.conjTranspose V * V = 1)
    (ρ : QIT.State A) (o : O) :
    (measureAfterIsometry readout V isometry).prob ρ o =
      (readout.prob (QIT.POVM.isometryLiftState ρ V isometry) o : ℝ) := by
  rw [measureAfterIsometry_prob]
  exact QIT.POVM.compressByIsometry_prob_eq readout ρ V isometry o

@[simp] theorem measure_prob (readout : QIT.POVM O A) (ρ : QIT.State A) (o : O) :
    (measure readout).prob ρ o = (readout.prob ρ o : ℝ) := by
  change (readout.prob ((QIT.Channel.idChannel A).applyState ρ) o : ℝ) =
    (readout.prob ρ o : ℝ)
  rw [QIT.State.idChannel_applyState]

/-- Measuring a classical outcome register again in its coordinate basis reads
back the original POVM probability. -/
theorem coordinate_after_measure (readout : QIT.POVM O A) (ρ : QIT.State A) (o : O) :
    ((QIT.POVM.coordinate O).prob
      ((QIT.Channel.measure readout).applyState ρ) o : ℝ) =
      (readout.prob ρ o : ℝ) := by
  rw [QIT.POVM.prob_eq_trace_re, QIT.POVM.prob_eq_trace_re]
  have hdiag := congrArg (fun X => X o o)
    (QIT.Channel.measure_map_state_diagonal readout ρ)
  change Complex.re ((((QIT.Channel.measure readout).applyState ρ).matrix *
    Matrix.single o o (1 : ℂ)).trace) =
    Complex.re ((ρ.matrix * readout.effects o).trace)
  rw [Matrix.trace_mul_single]
  simpa [Matrix.diagonal] using congrArg Complex.re hdiag

/-- Every local test agrees if the accessible reduced density matrices agree.
This quantifies over arbitrary local CPTP evolution and arbitrary finite POVMs. -/
theorem local_test_eq (ρ σ : QIT.State (A × B)) (h : ρ.marginalA = σ.marginalA)
    (t : Test A C O) (o : O) : t.prob ρ.marginalA o = t.prob σ.marginalA o := by
  rw [h]

/-- A whole family of local tests cannot recover information absent from its marginal. -/
theorem local_behavior_eq (ρ σ : QIT.State (A × B)) (h : ρ.marginalA = σ.marginalA)
    (tests : S → Test A C O) :
    ObservationallyEquivalent (behavior ρ.marginalA tests) (behavior σ.marginalA tests) :=
  fun s o => local_test_eq ρ σ h (tests s) o
end
end OntologySeparation.FiniteQuantum
