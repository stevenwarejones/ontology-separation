import OntologySeparation.Adapters.FiniteQuantum

/-! A small general circuit layer for finite systems whose register type is
unchanged between steps. Composition uses Lean-QIT channels directly. -/
namespace OntologySeparation.FiniteCircuit
noncomputable section

variable {A O : Type} [Fintype A] [DecidableEq A] [Fintype O]

/-- A sequential circuit on one finite register space. Each step is a proved
CPTP channel from the same register type back to itself. -/
abbrev Circuit (A : Type) [Fintype A] [DecidableEq A] := List (QIT.Channel A A)

/-- Compile a list of physical steps into one channel. List order is execution
order: the head acts first. -/
def Circuit.channel : Circuit A → QIT.Channel A A
  | [] => QIT.Channel.idChannel A
  | step :: rest => (Circuit.channel rest).comp step

@[simp] theorem Circuit.channel_nil :
    Circuit.channel ([] : Circuit A) = QIT.Channel.idChannel A := rfl

theorem Circuit.apply_nil (ρ : QIT.State A) :
    Circuit.channel ([] : Circuit A) |>.applyState ρ = ρ := by
  exact QIT.State.idChannel_applyState ρ

theorem Circuit.apply_cons (step : QIT.Channel A A) (rest : Circuit A)
    (ρ : QIT.State A) :
    (Circuit.channel (step :: rest)).applyState ρ =
      (Circuit.channel rest).applyState (step.applyState ρ) := by
  exact QIT.Channel.applyState_comp (Circuit.channel rest) step ρ

/-- Attach one final complete POVM to a compiled circuit. -/
def test (circuit : Circuit A) (readout : QIT.POVM O A) :
    FiniteQuantum.Test A A O :=
  FiniteQuantum.oneStep circuit.channel readout

theorem test_prob (circuit : Circuit A) (readout : QIT.POVM O A)
    (ρ : QIT.State A) (o : O) :
    (test circuit readout).prob ρ o =
      (readout.prob (circuit.channel.applyState ρ) o : ℝ) := rfl

theorem test_normalized (circuit : Circuit A) (readout : QIT.POVM O A)
    (ρ : QIT.State A) :
    ∑ o, (test circuit readout).prob ρ o = 1 :=
  (test circuit readout).normalized ρ

end
end OntologySeparation.FiniteCircuit
