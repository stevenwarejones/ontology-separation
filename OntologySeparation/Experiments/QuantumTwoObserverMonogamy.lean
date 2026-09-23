import OntologySeparation.Experiments.QuantumAccessMonogamy
import OntologySeparation.Core.RegisterAccess

/-! Two-observer access monogamy for the explicit RecordEnvironment quantum state.

A protocol is physically typed as laboratory-only, environment-only, or joint.
Its register footprint is derived from that constructor.  Because coherent and
collapsed laws have identical marginals on each factor, every separating
protocol in this class must be joint.  Therefore two observers with disjoint
register policies cannot both possess an allowed separator.

The local-indistinguishability theorems imported from QuantumAccessMonogamy are
stronger than the fixed-codomain protocol type used here: they quantify over
arbitrary finite local CPTP output spaces and POVMs. -/

namespace OntologySeparation.QuantumTwoObserverMonogamy
noncomputable section

open RecordEnvironment

inductive Protocol where
  | laboratory (test :
      FiniteQuantum.Test RecordEnvironment.Laboratory
        RecordEnvironment.Laboratory Bool)
  | environment (test : FiniteQuantum.Test Bool Bool Bool)
  | joint (test :
      FiniteQuantum.Test RecordEnvironment.Registers
        RecordEnvironment.Registers Bool)

def footprint : RegisterAccess.Footprint RecordEnvironment.Region Protocol where
  registers
    | .laboratory _ => {.laboratory}
    | .environment _ => {.environment}
    | .joint _ => {.laboratory, .environment}

def probability (ρ : QIT.State RecordEnvironment.Registers) :
    Protocol → ℝ
  | .laboratory t => t.prob ρ.marginalA true
  | .environment t => t.prob ρ.marginalB true
  | .joint t => t.prob ρ true

def Separates (p : Protocol) : Prop :=
  probability RecordEnvironment.coherent p ≠
    probability RecordEnvironment.collapsed p

theorem laboratory_not_separating
    (t : FiniteQuantum.Test RecordEnvironment.Laboratory
      RecordEnvironment.Laboratory Bool) :
    ¬ Separates (.laboratory t) := by
  intro h
  apply h
  exact QuantumAccessMonogamy.every_laboratory_test t true

theorem environment_not_separating
    (t : FiniteQuantum.Test Bool Bool Bool) :
    ¬ Separates (.environment t) := by
  intro h
  apply h
  exact QuantumAccessMonogamy.every_environment_test t true

/-- Any actual separator in the typed protocol class must touch both registers. -/
theorem separator_requires_joint (p : Protocol) (h : Separates p) :
    footprint.registers p = {.laboratory, .environment} := by
  cases p with
  | laboratory t => exact False.elim (laboratory_not_separating t h)
  | environment t => exact False.elim (environment_not_separating t h)
  | joint t => rfl

def CanSeparate (policy : RegisterAccess.Policy RecordEnvironment.Region) : Prop :=
  ∃ p : Protocol, RegisterAccess.Allowed footprint policy p ∧ Separates p

theorem canSeparate_requires_laboratory
    (policy : RegisterAccess.Policy RecordEnvironment.Region)
    (h : CanSeparate policy) :
    RecordEnvironment.Region.laboratory ∈ policy.available := by
  obtain ⟨p, hp, hs⟩ := h
  have hj := separator_requires_joint p hs
  have hm : RecordEnvironment.Region.laboratory ∈ footprint.registers p := by
    rw [hj]
    simp
  exact hp hm

theorem canSeparate_requires_environment
    (policy : RegisterAccess.Policy RecordEnvironment.Region)
    (h : CanSeparate policy) :
    RecordEnvironment.Region.environment ∈ policy.available := by
  obtain ⟨p, hp, hs⟩ := h
  have hj := separator_requires_joint p hs
  have hm : RecordEnvironment.Region.environment ∈ footprint.registers p := by
    rw [hj]
    simp
  exact hp hm

/-- Access monogamy: disjoint register grants cannot both contain an allowed
protocol that distinguishes the coherent and collapsed quantum laws. -/
theorem disjoint_policies_cannot_both_separate
    (alice bob : RegisterAccess.Policy RecordEnvironment.Region)
    (hdisjoint : Disjoint alice.available bob.available) :
    ¬ (CanSeparate alice ∧ CanSeparate bob) := by
  rintro ⟨ha, hb⟩
  have hla := canSeparate_requires_laboratory alice ha
  have hlb := canSeparate_requires_laboratory bob hb
  exact Finset.disjoint_left.mp hdisjoint hla hlb

/-- Full joint access really does attain the distinction, so the obstruction is
about disjoint access rather than nonexistence of a quantum separator. -/
def fullPolicy : RegisterAccess.Policy RecordEnvironment.Region :=
  ⟨{.laboratory, .environment}⟩

theorem full_policy_can_separate : CanSeparate fullPolicy := by
  refine ⟨.joint RecordEnvironment.returnTest, ?_, ?_⟩
  · intro r hr
    simpa [footprint, fullPolicy] using hr
  · unfold Separates probability
    intro h
    have hg := QuantumAccessMonogamy.joint_return_gap
    rw [h] at hg
    norm_num at hg

end
end OntologySeparation.QuantumTwoObserverMonogamy
