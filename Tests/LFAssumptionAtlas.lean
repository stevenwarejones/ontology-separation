import OntologySeparation.Experiments.LFAssumptionAtlas

open OntologySeparation LFAssumptionAtlas FriendRecords

example (p : Behavior LF.interface) : OperationalLF p ↔ LF.theory p :=
  operational_iff_lf p

-- The countermodel satisfies every retained physical law; it is not an empty class.
example : ReadableRecords prOperational ∧ ConditionalLocality prOperational ∧
    IndependentPreparation prOperational ∧ ¬ OutcomeIndependent prOperational :=
  ⟨operational_readable prMixture, operational_local prMixture,
    operational_independent prMixture, pr_not_outcomeIndependent⟩

-- Treating the LF countermodel as outcome independent produces a contradiction.
example (h : OutcomeIndependent prOperational) : False := pr_not_outcomeIndependent h

example : ¬ OperationalLF RealQuantum.lfBehavior := quantum_excludes_operational
