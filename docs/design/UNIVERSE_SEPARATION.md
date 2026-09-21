# From predictions to experimentally separating universes

## Target

Given two specified models and an allowed family of experiments, prove either
that all their observable probabilities agree, or exhibit an allowed experiment
and outcome with different probabilities. For a class of models, distinguish
membership (an explicit witness) from exclusion (a universally valid bound).
Neither a missing witness nor failure to violate one inequality is membership.

## Stack and acceptance criteria

1. **Experiment access and general quantum adapter.** Reuse pinned Lean-QIT
   complex density matrices, CPTP channels and POVMs. Connect them to Behavior.
   Define equivalence relative to allowed protocols, and separation witnesses
   whose protocol is proved allowed and whose probability gap is proved positive.
   Prove restriction monotonicity, impossibility of separation under equivalence,
   and indistinguishability after any local channel/POVM when marginals agree.
2. **Record access.** Exhibit a coherent copied record and its fully dephased
   counterpart as genuine quantum states. Prove equality of their accessible
   marginals and hence agreement for every local quantum test. Supply an explicit
   joint measurement with distinct exact probabilities; export audited claims.
   This is a minimal which-record recovery example, not a new LF inequality.
3. **Finite model classes.** Verify convex-mixture compatibility witnesses and
   separating linear inequalities. Verify every probability in a membership
   witness. Include a counterexample to inferring compatibility from one score.
   Provide a complete adopter example and extend the checked report.

## Interface boundaries

An experiment is supplied independently of a model. An access predicate specifies
which experiments are available. A model supplies normalized outcome behaviors;
there are no global physical axioms. Equivalence quantifies over *all* allowed
experiments and outcomes. Separation names one allowed protocol, setting, outcome
and a strictly positive gap. A restricted family must not be advertised as all
physically possible interventions.

The quantum adapter uses QIT.State / QIT.Channel / QIT.POVM directly. It does not
create a second definition of positive matrices or quantum channels. Named finite
index types (including products) describe registers. Positivity, trace preservation
and POVM completeness are proof obligations, inherited from library constructors.
General complex semantics are noncomputable; exact rational reporting remains a
separate proved layer. The existing efficient Bell/LF recipes remain supported;
this stack does not claim a full migration or equivalence bridge for those backends.

For finite model classes, an external optimizer may *propose* weights or a linear
functional. Lean checks nonnegative normalized weights and every output entry,
or verifies the functional on every generator and the strict separating gap.
Completeness applies only to the specified convex hull, not an arbitrary ontology.
We do not claim a complete automated solver in this stack.

## User experience

The first guide starts with a physical question: which registers can be accessed?
Users run a shipped example and inspect checked claims before defining new states.
Common setup is provided by constructors; custom physics still needs a proof.
Reports derive statements from proof-bearing Claim values. Unsupported capability,
unknown compatibility, and observational equivalence are different states.

## Deliberate later work

General quantum instruments with retained outcomes and adaptive control; ergonomic
arbitrary circuit recipes; bridges from existing Bell/LF efficient evaluators;
parameterized leakage and imperfect recovery; concrete collapse dynamics;
quantitative locality/independence relaxations; complete LF-polytope enumeration;
finite-sample statistics with detection and selection assumptions; automatic search
for a minimal intervention. No conscious-observer or experimental-discovery claim.

## Verification

Every PR compiles its new modules and tests, adds transitive axiom audit roots,
and includes negative tests for the new proof boundary. Public examples compile
and export using the same audited exporter as existing reports. The final stack
runs the repository gate and checks regenerated artifacts are stable. Only
propext, Classical.choice and Quot.sound are permitted by the audit.
