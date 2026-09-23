# From predictions to experimentally separating universes

## Current role

This document originally tracked the build-out of the general access/separation
framework. That foundation is now implemented. The current priority is to use it
for stronger physical theorems rather than continue expanding abstraction for its
own sake.

The core contract remains:

- an experiment is supplied independently of a model;
- an access predicate states which experiments are allowed;
- equivalence quantifies over every allowed protocol/setting/outcome;
- separation carries an explicit allowed witness and a proved positive gap;
- finite-class membership and universal class exclusion are distinct from
  pairwise equivalence/separation;
- restricted protocol families are never advertised as all physically possible
  interventions.

## Implemented foundation

| Question | Checked entry point / result | Scope |
|---|---|---|
| Do all permitted experiments agree? | `ExperimentAccess.Equivalent` | every allowed protocol, setting and outcome |
| Does extra access separate two models? | `RecordAccess.separator` and later record-access modules | explicit coherent/dephased finite-dimensional quantum examples |
| Can accessible registers be represented explicitly? | named register/access modules | stated finite register decompositions and permitted footprints |
| Can a finite class reproduce a behavior? | `FiniteModels.Membership` | supplied finite convex hull |
| Can a measurement exclude an entire finite class? | model-compatibility exclusion theorems | every mixture in the stated hull |
| Can exact finite candidates be searched and checked? | separator-search/report pipeline | declared finite candidate families only |
| Can recipes connect to checked semantics? | recipe correctness theorems and adopter tests | supported recipe backends |
| Can record access be studied in explicit QIT models? | perfect-record, two-copy and friendship-monogamy modules | finite-dimensional models stated in those files |

Reports carry proof-bearing claims and the axiom audit checks their transitive
logical dependencies. Exact rational recipe evaluators and general QIT semantics
remain separate interfaces where appropriate.

## The scientific frontier after PR #73

The framework should now serve four concrete theorem programs.

### 1. Forced-signaling model-class completeness

The current LC4 forced-signaling result is exact inside
`HiddenInfluence.Model`, a finite deterministic response-table representation.
The next access/model-class task is not a new UI. It is to prove that this
representation is equivalent, for the relevant observables and signaling metric,
to a general finite stochastic conditional-local hidden-variable model.

Acceptance:

- define the stochastic finite model with explicit normalization;
- determinize/refine it without changing ABD/ACD marginals;
- preserve the recipient total-variation signaling quantity;
- embed deterministic response tables back into the stochastic model;
- state the resulting behavior-class equivalence publicly;
- add audit roots and tests for the assumptions required by the construction.

### 2. Completion-independent forced-signaling sharpness

The current theorem uses one fixed operational completion. Make completion choice
explicit and prove the sharp coefficient over the entire declared completion
family.

Acceptance:

- completion type derived from the operational semantics;
- universal checked bound over every completion;
- kernel-checked finite certificate or analytic proof of the completion optimum;
- matching witness establishing coefficient sharpness;
- documentation updated to remove the fixed-completion caveat only if proved.

### 3. Imperfect record accessibility

The perfect-copy results establish exact decoherence and access obstruction but do
not characterize imperfect records. Extend the QIT record model continuously.

Acceptance:

- explicit normalized state/channel family for imperfect records;
- observer access policies defined from actual register footprints;
- operational discrimination quantity, preferably trace distance/fidelity or
  optimal binary-test probability;
- universal tradeoff over the stated parameter domain;
- attaining construction and recovery of the perfect-copy boundary case;
- prior-art comparison before any novelty language.

### 4. Active post-LF intervention

Passive nested records have already been proved to collapse to ordinary LF. Any
new nested-friend study must add an incompatible active operation: read, coherent
reversal, interference, or a comparably explicit intervention.

Acceptance:

- operational semantics retain the new intervention rather than hiding it in a
  label;
- structured adversaries are tested before witness optimization;
- a reduction to Bell/contextuality is recorded as a boundary result if found;
- any surviving constraint has a concrete quantum target and precisely stated
  model class.

## Deferred software milestones

The following remain useful engineering ideas but are not currently the research
bottleneck:

- a generic sum type wrapping equivalent/separated/unknown comparison outcomes;
- a broader exact finite-comparison adapter;
- more scaffolding for generated separation studies;
- external intervention proposal/search;
- arbitrary adaptive quantum instruments and retained outcomes.

Build these when a physical theorem needs them. Do not introduce them simply to
make the architecture look complete.

## Scientific extension gate

Pairwise distinguishability is not separation of entire interpretations of
quantum mechanics. A finite convex hull is not automatically an ontology. A
finite search is not an impossibility theorem. A witness score below a threshold
does not establish class membership.

Before attaching a named physical interpretation to a checked class, prove that
its operational models map into the represented class; prove the converse as well
if exact equality is claimed.

A strong new result should specify two physical law packages or model classes,
state the allowed controls, quantify over the relevant nuisance parameters, and
derive either an access-relative equivalence, a sharp separation, or an
impossibility theorem. Experimental feasibility and empirical evidence remain
separate obligations.

## Verification

Every theorem-bearing PR must compile its new modules and tests, add transitive
axiom-audit roots, and update the guide that states its physical scope. The full
repository gate is `sh scripts/check.sh`.

Only the project's existing logical axiom whitelist is permitted. External
optimizers and scripts may propose finite witnesses or certificates, but Lean must
check the mathematical statement used by the theorem.

See [the research program](../research/PROGRAM.md) for the ordered post-#73
sequence.
