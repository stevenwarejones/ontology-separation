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

## Next milestones

The three foundations above are implemented. The milestones below are planned,
not available commands or claims of a complete automatic comparison procedure.
Keep the [beginner path](../START_HERE.md) stable as these capabilities grow.

### 1. One proof-bearing comparison and its report

Add `UniverseComparison` with constructors carrying either an access-relative
`Equivalent` proof or a `Separator`. Derive the verdict from the constructor;
do not accept a user-entered status string. A certificate wrapper organizes
proved results; it is not an algorithm guaranteed to decide arbitrary models.
The search/report layer must separately represent unknown or unsupported cases.

Acceptance: express both local equivalence and joint separation for RecordAccess
as comparison values, export them through the existing transitive axiom audit,
and render distinct verdict cells in the HTML comparison view. Show the models,
access family, protocol/setting/outcome and positive gap where applicable.
Use an explicit checked numerical identity for an exact rational display of a
real-valued gap; never infer its value from a label. Prove the two certificate
arms cannot coexist for the same models and access family. Keep class membership,
class exclusion and pairwise equivalence/separation visibly distinct.

### 2. Bridge recipes and decide exact finite comparisons

Adapt a supported rational recipe backend to `ExperimentAccess.Predictions`,
proving equality of every exported probability. First demonstrate a read-only
equivalence and a reverse-protocol separator using the same vocabulary as the
quantum example. This operational adapter is a separate task from proving a
full recipe-to-complex-quantum semantics bridge.

A finite protocol set alone does not make arbitrary real probabilities
computationally comparable. Require finite enumerable protocols, settings and
outcomes, decidable access, and a computable exact comparison procedure for the
chosen backend (initially rational). Classical decidability on real numbers is
not an executable search algorithm. Prove the finite checker agrees with the
general real-valued equivalence definition through the adapter.

Acceptance: compute equivalence or a checked separator on a small recipe family;
alter one normalized behavior and obtain a separator automatically. The existing
separator requires a positive *ordered* difference. Search for a positive entry
using normalization, or explicitly track orientation; a first differing entry
can be negative. Test negative-first differences, equality, disallowed protocols
and empty allowed families. No failed or incomplete search may yield equivalence.

### 3. Scaffold the proved workflow

Add a `separation` scaffold and one physical-question-first guide after the
comparison API and exact adapter stabilize. Reuse supported recipes so beginners
can change model parameters and access without writing complex-matrix proofs.

Acceptance: `new-scenario X --backend separation` generates a compiling adopter
study whose audited report shows equivalence under restricted access and an
explicit separator when access expands. Compile and export outside the source
package; an invalid edit must leave the previous checked report intact.

### 4. Choose accessible registers as data

Generalize beyond the hard-coded system/record bipartition using named finite
registers and their Hilbert-space index types. A marginal's type depends on the
chosen register subset; define the reindexing and partial trace with that
dependency explicit. Derive admissible local tests from their actual input
registers rather than trusting a user-entered access label.

Acceptance: choose `{system}` or `{system, record}` as data for the existing
example. Prove restricted equivalence, enlarged-access separation, and access
monotonicity. Check empty/full subsets, register reorderings and rejection of a
joint operation under local access. State which interventions the model covers.

### 5. Propose interventions, then check them

Add an external proposer for a precisely declared finite or parameterized
measurement/isometry family. Emit exact candidate data; the Lean checker must
prove physical validity, access, normalization and the strict probability gap.
Rounding a numerical unitary generally breaks its isometry law: use a provably
physical parameterization or an exact certificate, not a numerical tolerance.

Acceptance: `find-separator <study>` recovers a checked witness for the record
example without the user supplying its matrix. Reject non-isometries,
incomplete POVMs and zero-gap candidates; failure preserves prior output and
reports unknown. Candidate search does not prove equivalence or minimality.
Claim an optimal/minimal intervention only with a bound over the entire stated
search family, matched by a witness.

### Scientific extension gate

Pairwise distinguishability is not a separation of entire interpretations of
quantum mechanics. The present coherent/dephased example establishes the former;
the finite class result excludes exactly the supplied convex hull. Before using
a named ontology as that class, prove its operational models are represented by
the generators (and the converse if claiming exact equality of classes).

The ambitious next scientific result should specify two physical law packages,
prove agreement for all experiments under a stated access restriction, and
derive a separating intervention over a nontrivial parameter range, with a
checked robustness threshold. Preserve the distinction between pairwise
comparison, class exclusion, experimental feasibility and empirical evidence.
This needs new model-specific mathematics, not just a common driver or renderer.

## Deliberate later work beyond these milestones

General quantum instruments with retained outcomes and adaptive control; ergonomic
arbitrary circuit recipes; full semantic bridges from every Bell/LF evaluator;
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

## Implemented entry points

| Question | Entry point | Scope checked |
|---|---|---|
| Do all permitted experiments agree? | `ExperimentAccess.Equivalent` | Every allowed protocol/setting/outcome |
| Does extra access separate models? | `RecordAccess.separator` | An explicit coherent/dephased record experiment |
| Can a class reproduce a whole behavior? | `FiniteModels.Membership` | The supplied finite convex hull |
| Can one measurement exclude a whole class? | `ModelCompatibility.recordClassExclusion` | All mixtures of the two correlated dephased preparations |

The public studies are `examples/RecordAccessStudy.lean` and
`examples/ModelClassStudy.lean`. Both are compiled again in an independent adopter
project by `scripts/check_recipes.py`. The latter changes the weights without
changing the target and checks that publication fails without overwriting output.
