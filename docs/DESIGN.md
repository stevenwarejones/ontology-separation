# Ontology Separation: design before implementation

Status: implementation contract, 2026-09-14. No claim of a new physics result.

## Goal and non-goals

A Lean 4 library for expressing experimental interfaces, alternative physical laws,
and observable separations. Bell and Local Friendliness (LF) are mandatory
reference scenarios. The ten earlier research proposals retain their original
identities and critical status. A matrix cell may honestly be unresolved.
Python is an optional client, never the owner of mathematical semantics.
This release does not promise automatic theorem discovery or a universal simulator.

## Decisions

1. Use Lean 4 v4.30.0, mathlib at its matching immutable revision, and a pinned
   Lean-QIT revision. Audit the imported dependency closure. Do not import the
   entire quantum library. Keep upstream probability/state objects behind adapters.
2. Mathematical core: an `Experiment` has setting and public-outcome types;
   `Behavior` is a normalized nonnegative real-valued table. A `Theory` is a
   predicate on behaviors for an experimental interface, not a globally asserted axiom.
   A concrete dynamics model is a separate interpretation yielding a behavior.
3. `Bound` and `Witness` carry proofs. A separation combines a universal bound
   for one theory with membership and a violating value in another. Theory inclusion
   and observational equivalence are reusable propositions. Empty theory classes
   never count as physically realized: exhibit membership separately.
4. Use explicit structures for selectable laws; typeclasses only for canonical
   mathematics (finite types, scalar algebra). Namespace all declarations. Disable
   implicit variables. Import narrowly, document conventions and use stable names.
5. Physical records are system identifiers. Access capabilities and public outcomes
   are separate. The protocol description includes operations and their order;
   capability checking checks the requested intervention, never substitutes a different
   experiment. No-signaling alone is a behavior class, not a circuit interpreter.
6. Evidence has two layers: proof-bearing Lean mathematical results, and a Lean
   scenario catalog describing their applicability. Metadata cannot confer proof.
   Numeric model exploration is explicitly marked. Export JSON from Lean; Python
   renders it without computing authoritative physical conclusions.
7. No project `axiom`, `sorry`, `admit`, `unsafe` or native decision escape in
   proved results. CI builds all examples and audits theorem axiom dependencies.
   Standard mathlib axioms (choice, propext, quotient soundness) are permitted.
8. LF uses the published three-setting, two-outcome scenario and its actual
   extended joint distribution constraints. The genuine LF inequality (Bong et al.
   Eq. 13) is distinguished from Brukner/CHSH. Any finite-vertex representation
   proof is labeled separately from the derivation from the joint-distribution
   assumptions; no unproved equivalence is smuggled into a theorem.
9. Twelve-plus scenarios do not imply twelve-plus new theorems. Preserve the
   difference between experiment specification, conditional theorem, realized model,
   numerical prediction, unsupported operation, and unresolved physical semantics.
10. Parameter families replace a hard-coded universe enum in the mathematical core.
    A finite list of named examples is only the report's registry.

## Module boundaries

- `OntologySeparation/Core`: behaviors, theory predicates, bounds, witnesses, separations.
- `OntologySeparation/Adapters`: translations to/from Lean-QIT with explicit preservation.
- `OntologySeparation/Models`: local, no-signaling, LF constraints, finite quantum models,
  and explicit dephasing dynamics. Interpretation names do not constitute dynamics.
- `OntologySeparation/Experiments`: Bell, genuine LF, memory/control benchmarks.
- `OntologySeparation/Catalog`: all named protocols, requirements, open obligations, matrix.
- `Reporting/Claim.lean` and `Reporting/Catalog.lean`: checked export of claims and the model matrix.
- `python/`: standard-library CLI client and Markdown/HTML rendering.
- `python_tests/`: mathematical examples and report-contract tests, including negative cases.
- `docs/`: sources, assumptions, limitations, contribution instructions.

## Original scenario inventory

B01 Bell CHSH; B02 genuine LF (Bong Eq. 13); B03 Bell-non-LF negative control;
B04 reversible-memory/dephasing calibration.

P01 Relative facts fail to compose: compare accessible views and cross-view joining.
P02 Conservation/public records versus reversibility: leakage and constrained controls.
P03 Hidden causal cost of absolute facts: allowed causal influence versus LF score.
P04 Coherent experimenter choices: setting registers and interference readout.
P05 Observer identity/subsystem boundaries: alternative factorizations and access.
P06 Observations with indefinite causal order: process semantics, not a fixed DAG.
P07 Gravitating records: explicit coherent mediator versus specified classical model.
P08 Computationally limited objectivity: bounded recovery resource classes.
P09 Observer versus reversible machine: physical memory protocol; cognition is open.
P10 Rules of shared reality: compatibility and composition of operational views.

Each P scenario gets concrete systems, interventions, readout, candidate comparison,
and missing proof obligations. Toy realizations are explicitly identified and are
not advertised as solutions to the radical proposal. Prior evaluation: P07/P04
priority; P06/P09 conditional; P10 design target; P01/P05 downgraded; P02/P03
supporting machinery; P08 set aside as a breakthrough claim.

## Acceptance and review

- A fresh pinned Lake build checks all claimed theorems.
- Generic bound/witness separation is connected to actual behavior semantics.
- Bell local bound and postquantum witness are imported with an audited adapter;
  quantum operator bounds and concrete witnesses have accurately delimited scope.
- LF has a real mathematical specification and a genuine-inequality implementation;
  report any remaining bridge proof openly.
- At least fourteen scenario definitions cross at least six theory/model choices.
- Unsupported and unresolved entries contain reasons, never invented probabilities.
- JSON schema includes experiment, model, status, statement, assumptions, theorem
  references and limitations. Python must consume the Lean-produced registry.
- Useful negative tests: unsupported coherent operation, unknown model ID, invalid
  probabilities, fake proof labels, and Bell violation compatible with LF.
- README states what is proved versus only specified, and offers exact commands.

## Sources informing design

Lean structures/axioms: https://lean-lang.org/theorem_proving_in_lean4/
Mathlib style: https://leanprover-community.github.io/contribute/style.html
Lake reproducibility: https://leanprover-community.github.io/mathlib4_docs/
Lean-QIT: https://github.com/QuAIR/Lean-QIT
Bong et al.: https://arxiv.org/abs/1907.05607 (published version v4, Eq. 13)
Quanundrum precedent: https://github.com/jangnur/Quanundrum

## Adoption and adapter budget (user review)

Core uses finite sums over probability tables, not a measure-space interface.
Continuous models may be added separately; no blanket claim is made about mathlib
probability requiring measure theory. Selectable physical theories are explicit
values, not competing typeclass instances. Every adapter must demonstrate entrywise
probability preservation before its bounds can be used through the common interface.
The quickstart must work without reading implementation internals. Contributors get
small executable recipes for a new theory, experiment and report cell. Tests cover
rejected inputs as well as successful predictions. The matrix is a research-status
report as well as a result browser; unresolved cells remain visible.

## Assumption profiles (user requirement)

Expose realism, global truth, locality and measurement independence as four
named predicates selected in an explicit `Vocabulary Model`. Each profile entry
is require / reject / unspecified. Generate all 16 fully specified combinations,
but never imply that all are realizable. Reject means logical negation; unspecified
means no constraint. Measurement independence is the operational statistical
surrogate, not a theorem about free will. Bell local causality and LF parameter
independence need distinct vocabulary definitions. If one selected predicate
implies another, Lean can prove the corresponding conflicting profiles empty.
Profile existence and experiment separation are different obligations. No demo
assigns a speculative physical theory to a profile merely from its name.

## Current reporting architecture

`Core.Claim` connects numerical values, bounds, witnesses and exclusions to their
proofs. `Reporting.Claim` supplies the common exporter used by recipes, standalone
results and the bundled catalog. Data is extracted by kernel reduction; the
reporting pipeline does not natively execute real-valued mathematical models.
See [unified reporting](design/UNIFIED_REPORTING.md).

Memory operations live in `Runtime/Memory.lean`, shared with `Models/Memory.lean`.
The internal rational engine has a public `Memory.Model` wrapper requiring strength
in [0,1]. Catalog memory claims take that checked model. The model list supplies
both parameter labels and interpretation dispatch, avoiding duplicated parameters.

The catalog is a client of the open `Theory`, `Interpreter`, `Scenario`, `Bound`,
`Witness` and `Separation` interfaces. It uses actual claims, not a second theorem
registry. Catalog schema 3 and scenario schema v2 share the claim contract; earlier
schemas are rejected. All HTML views are generated under examples/. Proof scope
and applicability to physical systems remain distinct review obligations.
