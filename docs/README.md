# Documentation index

Begin with [Getting started](START_HERE.md). The advanced separation guides are
optional research material, not prerequisites for running the recipes.

## Beginner

| Guide | Purpose |
|---|---|
| [Getting started](START_HERE.md) | Browse without installation, then change one parameter |
| [Quickstart](QUICKSTART.md) | Install and recheck proofs |
| [Physicist guide](PHYSICIST_GUIDE.md) | Connect physical questions to the framework |
| [Glossary](GLOSSARY.md) | Understand the vocabulary |
| [Scenarios](SCENARIOS.md) | Interpret the reference experiments and their scope |
| [Matrix](MATRIX.md) | Read the model comparison table |
| [Ruled-out models](RULED_OUT_MODELS.md) | Distinguish mathematical exclusion from empirical evidence |
| [Verification](VERIFICATION.md) | Understand what the checks establish |
| [Online examples](PAGES.md) | Browse or deploy verified snapshots |

## Recipes and extension

Lean adopters can start from `import OntologySeparation.Study` for supported studies.
Framework authors can use `import OntologySeparation.Extension` when the required
physics is outside the supported component set. These are import façades, not new
backends or alternate semantics.


| Guide | Purpose |
|---|---|
| [Recipe guide](RECIPE_GUIDE.md) | Understand the editable one-qubit example |
| [Separation study](SEPARATION_STUDY.md) | Edit a scoped agreement/separation study using checked qubit recipes |
| [Two-qubit guide](TWO_QUBIT_GUIDE.md) | Build a Bell–CHSH experiment |
| [LF protocol guide](LF_PROTOCOL_GUIDE.md) | Model explicit friend records and read-or-reverse choices |
| [Add a scenario](ADD_A_SCENARIO.md) | Introduce a law package and export checked results |
| [Extension guide](EXTENDING.md) | Write new Lean theories, experiments and adapters |

## Advanced — separation research

These APIs describe all permitted experiments or an explicitly supplied model
class. The quantum adapter uses general complex states, channels and POVMs.
The fast rational recipes share normalized behaviors and audited reporting with
this layer, but there is no checked recipe-to-quantum equivalence bridge yet.

| Guide | Purpose |
|---|---|
| [Experiment access](EXPERIMENT_ACCESS.md) | Prove equivalence over an access family or supply a separator |
| [Named register access](NAMED_REGISTER_ACCESS.md) | Derive allowed protocols from checked physical register footprints |
| [Typed named quantum registers](NAMED_QUANTUM_REGISTERS.md) | Bind named access to typed local and joint quantum tests |
| [Scoped comparison results](COMPARISON_RESULTS.md) | Package agreement or separation without losing model/access scope |
| [Record access](RECORD_ACCESS_GUIDE.md) | Follow a complete local-equivalence/joint-separation proof |
| [Model classes](MODEL_CLASS_GUIDE.md) | Certify whole-table membership or exclusion from a finite convex hull |
| [Exact finite comparison](EXACT_FINITE_COMPARISON.md) | Connect exact rational evaluators to scoped automatic comparison |
| [Structured comparison reports](STRUCTURED_COMPARISON_REPORTS.md) | Read checked models, covered experiments, separator probabilities and exact gap |

## Design and implementation reference

These documents explain architecture and planned work. A roadmap entry is not an
implemented capability; use each guide's stated scope and checked examples.

| Document | Topic |
|---|---|
| [Architecture](DESIGN.md) | Core abstractions and design decisions |
| [Operational onboarding](OPERATIONAL_ONBOARDING_DESIGN.md) | Physical-law and adopter workflow design |
| [Matrix completion](MATRIX_COMPLETION.md) | Implemented evidence semantics and migration |
| [Matrix completion design](MATRIX_COMPLETION_DESIGN.md) | Matrix extension plan |
| [Checked recipes](design/CHECKED_RECIPES.md) | Recipe verification contract |
| [Two-qubit recipes](design/TWO_QUBIT_RECIPES.md) | Quantum recipe boundaries |
| [LF protocol](design/LF_PROTOCOL.md) | Record simulation and proof boundaries |
| [Scenario workflow](design/SCENARIO_WORKFLOW.md) | Adopter scenario contract |
| [Unified reporting](design/UNIFIED_REPORTING.md) | Common evidence contract |
| [Universe separation](design/UNIVERSE_SEPARATION.md) | Implemented foundations and next milestones |

- [One-step finite quantum tests](ONE_STEP_FINITE_TESTS.md) — explicit channel/isometry plus POVM experiments using the existing Lean-QIT semantics.

- [Finite channel circuits](FINITE_CIRCUITS.md) — sequential CPTP steps followed by a complete POVM.

- [Automatic covered finite families](AUTOMATIC_COVERED_GRIDS.md) — derive complete discrete grids from nonempty protocol lists; continuous thresholds remain symbolic theorems.

- [Partial leakage and recovery](PARTIAL_LEAKAGE_RECOVERY.md) — mechanistic visibility/recovery model and exact recovery probabilities.

- [Partial leakage robustness](PARTIAL_LEAKAGE_ROBUSTNESS.md) — symbolic two-parameter separation region, distinct from finite scans.

- [End-to-end partial leakage study](PARTIAL_LEAKAGE_STUDY.md) — pointwise exact comparison plus a separately scoped symbolic robustness theorem.

- [Exact separator search](SEPARATOR_SEARCH.md) — certify base agreement, then search an explicit finite candidate family for an oriented separator.
