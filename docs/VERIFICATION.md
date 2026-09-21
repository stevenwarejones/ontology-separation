# Verification scope

Run `sh scripts/check.sh` in a checkout with the pinned Lean toolchain available.
The check builds the library and executable, checks mathematical and documentation
examples, audits transitive theorem axioms, regenerates the snapshot from Lean,
and tests the Python client and report contracts.

## Trusted mathematical boundary

- Definitions and proofs are Lean source with pinned dependency revisions.
- Core finite behaviors require nonnegativity and normalization proofs.
- The report's verified claims contain actual Lean proofs, not only name strings.
- No project proof uses unfinished terms, new physical axioms or native decision
  shortcuts. The audit accepts only the usual mathlib logical axioms: propext,
  Classical.choice and Quot.sound.
- The axiom report is written to AXIOM_AUDIT.txt. Build output alone is not the
  complete audit: assumptions and declaration statements must still be reviewed.
- Numerical exploration may suggest rational witnesses, but only the exact
  witness and its proved score enter verified results.

## Limits

The real-singlet adapter is a restricted quantum model. Its probability is a
squared singlet amplitude from normalized local measurement bases. General quantum
channels, all POVMs and arbitrary dimensions are not exposed through this adapter.
The Lean-QIT adapter currently imports its Bell behavior/local/NS results; it does
not yet identify the real-singlet implementation with QIT's `IsQuantum` predicate.
Both constructions are explicit, and that optional interoperability bridge is
not assumed by a reported theorem.

The LF implementation uses finite mixtures of conditional NS boxes with actual
friend outputs and a setting-independent prior. Its normalized probabilities,
conditional local marginals and friend-readout identities are proved. This is the
operational mathematical formulation being bounded; there is no proof that a
laboratory device satisfies those physical assumptions. The explicit singlet
witness is an ideal protocol, not a reanalysis of published experimental data.

The memory interpreter implements a small two-qubit circuit language. Its three
registered circuit families have exact proved probability formulas and appropriate
physical parameter restrictions. It is not a general quantum circuit verifier;
arbitrary program preservation theorems are an extension task. It does not model
consciousness, gravity, thermodynamic costs or indefinite causal order.

No general solver determines all assumption-profile consistency questions. A
boolean profile alone cannot supply a physical realization. The seven formerly empty advanced protocols have checked restricted subproblems.
Their `verifiedConditional` cells require additional laws and do not settle the
broader physical ambitions. All sixteen-profile UI mappings remain conditional
until a physical vocabulary bridge is proved; checkbox selection is not proof.

## Reports

The report references named Lean declarations and includes the hypotheses and
limitations for each scenario. Its prose is a presentation of those declarations,
not another formal language. The Python client validates the schema and catches
missing/duplicate cells, unknown selections and malformed evidence references.
It cannot authenticate the proofs behind arbitrary imported JSON. Rebuild trusted
source with Lean when mathematical assurance is required.


## Schema 2 and conditional evidence

Schema version 2 adds `extensions` with required laws, contrast and scope, and
`verifiedConditional` for theorems that need laws beyond the model column.
`requiresExtension` remains available for future unsupported cases. Schema 1
snapshots are intentionally rejected instead of silently relabeling old gaps.
Every ClaimId is resolved to a proof; the resolver's transitive axioms are audited.
A registered name does not formally check arbitrary English prose: theorem statements
and premises are the authoritative claims. The generated HTML is a presentation.

Published Hensen/Bong records are sourced literature summaries, not imported raw
data. No statistical confidence analysis is verified in Lean here. The generic
`Bound.excluded_by_lower` requires a valid lower bound on the true expectation;
passing an observed estimator alone would not discharge that premise.

The Python runner fails if it discovers zero tests. Tests verify case-fold-safe
paths so Mac extraction cannot collapse Lean and Python test directories again.

## Checked recipes and adoption safeguards

`Recipes.probability_correct` connects the exact rational evaluator to normalized
real-qubit experiment semantics for every law and operation list. The evaluator's
outputs are not treated as proofs in their own right. Tests exercise operation
order, both preparations/readouts, repeated exposure, and fixed channels independent
of the selected law. `probability_bounds` follows from the normalized behavior.

`scripts/check_recipes.py` builds an independent adopter package, generates a study
with the public scaffolder, and checks all twelve starter cells. It changes an
imported law without a manual rebuild to verify fresh predictions and labels, then
makes that law invalid to test rejection despite a pre-existing compiled module.
It also rejects eleven malformed laws, recipes and proof exports. Python tests
cover atomic writes, source protection, nested project selection and CLI isolation
from the legacy snapshot. These checks run in the normal CI gate.

The report commands build current imports using `lake lean`, with implicit parameter
insertion disabled for the checked source. Imported modules retain their own Lean
options. Neither this option nor the axiom audit establishes that the author's
physical definitions are appropriate. Generated labels prevent parameter drift in
the recipe API; free-form descriptions in the advanced API remain reviewable prose.

The manual `Tests/Audit.lean` file identifies selected roots and audits their
transitive dependencies. It is not a census of all project or adopter declarations.
Each `#export_scenario` and `#export_theorem` separately audits its dependencies,
including user-defined results not on that list. Editing raw JSON or emitting
lookalike text does not produce an authenticated proof: reports assume trusted
local source and tooling. Review definitions and recheck the source.
