# Scenario-to-comparison design

The adopter should define one operational question, interpret the same procedures
under explicit model laws, prove the predictions, and obtain a comparison without
editing the library's catalog. The existing theorem wrapper alone did not provide
that path.

## Contract

`Scenario M P` binds a `Question` and an interpretation `M → P → Behavior`.
`Scenario.ExactPredictions s` holds rational values with equality proofs for every
model/procedure pair. `Scenario.Comparison s` selects named model and procedure
lists and carries those predictions. Every displayed value comes from that same
record. The exporter checks its type and audits its transitive proof dependencies
before computing JSON. Fractions are serialized as integer strings, never floats.

`#export_scenario` complements `#export_theorem`; it accepts a proved comparison,
not a theorem name substituted for a numeric table. The Python command invokes Lean
before writing HTML, validates the rectangular grid, escapes labels, and retains an
existing report if checking or parsing fails. A failed cell proof prevents exporting
the whole grid. There is no silent fallback to the old curated matrix.

## Deliberate limits

- The scenario fixes the public interface. Its interpretation is explicit physics
  supplied by the adopter, not inferred from model labels.
- Table labels and prose are commentary. HTML is an editable snapshot; rechecking
  trusted Lean source remains the authority.
- Exact rational tables are the initial reporting scope. Arbitrary real values,
  inequalities, unsupported protocols, and symbolic families retain the existing
  `Prediction`, `Bound`, `Interpreter`, and theorem-report APIs. This exporter does
  not approximate them into rational values.
- The worked example varies effective coherence laws inside the real-qubit backend.
  It does not distinguish all interpretations of quantum theory, formalize a
  conscious observer, or claim a new foundational no-go theorem.
- Table equality means equality of the chosen statistic. Statistical discrimination
  of finite experimental data requires a separate analysis.

## Adoption test

The complete example lives in an independent Lake package under
`examples/downstream`, including the model laws, procedures, proof family, grid,
and export commands. Adding it does not require editing the bundled catalog. Each cell exports through `Core.Claim`.
Negative tests check wrong predictions/procedures and rejection of invented or
unfinished proofs. Python tests check dimensions, exact arithmetic, escaping,
CLI routing, and preservation of previous output on failure.
