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
boolean profile alone cannot supply a physical realization. Seven advanced
protocols remain unresolved; their cells do not carry verified-result labels.

## Reports

The report references named Lean declarations and includes the hypotheses and
limitations for each scenario. Its prose is a presentation of those declarations,
not another formal language. The Python client validates the schema and catches
missing/duplicate cells, unknown selections and malformed evidence references.
It cannot authenticate the proofs behind arbitrary imported JSON. Rebuild trusted
source with Lean when mathematical assurance is required.
