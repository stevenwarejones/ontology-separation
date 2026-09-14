# Contributing

Start with docs/QUICKSTART.md and docs/EXTENDING.md. Use a small, independently
reviewable example to demonstrate any API change.

- Follow mathlib naming and style where practical. Keep physical assumptions
  explicit. Use structures for selectable models, typeclasses for canonical math.
- Prefer existing mathlib/Lean-QIT concepts behind small adapters. Import narrow
  modules; do not introduce measure theory for a finite-table convenience API.
- Add no global physical axioms, unfinished proof terms, unsafe proof shortcuts or
  `native_decide` to verified results. Keep exploratory work outside claimed proofs.
- Prove adapter preservation, distribution normalization and relevant range laws.
- Test at least one meaningful counterexample/unsupported case when adding a new
  interpretation family. Do not prove a claimed bound by assuming that bound.
- A speculative protocol gets explicit missing obligations and an unresolved status.
- Documentation examples must compile in Tests/Documentation.lean. Regenerate
  exported snapshots with scripts/export.py; never hand-edit their predictions.
- Run the commands in scripts/check.sh. Explain physical scope and proof scope
  separately in the change description. Do not claim experimental confirmation
  from a formalized ideal model.

The initial code was AI-assisted and has not received independent expert physics
review. Passing Lean validates formal deductions, not their empirical premises.
