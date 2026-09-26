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

`sh scripts/check.sh` defaults to one Lean thread to bound memory use, matching
CI. On a machine with sufficient memory, opt into more threads locally:

```sh
LEAN_NUM_THREADS=8 sh scripts/check.sh
```

CI restores pinned dependency and incremental project builds, then runs all
builds, tests, axiom audits and snapshot checks before saving caches. PR and
`main` push verification do not run the additional kernel replay audit.

A nightly run of Verify performs all the usual verification plus serial replay
of every built project and test module, including cached declarations. It runs
on the default branch at 07:17 UTC (03:17 New York in summer, 02:17 in winter),
once this workflow is merged. GitHub may delay scheduled runs. The workflow's
manual **Run workflow** trigger also runs the full audit; select `main` to audit
the current default branch. Neither scheduled nor manual runs deploy Pages.

Run the full replay locally after `sh scripts/check.sh`:

```sh
LEAN_NUM_THREADS=1 lake env leanchecker --verbose OntologySeparation Tests
```

This uses Lean 4.30's bundled checker with each module's imported environment.
Third-party dependency declarations are not independently replayed; this is an
additional check using Lean's own kernel, not an external verifier. The normal
build checks newly compiled proofs, while restored compiled artifacts are
trusted until the nightly replay. That cache trust already existed before this
CI change. Nightly replay adds detection after merge, not a pre-merge guarantee;
any nightly failure needs investigation. Replay failures fail the nightly/manual
run and prevent its cache saves. Wait for all required checks on the latest PR
commit before merging.

The initial code was AI-assisted and has not received independent expert physics
review. Passing Lean validates formal deductions, not their empirical premises.
