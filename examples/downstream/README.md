# Your own laboratory project

## Easiest entry point

After the package setup below, `RecipeStudy.lean` imports the one-file recipe API.
From this directory, run:

```sh
PYTHONPATH=../../python python3 -m ontology_separation.cli scenario-report RecipeStudy.lean -o ../recipe-comparison.html
```

This builds current imports automatically. To create another complete study:

```sh
PYTHONPATH=../../python python3 -m ontology_separation.cli new-scenario MyStudy -o MyStudy.lean
PYTHONPATH=../../python python3 -m ontology_separation.cli scenario-report MyStudy.lean -o ../my-study.html
```

See [the walkthrough](../../docs/START_HERE.md). The `Coherence`/`Compare` example
below shows the advanced interface for implementing physics beyond this backend.


This independent Lake package imports only the qubit backend and adds a parameterized model, an operational coherence
law, a composed experiment, and predictions without editing the upstream registry.
From this directory, run `lake update`, `lake build`, then `lake env lean Publish.lean`.
After installing the Python client, run:

```sh
python3 -m ontology_separation.proof_report Publish.lean -o results.html
```

The local path dependency and shared `packagesDir` are for this checkout. The
example has its own manifest and build; it reuses the parent's pinned dependency
downloads. In a separate repository remove `packagesDir` and replace
`path` with `git = "https://github.com/stevenwarejones/ontology-separation.git"` and
`rev = "<full commit containing this API>"`. Retain the pinned toolchain and manifest.
`FullyCoherent` is a channel law; equating it with a foundational ontology predicate
requires an additional definition and proof.

## Complete scenario comparison

`Coherence.lean` adds three explicit coherence laws, four procedures, the shared
observable, and all twelve exact predictions. `Compare.lean` publishes the table
and its supporting theorem statements. Run after `lake build`:

```sh
PYTHONPATH=../../python python3 -m ontology_separation.scenario_report Compare.lean -o ../scenario-comparison.html
```

For an installed client use `ontology-separation scenario-report` with the same
arguments. See [the walkthrough](../../docs/ADD_A_SCENARIO.md). The comparison
requires no edit to the upstream registry.
