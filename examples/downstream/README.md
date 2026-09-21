# A separate adopter project

This Lake package demonstrates both supported recipes and an independent Bell law
package. Neither requires editing the parent catalog or registering theorem names.

From this directory, with the pinned Lean toolchain available:

```sh
lake update
lake build
PYTHONPATH=../../python python3 -m ontology_separation.cli scenario-report RecipeStudy.lean -o ../recipe-comparison.html
PYTHONPATH=../../python python3 -m ontology_separation.cli theorem-report Publish.lean -o ../bell-law-study.html
```

- `RecipeStudy.lean`: choose rates and experimental procedures; predictions and
  proofs come from the general recipe soundness theorem.
- `Study.lean`: define a Bell law package, supply its bound and a satisfying model,
  and prove exclusion of a singlet behavior. This uses the general interface.
- `Publish.lean`: export the Bell claims with the common checked exporter.
- `Checks.lean`: check the public contract and reject a mismatched proof.

See [the recipe walkthrough](../../docs/START_HERE.md) and
[the Bell example line by line](../../docs/ADD_A_SCENARIO.md).

To create another recipe study:

```sh
PYTHONPATH=../../python python3 -m ontology_separation.cli new-scenario MyStudy -o MyStudy.lean
PYTHONPATH=../../python python3 -m ontology_separation.cli scenario-report MyStudy.lean -o ../my-study.html
```

For your own repository, require `ontologySeparation` from its Git URL at an explicit
commit revision instead of the bundled `path = "../.."`, and omit this example's
shared `packagesDir`. Use the same `lean-toolchain`. The first `lake update`/cache
setup downloads dependencies; later report commands rebuild changed imports.
