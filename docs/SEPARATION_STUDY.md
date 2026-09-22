# Build an editable separation study

The single-qubit recipe backend can now be used through the same access-relative
comparison vocabulary as the general framework.

Create a checked study:

```sh
ontology-separation new-scenario SeparationStudy --backend separation \
  -o examples/SeparationStudy.lean
ontology-separation theorem-report examples/SeparationStudy.lean \
  -o examples/separation-study.html
```

The starter compares two explicit exposure-dephasing laws with two supported probes.

| Access | Probe | Physical meaning | Result |
|---|---|---|---|
| Restricted | prepare `|0>`, expose, read Z | calibration insensitive to phase damping | full Boolean distributions agree |
| Expanded | also allow prepare `|+>`, expose, read X | coherence signal | positive dephasing is separated |

The restricted conclusion is not inferred from one displayed number.
`RecipeSeparation.restricted_equivalent` proves equality of every Boolean outcome
for every protocol admitted by `calibrationOnly`.

The expanded result uses `RecipeSeparation.expandedSeparator`. Its gap is derived
from the actual exposure parameters; the scaffold does not contain a user-entered
gap label.

## Edit one physical parameter

Change:

```lean
def noisy : Law := Law.dephasing 1 2
```

to:

```lean
def noisy : Law := Law.dephasing 1 4
```

and regenerate the report. The exact coherence-probe probability changes from
`3/4` to `7/8`; the local calibration agreement remains proved.

Changing the noisy law to `Law.dephasing 0 1` makes it identical to the reference
law. The strict-separation proof then fails, and the report command leaves the
previous checked HTML untouched rather than publishing a zero-gap separator.

## Semantics and scope

This adapter is specific to the existing real-qubit recipe backend. The backend
already proves `Recipes.probability_correct` for every supported preparation,
operation sequence, law, and readout. `RecipeSeparation.outcomeProbability_correct`
extends that exact evaluator to both Boolean outcomes using normalization and then
feeds those behaviors into `ExperimentAccess`.

This is both an operational integration and a correspondence result for this
specific backend. It is **not** a proof that the two-qubit or Local Friendliness
fast evaluators equal arbitrary complex-QM semantics, and it is not an automatic
finite comparison algorithm. The next stage handles automatic exact comparison
over an explicitly enumerated finite family.
