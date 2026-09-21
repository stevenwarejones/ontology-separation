# Add a new physical mechanism with the advanced interface

**For the supported qubit operations, start with [checked recipes](START_HERE.md).**
That route generates labels and proves predictions automatically. Use this guide
when you need a new law, operation, state space, or measurement outside that backend.
`Scenario.Comparison.ofLists` can construct comparisons without manual nonempty-list
proofs; you still supply the new interpreter and its prediction theorem.


Start with [the rendered comparison](../examples/scenario-comparison.html), then
open [Coherence.lean](../examples/downstream/Coherence.lean). This is the complete
source, in its own Lake package. You can copy it without editing the upstream catalog.

## The physical question

Prepare |+>, apply a procedure, and measure X. What is the probability of +?
Each model specifies the law of an exposure: `(x,z) ↦ ((1-p)x,z)` in the real Bloch
disk. The alternatives are p=0, p=1/2, and p=1. Their labels mean precisely those
channel laws, not entire philosophical ontologies.

| Physical model | One exposure | Phase flip, exposure | H, exposure, H | Two exposures |
|---|---:|---:|---:|---:|
| Preserved coherence, p=0 | 1 | 0 | 1 | 1 |
| Partial dephasing, p=1/2 | 3/4 | 1/4 | 1 | 5/8 |
| Complete dephasing, p=1 | 1/2 | 1/2 | 1 | 1/2 |

The first procedure separates these predictions. The protected procedure maps the
prepared state into a dephasing eigenstate and back, so this statistic is identical
for all three laws. Two exposures compose the specified channel twice. These are
exact calculated probabilities; an individual trial is still random where the
probability lies strictly between zero and one.

## Run it

From the repository, after installing the pinned Lean toolchain:

```sh
lake exe cache get
lake build
cd examples/downstream
lake update
lake build
PYTHONPATH=../../python python3 -m ontology_separation.scenario_report Compare.lean -o ../scenario-comparison.html
```

Open `examples/scenario-comparison.html` from the repository root. If the Python
client is installed, the last command can instead be:

```sh
ontology-separation scenario-report Compare.lean -o ../scenario-comparison.html
```

The command checks the source with Lean before writing the table. `Compare.lean`
contains the entire publishing step:

```lean
import Coherence
import OntologySeparation.Reporting.Scenario
#export_scenario CoherenceStudy.comparison
#export_theorem CoherenceStudy.predictions_correct
#export_theorem CoherenceStudy.direct_separates
#export_theorem CoherenceStudy.protected_equal
```

## What you edit

1. **Model laws.** `Model` lists alternatives; `strength` specifies the exposure
   parameter for each. `noise` proves each parameter is physically admissible.
2. **Procedures.** `Protocol` lists the four procedures; `procedure` composes actual
   physical operations. Every branch uses the same preparation and X readout.
3. **Question and interpretation.** `scenario` connects each model/procedure pair
   to a normalized public behavior, and selects the + probability as the statistic.
4. **Predictions.** `predicted` proposes rational values. `predictions_correct`
   proves they follow from the physical interpretation, reusing the channel lemmas.
5. **Presentation.** `comparison` selects models and procedures and supplies their
   labels. Its `predictions` field contains the values together with their proof.

As a first exercise, change the partial-dephasing strength from `1/2` to `1/4` in
`strength`. The same proof script handles this admissible rational parameter, and
the table becomes `7/8, 1/8, 1, 25/32` for that model. Update its display label too:
Lean verifies equations, not the meaning of English labels. A value outside [0,1]
fails the physicality obligations. Changing a proposed probability without changing
its physics fails `predictions_correct`.

To add a fifth procedure, extend `Protocol`, `procedure`, `predicted`, the proof,
and the displayed protocol list. Lean reports missing cases and unsatisfied proof
obligations. You do not add a central claim ID, edit the exporter, or hand-fill HTML.

## Your own repository

Copy the downstream package, remove its shared `packagesDir` setting, and replace
the local `path = "../.."` dependency with a Git dependency pinned to a commit that
contains this API. Keep the matching `lean-toolchain`. See
[the package README](../examples/downstream/README.md).

A new kind of physics can use its own model and state types. Reuse this workflow
when each selected procedure has an explicit interpretation and a rational exact
prediction. General real-valued results and bounds use the existing theorem-report
API. New physical operations still need validity proofs; the framework supplies
composition and reporting, not the missing physical law.
