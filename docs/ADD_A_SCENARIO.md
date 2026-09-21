# Add experiments and new physical laws

Start with [checked recipes](START_HERE.md) for the supported real-qubit operations.
For a law package outside that backend, open
[Study.lean](../examples/downstream/Study.lean). It uses Bell's finite hidden-state
models and exports both a non-vacuous bound and a mathematical exclusion through
the same claim representation used by the matrix and recipes.

## Worked example: a Bell law package

The example defines `admissible m` by requiring outcome independence, parameter
independence and measurement independence in `OperationalBell.vocabulary`.
The meaning is a conjunction of those actual predicates, not an interpretation name.

```lean
def admissible (m : OperationalBell.Model Unit) : Prop :=
  OperationalBell.screeningOffProfile.Satisfied OperationalBell.vocabulary m

def bellBound : Claim := .realizedBound admissible (fun m => Bell.score m.behavior) 2
  (fun m h => OperationalBell.certified.valid m h)
  ClassicalWorld.constantWorld.operational ClassicalWorld.realizedBound.satisfies
```

Read this as:

1. `admissible` defines exactly which models the result covers. This worked example
   uses `Unit` as its hidden-state space. The library's general Bell theorem permits
   any finite hidden-state space; this example does not silently assert that generality.
2. The score is CHSH on the model's observable behavior.
3. The proposed ceiling is 2. The following proof must establish **that ceiling**
   for every admissible model; changing the number alone cannot produce a new result.
4. `constantWorld.operational` supplies an actual member of this class.
5. `realizedBound.satisfies` proves membership under these exact laws.

`singletExcluded` separately proves that the specified singlet behavior cannot be
produced by the same profile theory. A measured estimator alone cannot discharge
that mathematical exclusion proof or prove a physical interpretation false.

The publishing file contains only:

```lean
import Study
import OntologySeparation.Reporting.Claim
#export_claim MyLaboratory.bellBound
#export_claim MyLaboratory.singletExcluded
```

After [setting up the downstream package](../examples/downstream/README.md), run:

```sh
ontology-separation theorem-report examples/downstream/Publish.lean -o examples/bell-law-study.html
```

The report command selects the source's Lake project and builds its current imports.
Open [the generated example](../examples/bell-law-study.html) locally.

## Choose the evidence your experiment supports

All paths use `Core.Claim` and the same checked exporter and Python renderer:

| Constructor | Required evidence | What appears in reports |
|---|---|---|
| `Claim.exact` | An expression, rational value, equality proof | Exact value from that equality |
| `Claim.bound` | A class, score, rational ceiling, universal inequality | Bound; existence not certified |
| `Claim.realizedBound` | The same bound plus a member and membership proof | Bound + satisfying model |
| `Claim.witness` | A class member, membership proof and exact score | Realized witness with proved value |
| `Claim.exclusion` | A model/behavior and proof it is outside a class | Mathematical exclusion |
| `Claim.theoremResult` | A proposition and its proof | Full theorem, including its assumptions |

`#export_theorem` is a convenience for the last constructor. It uses the same
exporter, not a separate evidence system. `RealizedProfileBound` remains the
specialized convenience type for assumption profiles.

## Exact grids for a new backend

For an experiment needing a new state space, dynamics or measurement:

1. Define model and protocol types, their normalized observable behavior, and score.
2. Define a `Scenario` connecting those interpretations to the experimental question.
3. Supply `Scenario.ExactPredictions`: a rational evaluator and a proof it equals
   that question's score for every model and protocol.
4. Construct a `Scenario.Comparison` and use `#export_scenario`.

Each exported cell becomes `Claim.exact` through `ExactPredictions.claim`. A
handwritten evaluator is acceptable because its correctness is proved against the
interpretation; changing it alone invalidates the proof. Generate parameter labels
from the same model data. Descriptions remain explanatory text, not physical laws.

## Add a bundled catalog entry

Ordinary adopter projects require no catalog edit. For the bundled examples,
`Catalog.Matrix.evaluate` selects a proof-bearing claim for each model/protocol.
`Catalog.checked` takes that claim, assumptions and an applicability scope. It has
**no independent numeric-result or evidence-status argument**. An extension carries
its actual claim; there is no theorem-ID lookup table or hand-maintained resolver.

Mark additional laws explicitly with `.additional`. A concrete witness under those
extra laws does not prove that the original column alone entails the result.
Regenerate with `python3 scripts/export.py`, then run `sh scripts/check.sh`.
The offline JSON is a generated view, not a second source of predictions.
