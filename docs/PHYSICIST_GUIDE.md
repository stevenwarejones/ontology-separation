# From physical assumptions to predictions

Start with [PhysicistWorkflow.lean](../examples/PhysicistWorkflow.lean). It contains
complete experiments whose parameters and operations you can edit. For a separate
project, use [the downstream example](../examples/downstream/README.md).

## Begin with a physical question

Choose the state or hidden-variable space, the available interventions, and what
will be measured publicly. Then choose the equations that represent the assumptions
you want to study. An ontology name alone does not determine those equations.

The library supplies two named operational vocabularies. They give the four existing
profile slots precise meanings, but do not claim those meanings exhaust realism,
locality, global truth, or human free will.

## Bell vocabulary

`OperationalBell.Model Λ` supplies a finite hidden-state space Λ, preparation
P(λ|x,y), and normalized conditional responses P(a,b|x,y,λ). The public table is
P(a,b|x,y) = Σλ P(λ|x,y) P(a,b|x,y,λ). Every setting in the interface is treated as
an available experimental choice. Both settings may affect preparation, and the
conditional responses may signal, until the corresponding laws are imposed.

| Operational law | Meaning | Legacy slot |
|---|---|---|
| Outcome independence | P(a,b\|x,y,λ) = P(a\|x,y,λ) P(b\|x,y,λ) | realism |
| Conditional parameter independence | Alice's conditional marginal does not depend on y; Bob's does not depend on x | locality |
| Independent preparation | P(λ\|x,y) is constant across settings | measurement independence |
| Joint counterfactual assignments | A common finite mixture of predetermined local outputs A(0), A(1), B(0), B(1), using the existing Bell-local class | global truth |

The first three imply **CHSH S ≤ 2**. The proof factors conditional correlators,
applies a bound to means in [-1,1], and averages using the same preparation weights.
It does not define locality as the desired score ceiling. Joint counterfactuals
provide a second route to S ≤ 2, regardless of the other slots. This last predicate
asserts that the public table admits a joint representation; it does not assert that
the supplied model's particular hidden variables instantiate that representation.

Outcome independence is a particular screening-off condition, not a definition of
all philosophical realism. Conditional parameter independence is stronger than
observed no-signaling: averaging may conceal conditional dependence. Measurement
independence is a statistical equation, not a theorem about free will.

There are concrete countermodels: a signaling response reaches S=4 while keeping
screening-off and independent preparation; a setting-dependent preparation reaches
S=4 while keeping screening-off and conditional locality. A singlet response with
independent preparation and conditional locality is proved to fail screening-off.
These examples demonstrate changes in laws without declaring every such model
physically realized in nature.

## Friend-record vocabulary

`FriendRecords.Model Λ` supplies arbitrary conditional tables for three settings per
laboratory, preparation probabilities, and fixed record functions C(λ), D(λ).
Setting zero asks the corresponding friend.

| Operational law | Meaning | Legacy slot |
|---|---|---|
| Readable fixed records | P(a=C(λ)\|x=0,y,λ)=1 and P(b=D(λ)\|x,y=0,λ)=1 | global truth |
| Conditional locality | Conditional local marginals are independent of the distant setting | locality |
| Independent preparation | The distribution over λ does not depend on either setting | measurement independence |
| Outcome independence | Same screening-off equation as in the Bell vocabulary | realism; not required |

The first three yield the genuine **LF score G ≤ 6**. A proved adapter reconstructs
the conditional moment boxes and preserves every public probability before
importing the existing LF bound. The test suite includes a PR inner box with
readable friend records; LF does not require screening-off of the alternative
Wigner outcomes. A quantum friend candidate also explicitly realizes rejection of
record readability while retaining conditional locality and independent preparation.
This is a scoped operational countermodel, not a classification of an interpretation.

“Global truth” here means readable fixed actual records. In the Bell vocabulary,
it refers to all local counterfactual assignments. These predicates differ. Never
transfer a classification merely because it uses the same old slot name. The
finite model is a scoped operational implementation of absolute records, not a
claim about consciousness or an exhaustive formalization of every LF interpretation.
The physical motivation is [Bong et al.](https://arxiv.org/abs/1907.05607v4).

## All sixteen combinations

`require` asserts a predicate, `reject` asserts its negation, and `unspecified`
imposes neither. `ProfileBound.under` carries a proved bound to a stronger profile
only after Lean checks that the necessary laws were retained.

The Bell screening-off rule covers two fully specified profiles. The joint-assignment
rule covers eight, with one overlap: **nine** Bell-vocabulary profiles inherit the
bound. **Two** friend-record profiles inherit the LF bound. The counts and implication
rules are checked in Lean and exported to the operational HTML table.

A bound does not prove a profile inhabited. The other cells are not automatically
possible, excluded, or predictive. Construct a model to show realizability. Negating
locality does not select a unique signaling mechanism. Experimental exclusions
require statistical evidence beyond these mathematical bounds.

## Compose experiments

`Channel` represents finite classical random transitions. `andThen` composes stages,
`parallel` assumes independent composition, and `feedForward` is classical outcome-
dependent control. Constructors supply normalization proofs.

`Procedure` represents maps between physical state types. These can be density
operators or other validated states; they are not assumed to be classical ontic
samples. Compose stages with `thenDo`. `Experiment` supplies preparation and a
normalized public readout. Internal states do not automatically become public records.

The supplied `Qubit` backend is the real Bloch disk x²+z² ≤ 1 with density matrix
[[ (1+z)/2, x/2 ], [ x/2, (1-z)/2 ]]. H, phase flip, and dephasing preserve this
state constraint. Trace, diagonal positivity, and determinant nonnegativity are
proved, and X readout is normalized. This is a restricted single-qubit family,
not a general tensor-product or arbitrary-instrument interpreter.

For two dephasing stages the + probability is [1+(1-p₂)(1-p₁)]/2. A phase flip
followed by dephasing gives p/2. Rotating to a dephasing eigenstate and back gives
+ with certainty for this preparation. These are channel calculations, not new
foundational no-go theorems. Composition saves repeated validity proofs; genuinely
new physics still needs a state-preservation proof or an appropriate new backend.

## Keep a prediction attached to its experiment

`Question` binds a statistic to its interface. `Prediction question behavior`
contains the value and an equality proof for that exact behavior. `PredictionFamily`
adds explicit model and protocol indices. `ProfileBound` contains the actual
vocabulary, profile, predictor, target theory, bridge, and bound. Deliberately wrong
value and experiment assignments are rejected in the tests.

To export your own theorem, no central claim enumeration needs editing:

```lean
import OntologySeparation
import OntologySeparation.Reporting.Export
#export_theorem OntologySeparation.FriendRecords.bound
```

After installing the Python client and building, use:

```sh
ontology-separation theorem-report examples/Publish.lean -o examples/operational-results.html
```

Without installing the client, from the repository:

```sh
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/Publish.lean -o examples/operational-results.html
```

The formal proposition is generated from the theorem's actual Lean type. Definitions,
unfinished proofs, and unsupported proof dependencies cannot be published by this
command. Physical interpretation text is commentary, not an extra inferred theorem.
HTML and JSON remain editable snapshots. Recheck trusted local source with Lean;
this command executes that source and does not authenticate arbitrary third-party
JSON. The legacy 98-cell report still has a weaker, curated presentation contract.

## Setup

```sh
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
lake env lean examples/PhysicistWorkflow.lean
sh scripts/check.sh
```

The full development gate needs Python 3.10+ and Node 18+. The toolchain and dependencies
are pinned; no independent upgrades are needed. First downloads can be substantial.
Open `examples/index.html` for navigation, `operational-results.html` for operational
coverage, and `ruled-out-models.html` for the historical reference classes.

For your own ontology define its model space, predictor, and laws. Reuse a vocabulary
only when its equations match your intended meaning. Supply a `ProfileBridge` or
prove a new bound. Continuous hidden variables, gravitational dynamics, indefinite
causal order, many-observer semantics, and general quantum instruments remain
substantive adapter/research work.

For a complete experiment → models → proofs → table workflow, see
[Add a scenario](ADD_A_SCENARIO.md). The example lives in a separate adopter package.
