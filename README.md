# Ontology Separation

**Compare physical assumptions through Lean-verified experimental predictions.**

Ontology Separation is a Lean 4 library with a small Python result browser. Define a
physical theory, describe an experiment, and prove which predictions distinguish
it from another theory. Physical assumptions remain explicit; Lean's logic and
proof checker stay fixed.

## Choose your path

### Getting started

| I want to… | Start here | Installation |
|---|---|---|
| Browse results | [Online explorer](https://stevenwarejones.github.io/ontology-separation/) · [offline views](examples/index.html) | None |
| Change a parameter | [Getting started](docs/START_HERE.md) | Python; Lean to check new predictions |
| Build a Bell–CHSH experiment | [Two-qubit guide](docs/TWO_QUBIT_GUIDE.md) | Python + Lean |

The online explorer publishes verified snapshots from `main`; each page links to
its source revision. [Deployment details](docs/PAGES.md).

**[Local Friendliness protocol guide](docs/LF_PROTOCOL_GUIDE.md)** — explicit friend
records, read-or-reverse choices, and checked LF/profile conclusions.

### Advanced — the separation framework (research)

| I want to… | Start here | Installation |
|---|---|---|
| Compare every permitted experiment | [Experiment access](docs/EXPERIMENT_ACCESS.md) | Lean |
| Separate the laboratory from its environment | [Three-register guide](docs/ENVIRONMENT_ACCESS_GUIDE.md) · [report](examples/environment-access.html) | Lean |
| Find what extra access separates two models | [Record access](docs/RECORD_ACCESS_GUIDE.md) | Lean |
| Prove whole-table membership or class exclusion | [Model classes](docs/MODEL_CLASS_GUIDE.md) | Lean |
| Define new physical laws or a backend | [General scenario interface](docs/ADD_A_SCENARIO.md) · [Extension guide](docs/EXTENDING.md) | Lean |

The recipes use fast exact rational evaluators; the general complex-quantum
semantics are noncomputable. They share normalized behaviors and audited reporting,
but there is no checked recipe-to-quantum equivalence bridge yet.
[Documentation index](docs/README.md) · [Separation roadmap](docs/design/UNIVERSE_SEPARATION.md#next-milestones).

## Explore the HTML views

| View | What you can explore |
|---|---|
| [Recipe comparison](examples/recipe-comparison.html) | Three dephasing laws × four procedures; the simplest worked example. |
| [Two-qubit Bell recipes](examples/two-qubit-comparison.html) | Four noise laws × direct singlet, gate-built singlet, and product preparation. |
| [LF read-or-reverse protocol](examples/local-friendliness-protocol.html) | Four record-noise laws × entangled and product preparations. |
| [Full experiment matrix](examples/matrix.html) | All 14 scenarios across seven model classes, with proof-derived results. |
| [Bell assumptions](examples/B01.html) | All sixteen assumption combinations and two-axis comparisons. |
| [Local Friendliness assumptions](examples/B02.html) | The same ontology views for the LF experiment. |
| [Experimental evidence](examples/evidence.html) | Published measurements, their assumptions, and what they challenge. |

[All HTML examples](examples/index.html) · [Bell law package and exclusion](examples/bell-law-study.html)

GitHub displays HTML as source. Clone or download the repository, then open these
files in your browser; the views work offline without installing Lean or Python.

## Scope of the reference catalog

This is an initial research framework. It includes **14 scenario descriptions**
and a **7-model comparison matrix**. Bell and genuine Local Friendliness have
formal reference examples. All later scenarios now have checked restricted subproblems or conditional extensions.
The matrix has 24 native results and 74 results requiring explicitly added laws;
it is not 98 unconditional predictions from seven complete physical universes.
It does not claim ten new beyond-LF discoveries or a simulator for arbitrary physics.

## Browse the bundled catalog

```sh
python -m pip install -e .
ontology-separation compare B01 B02
ontology-separation compare B04 P02 --models unitary_memory dephased_memory partial_memory
ontology-separation html matrix.html
```

These commands browse a bundled Lean-generated snapshot. To check proofs locally,
install [Lean](https://lean-lang.org/install/) and run:

```sh
lake exe cache get
sh scripts/check.sh
```

The pinned toolchain is Lean 4.30.0. The first build downloads mathlib dependencies;
subsequent builds reuse them. [Quickstart](docs/QUICKSTART.md) has the full setup.

## Ordinary Lean underneath

```lean
import OntologySeparation
open OntologySeparation

example : ¬ LF.theory RealQuantum.lfBehavior :=
  LF.quantumSeparation.excludes

example (m : Memory.Model) :
    Memory.probability m Memory.echo = 1 - m.strength / 2 :=
  Memory.echo_probability m
```

The core has normalized finite probability tables, theory predicates, observables,
proof-bearing bounds and realized witnesses. A `Separation` combines a universal
bound with a violating model. Existing Lean-QIT Bell results enter through an
entrywise probability-preserving adapter. Quantum singlet examples use a small,
explicit real-projective Born-rule model.

## What the examples establish

- **Bell:** a local-class bound of two, an explicit quantum singlet violation,
  and a no-signaling PR witness with score four.
- **Genuine LF:** Bong et al.'s Eq. (13) bound of six for finite conditional
  no-signaling friend models, plus an exact singlet witness above six.
- **Bell versus LF:** a conditional PR box violates CHSH on non-friend settings
  while remaining allowed by the LF model.
- **Memory experiments:** exact matrix calculations for echo, inaccessible leakage
  and phase control at arbitrary specified dephasing strength.
- **Assumption profiles:** all sixteen binary combinations of four selected laws
  can be expressed. Their realizability is a separate proof obligation.

The ten original research proposals retain their names and limitations. The seven previously empty directions now include gluing, contamination, access,
order-interference, pure-state entanglement, classical-query and agreement proofs.
These are restricted subproblems, not solutions to their broader research ambitions. [Scenario guide](docs/SCENARIOS.md)
explains the distinction.

## Read and extend

- [Matrix completion and evidence semantics](docs/MATRIX_COMPLETION.md)
- [Architecture and decisions](docs/DESIGN.md)
- [Add a theory, experiment or adapter](docs/EXTENDING.md)
- [Comparison matrix](docs/MATRIX.md) and [expandable HTML](docs/matrix.html)
- [Contributing and proof policy](CONTRIBUTING.md)
- [Verification scope](docs/VERIFICATION.md)

Realism, global truth, locality and measurement independence are predicates chosen
by the model author. **Reject** means logical negation; **unspecified** adds no
condition. We do not equate statistical measurement independence with human free will.

A checked theorem establishes the stated mathematical implication. Experimental
interpretation and physical premises remain reviewable assumptions. Loading JSON
is not proof verification, and evidence labels cannot replace a Lean proof.

## Attribution

Based on [Lean 4](https://lean-lang.org/), [mathlib](https://github.com/leanprover-community/mathlib4),
and selected [Lean-QIT](https://github.com/QuAIR/Lean-QIT) modules. The LF reference is
[Bong et al., Nature Physics 16 (2020)](https://arxiv.org/abs/1907.05607v4).
[Quanundrum](https://github.com/jangnur/Quanundrum) is relevant prior software for
quantum-agent thought experiments; this project does not claim that comparison of
physical theories is a new idea.

No package-registry name has been reserved. Apache-2.0 license.

## Operational onboarding

Start with [the physicist guide](docs/PHYSICIST_GUIDE.md),
[editable experiments](examples/PhysicistWorkflow.lean), or
[the independent Lake package](examples/downstream/README.md). Explicit Bell and
friend-record laws now connect to checked bounds. Composable classical channels
and restricted qubit procedures reuse normalization proofs.
[Operational results](examples/operational-results.html) display actual theorem
types; [ruled-out models](examples/ruled-out-models.html) separate empirical evidence
from mathematical exclusions. The matrix, recipes and theorem reports share the same proof-bearing claim format.
Values and evidence categories are derived from the claims; offline snapshots are generated views.

For a complete experiment → models → proofs → table workflow, see
[Add a scenario](docs/ADD_A_SCENARIO.md). The example lives in a separate adopter package.

For the research layer, use the advanced paths above or the
[documentation index](docs/README.md).

[Research milestones](docs/research/PROGRAM.md) · [Checked LF assumption correspondence](docs/research/LF_ASSUMPTIONS.md)

For the LF paper-to-code correspondence, see [the LF joint-event walkthrough](docs/research/LF_PAPER_GUIDE.md) and its [checked HTML report](examples/lf-paper.html).

Explore imperfect friend readout with [the sharp error-budget study](docs/research/LF_READOUT_GUIDE.md) and its [checked HTML report](examples/lf-readout.html).
