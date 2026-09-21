# Ontology Separation

**Compare physical assumptions through Lean-verified experimental predictions.**

Ontology Separation is a Lean 4 library with a small Python result browser. Define a
physical theory, describe an experiment, and prove which predictions distinguish
it from another theory. Physical assumptions remain explicit; Lean's logic and
proof checker stay fixed.

## Make your first checked comparison

1. [Open the worked recipe table](examples/recipe-comparison.html) locally.
2. Follow [the short setup guide](docs/START_HERE.md).
3. Generate a study, edit its laws or procedures, and export it:

```sh
ontology-separation new-scenario MyStudy -o examples/MyStudy.lean
ontology-separation scenario-report examples/MyStudy.lean -o examples/my-study.html
```

For supported qubit recipes, the framework derives **both predictions and their
proofs**. Labels come from the actual parameters and operations. Reports rebuild
edited dependencies before checking, and fail without publishing if a proof fails.
See [the glossary](docs/GLOSSARY.md) for terminology, or the
[advanced interface](docs/ADD_A_SCENARIO.md) for new physical mechanisms.

## Scope of the reference catalog

This is an initial research framework. It includes **14 scenario descriptions**
and a **7-model comparison matrix**. Bell and genuine Local Friendliness have
formal reference examples. All later scenarios now have checked restricted subproblems or conditional extensions.
The matrix has 24 native results and 74 results requiring explicitly added laws;
it is not 98 unconditional predictions from seven complete physical universes.
It does not claim ten new beyond-LF discoveries or a simulator for arbitrary physics.

## Browse without installing

Open [examples/index.html](examples/index.html) locally after cloning or downloading.
It links the full matrix, fourteen per-experiment ontology views (all sixteen
profiles and every two-axis slice), and a sourced experimental evidence ledger.
GitHub displays HTML source; download it to use the interactive controls.

Conditional cells explicitly state their added laws. Ontology coloring is a
conditional preview until a vocabulary-to-theorem `ProfileBridge` is proved.
Published measurements are separated from calculated witnesses.

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
from mathematical exclusions. The legacy matrix remains a curated snapshot.

For a complete experiment → models → proofs → table workflow, see
[Add a scenario](docs/ADD_A_SCENARIO.md). The example lives in a separate adopter package.
