# What changes when the environment becomes accessible?

Start with `examples/EnvironmentAccessStudy.lean`. It uses one public import and
exports kernel-checked statements through the usual audited report path.

The question is physical: can any experiment on a laboratory distinguish coherent
record copying from a specified irreversible measurement, when a separate
which-record environment remains inaccessible?

## The preparation and laws

The tensor order is **((system, friend record), environment)**. Prepare
`3/5 |000⟩ + 4/5 |111⟩`. This is not just an asserted normalized matrix:
`preparation_is_copy` proves that it comes from the existing two-register source
by copying the friend record to a clean environment with a checked isometry.

Both laws have exactly this preparation. Under `coherent` it remains coherent.
Under `collapsed` a complete unread coordinate measurement follows preparation.
Its outcome is not an additional accessible register. This is an explicit
irreversible alternative; it is not a claim about all collapse interpretations.

The environment is a modeled qubit, not every unmodeled laboratory degree of
freedom. The friend is a readable qubit record, not a conscious observer.

## Choose access before choosing the measurement

| Access | Permitted operations | Result in this PR |
|---|---|---|
| Laboratory | Any finite CPTP channel on system **and** friend record, then any finite POVM | All outcome probabilities agree |
| Laboratory and environment | Joint operations on all three modeled qubits | The states differ; optimal discrimination follows in the next PR |

`laboratory_state` identifies the reduced state with the existing checked
dephased two-register state. `same_laboratory_state` proves equality of the two
laws' reduced states. `every_laboratory_test` transports this equality through
**every** local test; it does not enumerate a sample of circuits.

`laboratoryClaim` exports that scoped equivalence. The named protocol constructors
require a laboratory-typed test for laboratory access. A joint test cannot be
made local by editing a string. “Laboratory” is a grouped region containing two
specified tensor factors, not a claim that arbitrary register subsets are already
implemented.

## Run it

From a checked-out repository with its documented Lean dependencies installed:

```sh
lake build
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/EnvironmentAccessStudy.lean -o examples/environment-access.html
```

The [HTML report](../examples/environment-access.html) distinguishes whole-family
agreement from global state inequality. State inequality alone supplies neither
a practical recovery circuit nor finite-shot statistical significance.

## How this fits the ambitious program

1. **This PR:** make the physical comparison and inaccessible information precise.
2. **Next:** connect accessible states to the existing Lean-QIT Helstrom theorem,
   proving an attained optimum over all binary measurements, with a checked
   laboratory impossibility result. Add an explicit implementable witness.
3. **Then:** connect a chosen witness and explicit calibration/trial assumptions
   to a verified prospective finite-shot rejection rule.

These are known discrimination/decoherence baselines that the framework must
get right before attempting restricted-control optimization or new foundations
claims. Helstrom discrimination is covered in Watrous, *The Theory of Quantum
Information*, section 3.1: https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf.
No novelty or experimental rejection is asserted here.

## Infrastructure reuse review

Use pinned Lean-QIT `PureVector`, `State`, `Channel.measure`, `POVM.coordinate`,
`POVM.isometryLiftState`, and existing reduced states. Reuse the merged
`FiniteQuantum.Named` adapter and `Claim` reporting. The only new matrix is the
physical record-copy isometry and its finite proof; no replacement tensor,
channel, positivity, or measurement framework is introduced.
