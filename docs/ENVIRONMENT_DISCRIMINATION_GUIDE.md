# How well can any allowed experiment distinguish the laws?

Open `examples/EnvironmentDiscriminationStudy.lean`, or its
[checked report](../examples/environment-discrimination.html). The same
[three-register preparation and laws](ENVIRONMENT_ACCESS_GUIDE.md) are used.

## Choose the objective first

Here the task is to identify which of **two equally likely, fixed states** was
prepared from **one copy**. A binary measurement returns `true` for coherent and
`false` for collapsed. Decision error averages the two possible wrong answers.
This is not a null-model p-value or a probability that an ontology is true.

For accessible states ρ and σ, the proved optimum is

`minimumError ρ σ = (1 - D(ρ,σ)) / 2`,

where D is Lean-QIT's normalized trace distance. The lower bound covers every
finite CPTP preprocessing channel followed by every binary POVM.
`optimalTest ρ σ` attains it, using the upstream Helstrom spectral projector.
Thus the optimization is over an entire class, not a finite circuit search.
The theorem is a mathematical optimum, not certification of hardware capable of
implementing an arbitrary spectral measurement. The current theorem leaves the full-state
trace distance symbolic; it does not report a numerically evaluated optimum.

| Access | Best decision error | Scope |
|---|---|---|
| System and friend record, no environment | Exactly 1/2 | Every finite laboratory channel and binary readout |
| All three modeled registers | Attained `(1-D)/2`, strictly below 1/2 | Every finite full-register channel and binary readout |

The second row follows from global state inequality and positive trace distance.
It does not claim that an arbitrary recovery circuit attains the optimum.

## A specified measurement for an experimental protocol

`returnReadout` has two effects: the projector onto the prepared pure state,
and its complement. This is equivalently a return-to-source test: invert a
preparation and read whether the initial state has been recovered. Both outcomes
are retained. It is a complete measurement, not postselection on recovery.

| Law | Probability of `true` |
|---|---|
| Coherent copying | 1 |
| Specified irreversible measurement | 337/625 |

The exact signed gap is 288/625. `returnSeparator` checks full-register access
and the model order. The theorem proves the POVM probabilities; a physical gate
compilation and instrument calibration are separate requirements. This specific
measurement is **not claimed optimal**. It is used in the [finite-shot protocol](FINITE_SHOT_GUIDE.md) because its null probability and ideal power are explicit.

## Use the general interface

```lean
-- rho and sigma are your already-defined accessible QIT states.
-- t is any finite CPTP channel followed by a binary readout.
#check OntologySeparation.QuantumDiscrimination.every_test
#check OntologySeparation.QuantumDiscrimination.optimalTest
#check OntologySeparation.QuantumDiscrimination.attained
```

Changing the accessible tensor space changes the input types. To use a new
physical model, supply actual normalized states and the theorem identifying the
accessible marginal. You do not type an “optimal” label or an unexplained bound.

Run the report through the normal command:

```sh
lake build
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/EnvironmentDiscriminationStudy.lean -o examples/environment-discrimination.html
```

## Reuse and scientific limits

`QuantumDiscrimination` wraps pinned Lean-QIT's
`helstrom_equalPriorError_lower_bound`, `helstromTest_equalPriorError_eq`, and
`Channel.normalizedTraceDistance_applyState_le`. The specific binary projector
uses the existing normalized pure-state idempotence theorem and matrix positivity.
The pinned public core lacks a ready-made pure-return POVM constructor, so this
small adapter proves both effects positive and their sum equal to identity.
No spectral, trace-distance, or channel infrastructure is reimplemented.

This is standard Helstrom/data-processing physics; see Watrous,
[*The Theory of Quantum Information*, section 3.1](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf).
The foundations goal beyond this baseline is an attainable optimum under explicit
restricted control and noise, with a finite-data decision procedure—not another
unrestricted-discrimination novelty claim.
