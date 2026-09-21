# Which experiments can separate two models?

Start with the access question: **what can the experimenter actually control or
read?** A comparison without that boundary can make two models appear different
using a measurement that the experimenter cannot perform.

The library now has two reusable layers. `ExperimentAccess.Equivalent` says two
models agree on every allowed protocol, setting and outcome. `Separator` supplies
one allowed protocol and a proved positive probability gap. It is impossible to
supply both for the same family. Restricting access preserves equivalence;
expanding access preserves a separating witness.

```lean
import OntologySeparation.Adapters.FiniteQuantum
open OntologySeparation
```

## Build a quantum test

A `FiniteQuantum.Test A B O` consists of `evolution : QIT.Channel A B` and
`readout : QIT.POVM O B`. Here `A` and `B` index the input and output basis states;
`O` indexes recorded outcomes. `Bool × Bool` describes two qubit registers; a
custom finite type can describe a different finite system.

Use `FiniteQuantum.measure myPOVM` for a measurement with no preceding evolution.
Use `test.prepend myChannel` to add a physical process before a test.
`FiniteQuantum.behavior state tests` turns a setting-indexed family into the
same normalized `Behavior` used by the rest of the framework.

The underlying states are complex density matrices, channels are completely
positive and trace preserving, and POVMs are positive and complete. These are
Lean-QIT types already pinned by this repository. Supplying an arbitrary matrix
without those proofs does not construct a physical operation. Common QIT
constructors discharge those obligations; custom operations require a proof.

## State what is inaccessible

For `state : QIT.State (System × Environment)`, `state.marginalA` traces out the
environment. If two joint states have equal `marginalA`,
`FiniteQuantum.local_test_eq` proves that **any** local channel followed by **any**
finite POVM gives the same probabilities. This is stronger than trying a few
measurement angles. It includes any finite local processing representable by a
CPTP channel followed by a terminal POVM; it does not include access to the other
register or unmodeled interventions before the supplied states were prepared.

## Trust and scope

These semantics support arbitrary finite complex systems; they are not a fast
arbitrary-circuit simulator or an automatic proof generator. Existing rational
Bell/LF recipes keep their own proven fast evaluators. A numerical search result
becomes a proved framework result only when accompanied by a checked theorem.

See [the implementation plan](design/UNIVERSE_SEPARATION.md) for the record-access
example and model-class certificates developed in the following PRs.
