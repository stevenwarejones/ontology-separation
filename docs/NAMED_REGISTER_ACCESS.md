# Named register access policies

Access restrictions are now represented by physical register names and a
protocol footprint derived from the protocol data.

## Core rule

A concrete experiment supplies a `RegisterAccess.Footprint` function. The
framework permits a protocol exactly when every register in that derived
footprint is included in the selected `RegisterAccess.Policy`.

The footprint is not a human-entered label. A concrete adapter derives it by
pattern matching on the protocol representation, so changing report text cannot
turn a joint operation into a local one.

Access is monotone: if a protocol is allowed under a narrower policy, granting
more registers preserves that permission.

## Record-access example

The existing copied-record experiment now names two registers:

- `system`
- `record`

A `localTest` derives footprint `{system}`. A `jointTest` derives footprint
`{system, record}`.

The existing theorem that coherent and dephased models agree for every local
test is re-expressed under the `systemOnly` policy. The existing recovery
separator is accepted under `systemAndRecord`, while the same joint protocol is
provably rejected under `systemOnly`.

This does not change the quantum tensor semantics or the established
probabilities. It makes the access restriction structural and checked.

## Scope and next step

This PR provides theory-independent named access and connects the existing
two-register quantum example to it. It does not yet implement arbitrary
many-register partial traces or infer tensor decompositions from names.

A dependent quantum-register PR can add checked typed reductions/embeddings for
larger register layouts while preserving this policy contract.
