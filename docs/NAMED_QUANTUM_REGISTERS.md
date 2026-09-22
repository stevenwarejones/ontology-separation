# Typed named quantum registers

This layer connects named access policies to the quantum type system for a
two-register state `State (A × B)`.

## Why both names and types matter

Register names answer the operational question “which systems may this protocol
touch?” The tensor types answer the mathematical question “which Hilbert-space
factor does this channel act on?”

`FiniteQuantum.Named.Protocol` therefore has two constructors:

- `localTest : Test A C O → Protocol A B C O`
- `jointTest : Test (A × B) C O → Protocol A B C O`

A local protocol cannot contain a channel typed on `A × B`; Lean rejects that
before the access proof is considered. The register footprint is then derived
from the constructor:

- local → the named left register
- joint → both named registers

This avoids a dangerous design where a joint operation could be hidden behind a
user-entered “local” label.

## Checked reduction

Local prediction uses `ρ.marginalA`; joint prediction uses the full state.
The theorem `FiniteQuantum.Named.left_equivalent` proves that equal left
marginals imply agreement for every protocol admitted by the left-register
policy.

The existing coherent/dephased record states instantiate this theorem directly:
their system marginals are equal, so all typed system-only tests agree. The
existing recovery operation is a joint test and is rejected by the left-only
policy.

## Current boundary

This is a checked two-register abstraction. It does not yet claim a general
dependent tensor decomposition for an arbitrary set of named registers. Moving
to many registers requires explicit reindexing/partial-trace maps and proofs that
register permutations preserve the intended physical subsystem.
