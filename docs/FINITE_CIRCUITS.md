# Finite channel circuits

This layer extends one-step finite tests to sequential circuits without replacing
Lean-QIT's channel semantics.

A `FiniteCircuit.Circuit A` is a list of proved CPTP channels `A → A`.
`Circuit.channel` compiles the list by QIT channel composition, with list order
equal to execution order. A final complete POVM is attached with
`FiniteCircuit.test`, producing the existing `FiniteQuantum.Test`.

## What is proved

- the empty circuit acts as the identity channel;
- a cons step acts first, followed by the compiled remainder;
- a compiled circuit plus POVM uses the ordinary Born probability;
- every resulting test is normalized.

The regression suite uses two distinct physical measurement channels on the
record-access registers: coordinate dephasing first, followed by the recovery
POVM measurement. The expected expression fixes that execution order, providing
a stronger cross-check than repeating the same channel twice.

## Current boundary

The first circuit surface keeps the register type fixed between steps. Lean-QIT
itself supports channels between different finite types, but a heterogeneous
typed circuit language needs additional syntax and composition bookkeeping.
That extension should be added only when a concrete protocol needs it.
