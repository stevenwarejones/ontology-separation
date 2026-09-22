# One-step finite quantum tests

The finite complex-quantum adapter already represents a terminal experiment as a
physical channel followed by a complete POVM. This stage makes that capability a
stable, physicist-facing API instead of introducing another quantum semantics.

## Supported forms

`FiniteQuantum.oneStep evolution readout`

: one explicit QIT channel followed by one complete finite POVM.

`FiniteQuantum.measureAfterIsometry readout V h`

: one proved isometry `V` followed by a POVM. The implementation pulls the
measurement back along the isometry using Lean-QIT's
`POVM.compressByIsometry`; the proof `V† V = I` is required by the type.

These constructors produce the existing `FiniteQuantum.Test`, so all existing
normalization, behavior, local-access, and comparison theorems continue to apply.

## Nontrivial regression example

The record-access recovery experiment already uses a rational isometry and a
four-outcome POVM. The tests prove definitionally that the new helper constructs
that same experiment, then reuse the established exact probabilities:

- coherent record: recovery outcome probability = 1;
- dephased record: recovery outcome probability = 337/625.

This gives a nontrivial one-step intervention without adding floating-point
arithmetic or a replacement quantum library.

## Scope

This is not yet a general circuit language. It covers one explicit channel or
isometry plus one finite POVM. Multi-step circuits should continue to use the
existing channel composition machinery until a later stage adds a dedicated
circuit layer.
