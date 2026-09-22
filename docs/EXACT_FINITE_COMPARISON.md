# Exact finite comparison contract

This is the execution boundary for automatic finite comparison.

## Contract

`ExactFinite.Backend predict` is parameterized by the already-selected normalized
`ExperimentAccess.Predictions M P E` semantics and contains:

- an exact rational probability function for every model, protocol, setting and outcome;
- a proof that every rational value equals the corresponding probability from that exact `predict` semantics.

For example, the recipe adapter constructs `exactBackend : ExactFinite.Backend predict`,
where `predict` is definitionally the existing recipe `interpret` semantics. The backend
therefore cannot silently substitute a different physical prediction function.

`ExactFinite.EquivalentQ` states equality of those rational probabilities over an
explicit access predicate. The checked theorem
`ExactFinite.equivalent_iff_exact` connects that proposition to the existing
`ExperimentAccess.Equivalent` semantics.

The contract does **not** say that a finite protocol family exhausts all physically
allowed experiments. Any broader agreement claim still requires the existing
coverage evidence.

## First backend

The single-qubit recipe adapter implements this contract using
`RecipeSeparation.outcomeProbability`. Its correctness reuses the already-proved
recipe evaluator correspondence and normalization, so the automatic comparison
layer does not introduce a second physical semantics.

The two-qubit, Local Friendliness, and general complex-quantum layers are not
silently covered by this adapter.

## Automatic checker

The accompanying checker enumerates an explicitly supplied finite domain and
return one of:

1. agreement over that exact domain;
2. a separator with positive `a-b` gap; or
3. a separator with positive `b-a` gap.

The orientation is explicit so the implementation never assumes the first
difference has the desired sign. A failed/incomplete search must never become an
agreement certificate.
