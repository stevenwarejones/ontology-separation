# Symbolic robustness region

This theorem is deliberately separate from the finite automatic checker.

For visibility `v` and recovery efficiency `r`, the partial-leakage model
derives the exact recovery-probe gap

`Δ(v,r) = v r / 2`.

The real-valued theorem proves, for nonnegative physical parameters,

`Δ(v,r) > 0 ↔ v > 0 ∧ r > 0`.

Thus the separating region is the positive interior of the visibility/recovery
square. The exact rational backend is proved to embed into that real formula,
and every exact point with positive visibility and recovery receives the
existing proof-bearing separator certificate.

At `v=0` or `r=0`, this particular recovery witness has zero gap. The theorem
does **not** claim that the two broader model classes are globally equivalent on
those boundaries; another experiment could in principle distinguish them.

## Why this is not a finite scan

The automatic finite checker certifies a supplied finite experiment family at
specific exact model parameters.

This module instead proves one algebraic statement for every real parameter in
the stated region. A later report must keep those two claims visually and
semantically distinct:

- checked at this exact point;
- proved throughout this symbolic parameter region.

## Scientific status

The one-parameter partial-leakage visibility is motivated by the published
Wigner/friend leakage calculation documented in the preceding study. The
recovery-efficiency extension and two-parameter region are a showcase model
unless a separate literature/novelty review establishes otherwise.
