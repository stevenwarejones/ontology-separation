# Symbolic robustness region

This theorem is deliberately separate from the finite automatic checker.

For visibility `v` and recovery efficiency `r`, the partial-leakage model
derives the exact recovery-probe gap

`Δ(v,r) = v r / 2`.

The real-valued theorem proves, for nonnegative physical parameters,

`Δ(v,r) > 0 ↔ v > 0 ∧ r > 0`.

Within the physical square `[0,1]²`, the separating region is `(0,1] × (0,1]`.
It includes the upper edges and the ideal corner; it is not the open interior. The theorem `real_channel_gap` derives the same formula directly from the existing real-qubit dephasing-channel/Born-rule semantics across the full physical square. The exact rational backend is then proved to embed into that real formula, and every exact point with positive visibility and recovery receives the existing proof-bearing separator certificate.

At `v=0` or `r=0`, the recovery witness has zero gap. In this particular
effective-law family, `zero_visibility_law` and `zero_recovery_law` prove the
stronger fact that the two laws are equal, so every recipe in this backend
agrees there. This does not identify broader physical ontologies or models
with extra degrees of freedom.

`real_channel_gap` connects the formula to actual real-qubit dephasing
semantics for every real `v,r ∈ [0,1]`. The real theorem is therefore not
just extrapolation from rational samples. This remains an ideal exact
separation condition: it gives no finite-shot sample complexity or tolerance
to uncertainty in measured probabilities.

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
