# Certified partial-leakage study

This public example deliberately exports two different kinds of checked result.

## Exact point

At visibility `v=1/2` and recovery efficiency `r=3/4`, the finite exact
comparison checks the supplied recovery probe and reports

- Wigner/recovery probability: `11/16`;
- fully leaked friend probability: `1/2`;
- exact oriented gap: `3/16`.

This is a checked statement at one exact parameter point and one supplied finite
experiment family.

## Symbolic region

A separate theorem claim proves over the physical real square

`0 < Δ(v,r) ↔ 0 < v ∧ 0 < r`

under `0≤v≤1` and `0≤r≤1`.

The report keeps this theorem in the formal-results section rather than
presenting it as a finite comparison card. The continuum theorem follows from
the specified partial-leakage/recovery model only; it is not a claim about all
Wigner-friend models or all possible recovery operations.

The independent downstream Lake-project gate copies this example and requires
both the exact `3/16` point result and the separate theorem export.
