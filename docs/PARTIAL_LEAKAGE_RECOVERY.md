# Partial information leakage and imperfect recovery

This study is a **certified-derivation showcase**, not currently a novelty claim.

## Physical motivation

Del Santo, Manzano and Brukner, [*Physical Review Research* 7, 033279 (2025)](https://doi.org/10.1103/c3yq-9mc7),
analyze Wigner/friend predictions when which-outcome information leaks only
partially from the friend's laboratory. Their Appendix B gives Wigner's preferred
outcome probability as

`p_W(ω0) = [1 + cos(πθ/2)] / 2`

while the friend's corresponding prediction remains `1/2`. The predictions
coincide in the complete-leakage limit.

This module uses the directly observable visibility

`v = cos(πθ/2)`

as its exact parameter rather than formalizing transcendental trigonometry in
the rational checker. Thus `v=1` is the no-leakage limit and `v=0` is the
complete-leakage limit.

The second parameter, recovery efficiency `r`, is an explicit extension of the
showcase model: only the fraction `r v` of retained coherence is available to
the superobserver's recovery operation. This extension should not be attributed
to the cited paper without a separate derivation.

## Connection to the audited backend

The model does not directly interpolate final probabilities. It derives an
effective exposure law

`exposure = 1 - v r`

and feeds that law through the repository's already-proved real-qubit recipe
semantics. Consequently the coherence/recovery probe yields

`P_W(+) = (1 + v r)/2`

while the fully dephased friend law yields

`P_F(+) = 1/2`.

The exact gap is therefore `v r / 2`.

Calibration remains identical for both laws.

## Scope

This PR establishes the operational parameterization and exact probability
formula only. The next stacked PR proves the continuous separating region and
keeps that symbolic theorem distinct from finite-grid checking.

The `v` parameter is a rational exact proxy for the paper's visibility. This
module does not claim to formalize the paper's full unitary laboratory model or
its statistical hypothesis-testing protocol.


## What is assumed and what is derived

The product visibility law `v r` is an explicit assumption of this effective
model. `sequential_attenuation` proves a realization as two consecutive
real-qubit dephasing channels with strengths `1-v` and `1-r`. The probability
formula follows from that channel choice. This is not a derived description
of every imperfect reversal, an optimized recovery algorithm, or a theorem
identifying inaccessible laboratory records with a particular value of `r`.
The reported probabilities refer to the specified recovery probe; the paper's
full laboratory dynamics and conditional-state assignments are not formalized.
