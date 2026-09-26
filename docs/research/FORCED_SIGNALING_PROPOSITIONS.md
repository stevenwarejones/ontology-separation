# Forced-signaling Propositions 1 and 2

This note records the Lean 4 scope of Propositions 1 and 2 from the
[forced-signaling manuscript](https://github.com/stevenwarejones/forced-signaling).
The source certificates are `paper/directional_certificates.json` and
`paper/invisible_certificates.json`, whose standalone exact verifiers are
`verify_directional.py` and `verify_invisibility.py`. They were ported from
`stevenwarejones/forced-signaling` commit
`bae83b865ea60b1fbc4b808e66dc9bbaf7da2d4b`; no certificate values were
adjusted during the Lean port.

The formalization makes no novelty claim and has not been reviewed by a human
domain expert.

## Proposition 1: directional refinement

[ForcedSignalingDirectional.lean](../../OntologySeparation/Experiments/ForcedSignalingDirectional.lean)
splits the sixteen early-setting recipient-TV comparisons exactly as the source
LP does:

- contexts 0–7 change A's early setting `x`; their maximum is `deltaA`;
- contexts 8–15 change D's early setting `w`; their maximum is `deltaD`.

`signaling_eq_max` proves that the scalar signaling strength already used by
Theorem 2 is exactly `max deltaA deltaD`.

The existing K=8 dual certificate is then reused row-for-row.
`directional_bound` proves for every `HiddenInfluence.Model`

```
score m.behavior <= 6 + 4 * deltaA m + 4 * deltaD m.
```

For every exact LC4 marginal match,
`lc4_directional_lower_bound` consequently proves

```
(sqrt 2 - 1) / 2 <= deltaA m + deltaD m.
```

[ForcedSignalingPropositionWitnesses.lean](../../OntologySeparation/Experiments/ForcedSignalingPropositionWitnesses.lean)
ports the two **distinct** primal models from
`directional_certificates.json`. Lean recomputes their normalization, every
ABD/ACD LC4 marginal, all recipient differences and TVs. The resulting
`DirectionalA` and `DirectionalD` models attain respectively

```
(deltaA, deltaD) = ((sqrt 2 - 1)/2, 0)
(deltaA, deltaD) = (0, (sqrt 2 - 1)/2).
```

[ForcedSignalingPropositions.lean](../../OntologySeparation/Experiments/ForcedSignalingPropositions.lean)
also lifts the directional definitions and inequality to the finite stochastic
conditional-local class through the already-proved determinization bridge.

## Proposition 2: pairwise-invisible attainment

The same witness module separately ports the three models
`InvisibleA`, `InvisibleD`, and `InvisibleBalanced` from
`invisible_certificates.json`; these are not identified with the Proposition-1
certificate models.

For each model Lean checks:

1. every response weight is nonnegative and each early-setting block is normalized;
2. every ABD and ACD no-blind-pair marginal equals the exact LC4 target;
3. all three single-recipient and all three two-recipient projections are
   unchanged under A-setting flips, for every fixed `w,y,z`;
4. the analogous six proper recipient projections are unchanged under D-setting
   flips, for every fixed `x,y,z`;
5. changes of B or C setting cannot signal even to the complete complementary
   three-party record (the existing conditional-locality theorem is stronger
   than the single/pair checks required here);
6. the surviving A/D full-three-party difference is a pure binary parity shift;
7. the exact directional values are
   `((sqrt 2 - 1)/2,0)`, `(0,(sqrt 2 - 1)/2)`, and
   `((sqrt 2 - 1)/4,(sqrt 2 - 1)/4)`.

The public predicate `PairwiseInvisible` and theorem
`pairwise_invisible_optimum` package these facts. The latter states that
adding the pairwise-invisibility requirement does not change the LC4 minimum of
`deltaA + deltaD`.

## Deliberately not formalized here

This PR does **not** formalize the manuscript's Lemma 2 classification of which
recipient sets can carry signal, the collectibility conditions, the
spacetime-geometry examples, or any claim that the surviving full-record signal
is experimentally accessible. Those remain analytic/Python-supported statements
in the manuscript package.

It also does not add a finite-sample confidence protocol. All bounds here are
exact expectation-level statements within the stated finite conditional-local
model class.

## Verification

The real tests are in
[Tests/ForcedSignalingPropositions.lean](../../Tests/ForcedSignalingPropositions.lean).
Public trust roots are registered in
[Tests/Audit.lean](../../Tests/Audit.lean), and `sh scripts/check.sh`
regenerates [docs/AXIOM_AUDIT.txt](../AXIOM_AUDIT.txt).
