# Finite-speed hidden influences × Local Friendliness: feasibility result

## Question

Can a Local Friendliness (LF) experiment keep **Absoluteness of Observed Events**
by replacing Local Agency with hidden influences of some finite speed `v > c`,
while still reproducing the quantum LF statistics without operational signaling?

This note records the cheapest exact test implemented in
`OntologySeparation.Experiments.LFFiniteSpeed`.

## Spacetime reduction

Take the standard two-laboratory LF protocol. Charlie and Debbie record their
outcomes early. Alice and Bob choose their Wigner-stage settings later. Choose
the timing and separation so that, in the preferred frame of a finite-speed
model, Alice and Bob are outside one another's `v`-cones.

AOE supplies one joint event table
`P(c,d,a,b | x,y)`. No-superdeterminism makes the distribution of the friend
records `(c,d)` independent of the later choices. Exact readout requires the
friend-setting outcomes to return the corresponding records.

For the late blind pair, finite-speed causal separation says that after
conditioning on the complete shared past available to both late wings—including
the absolute friend records—the remote late setting cannot change the opposite
late marginal. In the repository's existing joint-event formulation, that is
exactly `LFJoint.Local`.

Therefore the zero-hidden-influence blind-pair feasibility problem is not a new
polytope: it is precisely the already-certified LF joint model.

## Exact result

For every compatible joint table,

```
G_LF <= 6.
```

The rational two-qubit singlet witness already in the repository has

```
G_LF = 1214656 / 180625
G_LF - 6 = 130906 / 180625 ~= 0.7247391003.
```

So no AOE + exact-readout + setting-independent-record + finite-speed-blind-pair
joint model reproduces that target.

At the same time, Lean proves that the **public quantum target is exactly
no-signaling**. This is the key diagnostic outcome.

## What this does *not* prove

It does **not** yet prove the Bancal-style statement

> every finite-speed hidden-influence completion reproducing LF quantum
> predictions yields an operationally accessible superluminal signal.

The standard LF probability table only shows that conditional locality at fixed
absolute friend records must fail. A model may hide that failure inside the
unread record sectors while preserving the public no-signaling marginals.

Thus the appealing observation that LF naturally contains four *agents* does not
by itself supply the four independently usable spacetime parties/settings in the
Bancal construction.

## Next adversary search

The next target should add the missing operational bridge rather than rerun the
same LF LP:

1. Give at least one early friend wing an independently variable setting (or add
   a second late spacetime context) whose choice changes which hidden influence
   paths are available.
2. Keep a late Alice/Bob blind pair outside one another's `v`-cones.
3. Require one global AOE table/causal model across those contexts.
4. Minimize an **observable** total-variation signaling quantity over all such
   models while matching the LF quantum marginals.
5. If the optimum is positive, export the dual certificate and prove the
   physical-model-to-LP bridge in Lean, following the PR #35 pattern.

That enlarged problem is the genuine LF analogue of Bancal et al.; this PR
establishes why the unaugmented two-lab LF experiment is not already that result.

## Prior-art boundary

The implementation is intentionally conservative about novelty.

- Bancal et al. (Nature Physics 8, 867–870, 2012) prove that finite-speed hidden
  influences for Bell nonlocality lead to operational superluminal signaling.
- Bong et al. (Nature Physics 16, 1199–1205, 2020) derive LF from Absoluteness of
  Observed Events, locality/Local Agency, and No-Superdeterminism.
- Cavalcanti and Wiseman (Entropy 23, 925, 2021) analyze LF from quantum-causal
  principles and emphasize that LF is strictly stronger than Bell locality.
- The 2025 multipartite-LF-polytope work characterizes broad LF polytope
  structure. The present feasibility reduction should therefore not be sold as
  a new LF inequality or new polytope characterization.

A dedicated literature search for an explicit **finite-v LF → operational
signaling** theorem remains necessary before making a novelty claim.
