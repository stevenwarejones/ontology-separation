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


## Trust status

This repository treats Lean as the source of truth. Solver output may be used to
discover conjectures and certificates, but a numerical optimum is **not** an
established result until Lean checks the corresponding exact statement.

The current status is:

| statement | status |
| --- | --- |
| blind-pair compatibility is the existing LF joint model | **Lean-certified** |
| every compatible table obeys `G_LF <= 6` | **Lean-certified** |
| exact quantum LF gap `130906/180625` | **Lean-certified** |
| public quantum target is exactly no-signaling | **Lean-certified** |
| record-revealed TV is nonnegative | **Lean-certified** |
| conditional locality forces every record-revealed TV to zero | **Lean-certified** |
| reversible-score candidate `delta = 1/8` at score 8 | **numerical candidate only** |
| reversible-score zero-signal ceiling `22/3` | **numerical candidate only** |
| full-table record-revealed candidate `63/625` | **numerical candidate only** |

The three numerical values are represented in Lean under
`LFFiniteSpeed.NumericalCandidates`, but **no theorem asserts their optimality**.

## Trusted record-revealed diagnostic

`OntologySeparation.Experiments.LFFiniteSpeedDiagnostics` now defines the
quantity used in the numerical discussion directly in Lean.

For a joint AOE table `P(c,d,a,b|x,y)`, it defines:

- the joint distribution of the record pair and Alice's local outcome;
- the analogous distribution for Bob;
- total-variation distance under a remote-setting change;
- a uniform `RecordRevealedWithin` budget.

Lean proves

```
LFJoint.Local j
  -> RecordRevealedWithin j 0.
```

So "record-revealed signaling" now has a precise trusted meaning: it measures
failure of the same conditional locality law used by the finite-speed blind-pair
model.  It is still **not** public operational signaling because the friend
records need not be available after the Wigner reversal.

## Numerical candidate targets

The exploratory LP search suggested three exact rational targets:

```
score-8 reversible-record TV       = 1/8
zero-signal reversible score       = 22/3
full-LF-table record-revealed TV   = 63/625
```

These values were stable across multiple HiGHS algorithms, which makes them good
certificate targets, but solver agreement is not proof.

The full-table theorem obligation is now named in Lean as

`LFFiniteSpeed.FullTableCandidateStatement`.

It says, in substance: every joint AOE table with exact friend readout,
setting-independent records, and public behavior equal to the exact repository
quantum LF target must have at least one record-revealed remote-setting TV of
`63/625` or larger.

That proposition is intentionally **unproved**.  Once an exact rational dual
certificate is extracted, the PR should add a kernel-checked proof plus, ideally,
an attaining table establishing sharpness.

The `1/8` and `22/3` score-surrogate values remain discovery targets rather
than trusted repository results until the reversible-score LP itself is given a
fully explicit Lean model and exact certificates.

## Promotion criteria

A numerical candidate is promoted to an established repository result only when
all of the following are present:

1. the physical/model class is defined in Lean;
2. the optimized observable is defined in Lean;
3. an exact rational upper/lower certificate is checked by Lean;
4. the physical model is bridged to the certificate LP without an unproved
   encoding assumption;
5. for a claimed optimum, an explicit attaining model is also checked.

This is the same standard used by the forced-signaling work after PR #35.

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
