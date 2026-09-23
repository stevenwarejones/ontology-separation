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


## Numerical sensitivity checks

Before adding any more Lean, two independent linear-program checks were run to
separate three notions that are easy to conflate:

1. an early outcome that remains operationally visible;
2. an absolute friend record that remains real but is unread after a reversible
   Wigner operation; and
3. the public late-party statistics after that record is marginalized.

These are **exploratory numerical results**, not trusted proof objects.

### 1. Rebuild the forced-signaling score with reversible friend records

The repository forced-signaling atom has the form
`(x,w,a,d,f_B,f_C)`.  The check was rebuilt directly from the atom decoding,
without using the Lean LP matrix.

For the reversible-record variant:

- only atoms satisfying exact readout were retained:
  `B_0 = a` and `C_0 = d`;
- the recipient signaling TV marginalized the unread friend records `a,d`;
- the same forced-signaling score was used.

Exact-readout consistency reduces the 256 response atoms to 64 atoms.

The resulting optima were stable under HiGHS' default method, dual simplex and
interior-point solver:

| model | zero-signaling score ceiling | minimum TV budget for score 8 |
| --- | ---: | ---: |
| early outcomes operationally observed | 6 | 1/4 |
| reversible unread friend records + exact readout | 22/3 | 1/8 |

Removing exact readout from the reversible-record model makes score 8 possible
with zero signaling.  Thus the nonzero `1/8` is not produced merely by hiding
the early variables; the friend/readout consistency condition is essential.

The independent 64-atom formulation returned `1/8` and `22/3` with all three
solver algorithms, so the earlier numerical values are reproducible rather than
an artifact of the original matrix encoding.

### 2. Match the complete LF singlet probability table

The second LP did **not** optimize only the LF score.  It matched every one of
the 36 public probabilities of the repository's exact rational
`RealQuantum.lfBehavior`.

Variables were the full joint-event table

`P(c,d,a,b | x,y)`

with:

- nonnegativity and normalization inherited from exact matching of the public
  table;
- exact friend readout when `x = 0` or `y = 0`;
- setting-independent friend-record distribution;
- all 36 public outcome probabilities fixed to the exact rational singlet
  target.

Because that target is itself no-signaling, minimizing **public** signaling is
trivial: the optimum is exactly zero.

The nontrivial diagnostic is therefore the signaling that would become visible
if the absolute friend records were also revealed.  For each remote-setting
comparison, the LP minimized the total variation distance of the joint
distribution of

`(friend-record pair, local late outcome)`.

Across all 18 Alice/Bob remote-setting comparisons, the optimum was

```
delta_record-revealed = 0.1008 = 63/625.
```

The same value was returned by HiGHS default, dual-simplex and interior-point
methods.

So the complete LF table supports the same qualitative conclusion as the
score-only experiment, but not the same numerical constant:

- public signaling: **0**;
- hidden / record-revealed locality violation: **63/625**;
- score-surrogate reversible-record optimum at score 8: **1/8**.

This makes the boundary sharper.  AOE plus reversible records can hide a
positive conditional influence inside sectors that disappear on public
marginalization.  The standard LF table therefore forces a quantitative hidden
failure of blind-pair locality without, by itself, converting that failure into
an operational superluminal channel.

### What the numerics suggest checking next

The next numerical work should target the missing conversion mechanism rather
than another version of the same LF polytope:

1. extract rational dual certificates for the `1/8`, `22/3`, and
   `63/625` optima;
2. add an independently variable early friend setting or second spacetime
   context while keeping one global AOE model;
3. minimize **public** recipient TV across those contexts;
4. test asymmetric timings and one-sided readout, to determine the minimal
   geometry that turns the hidden `63/625` violation into an accessible
   signal;
5. only after a positive public optimum survives those checks, port that
   enlarged physical-model-to-LP bridge into Lean.

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
