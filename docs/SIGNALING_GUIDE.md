# A sharp signaling tradeoff, from physical responses to a report

Start with [the editable study](../examples/SignalingStudy.lean) or browse its
[checked results](../examples/signaling-tradeoff.html). This study asks:
**how large can this six-term correlation score be if the allowed signaling is δ?**

```lean
import OntologySeparation.Signaling
open OntologySeparation

def study := SignalingStudy.design (1/8)
noncomputable def bound := study.boundClaim
noncomputable def attainingModel := study.attainmentClaim
noncomputable def actualSignaling := study.signalingClaim
#export_claim bound
#export_claim attainingModel
#export_claim actualSignaling
```

From the repository root, with the existing Python/Lean setup:

```sh
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/SignalingStudy.lean -o examples/signaling-tradeoff.html
```

Change the allowed budget and rerun. You do not write a new proof or enter predicted
values: the general theorem supplies them. A negative budget fails Lean checking.
The three claims have different meanings: a bound for **every** admitted model,
a physical response model attaining that bound, and that model's actual signaling.

| Allowed TV budget δ | Whole-class optimum | Attaining model's actual signaling |
|---|---|---|
| 0 | 6 | 0 |
| 1/8 | 7 | 1/8 |
| 1/4 | 8 | 1/4 |
| 1/2 | 8 | 1/4 |

The maximum is `min (6 + 8*δ) 8` for every real δ ≥ 0. The rational study is an
editable reporting front end to that theorem. In particular, an allowed budget
is not automatically an observed signaling strength. The score saturates at 8.

## What physical assumptions are being made?

There are four binary-output parties A, B, C, D, with respective binary settings
x, y, z, w. A and D are early. A response model chooses a joint distribution of
early outcomes and complete response tables for B and C, separately for each
(x,w). That distribution cannot depend on the late choices (y,z). B then consults
only y and its table; C consults only z and its table.

This is the **finite conditional-local response class** implemented by
`HiddenInfluence.Model`. Neither a score bound nor no-signaling is assumed in
its definition. Normalization and nonnegativity produce an actual `Behavior`.
Lean proves that changing B's setting cannot affect the joint A,C,D distribution,
and likewise C cannot affect A,B,D. Early-setting changes can signal.

For each change of x or w, keeping the other settings fixed, compare the joint
probabilities of **all three other parties**. The total-variation distance is
half the sum of absolute probability differences. `Within behavior δ` bounds
every one of these 16 comparisons; it is not an average or a collection of
single-recipient marginal bounds. `Model.signaling` is their maximum. The two
remaining sender directions vanish by the no-signaling theorems above.

This is an explicit causal response model, not a formal derivation from a
spacetime diagram. Equivalence to general hidden-variable conditional-local
formulations with arbitrary hidden-state spaces is a separate representation
obligation. No quantum realizability or cluster-state marginal matching is
asserted for the attaining model.

## Which score?

Outputs `false`/`true` mean +1/−1. Each correlation is an expectation of the
product of the indicated signs, at the fully specified setting below. Specifying
the otherwise omitted settings matters when signaling is allowed.

| Coefficient | Correlation | (x,y,z,w) |
|---|---|---|
| +1 | AB | (0,0,0,1) |
| +1 | AB | (0,1,0,1) |
| +1 | ABD | (1,0,0,0) |
| −1 | ABD | (1,1,0,0) |
| +2 | CD | (1,0,0,0) |
| +2 | ACD | (0,0,1,1) |

The sharp slope 8 is proved for **this fixed completion**, with intercept 6.
It does not establish optimality over all completions, a quantum optimum, a
measurement of signaling in a laboratory, or a finite-sample hypothesis test.

## Add a response model without touching the LP

`HiddenInfluence.Strategy` has Boolean fields `a`, `d`, `b0`, `b1`, `c0`, `c1`.
For example, `{ a := false, d := false, b0 := false, b1 := true,
c0 := true, c1 := false }` describes six physical responses. The Boolean fields
reject numeric values such as 2; they cannot silently wrap modulo two.

Supply one `FiniteDistribution Strategy` for each of the four early settings to
`HiddenInfluence.Model.fromStrategies`. Each distribution contains a mass
function, a nonnegativity proof and a proof that its total is one. The theorem
`strategy_output` checks that the named responses really become the intended
outputs for every setting. A complete deterministic distribution example is in
[Tests/Signaling.lean](../Tests/Signaling.lean).

For sparse mixtures, `Model.ofAtoms` accepts any finite seed type and weights,
with normalization per early setting. Packed atom indices are an implementation
interface; named strategies are the adoption interface.

Given a model and a proof of its observable budget, `Model.toLP` constructs its
feasible LP point automatically. `score_bound` then gives `score ≤ 6 + 8*δ`;
`sharp_bound` also includes the algebraic ceiling. Users supply no LP rows,
auxiliary variables or coefficient correspondence assumptions.

## Why the sharpness claim is stronger than a solver answer

1. Observable probabilities define the score and all recipient TV distances.
2. `HiddenInfluenceEncoding` checks that independently defined physical
   coefficients equal the pinned LP's objective, normalization and constraints.
3. `Model.toLP` fills auxiliary variables with actual absolute probability
   changes, proving feasibility from the physical budget. `lp_score` proves
   the objective is the physical score.
4. The previously checked rational dual bounds every such real feasible point.
5. An explicit 26-atom rational response model has score 8 and maximum TV 1/4.
   Its normalization, individual signed changes and all 16 TVs are rechecked
   in Lean. Only contexts 5, 7, 12 and 14 have nonzero TV, each exactly 1/4.
6. Mixing this model with the all-zero-output model attains every point from
   (δ,score)=(0,6) to (1/4,8). Larger budgets use the same endpoint model.

A numerical LP solver helped discover the endpoint. Its answer is not trusted:
the Lean proof checks the explicit rational model through physical probabilities.
No solver, `native_decide`, additional axiom or unfinished proof enters the export.
The coefficient identity module uses kernel-checked finite decisions and can take
a few minutes on its first build; subsequent downstream edits reuse the build.

The LP provenance is the MIT-licensed
[forced-signaling source](https://github.com/stevenwarejones/forced-signaling/tree/bae83b865ea60b1fbc4b808e66dc9bbaf7da2d4b).
See [the reconciliation spike](research/TRADEOFF_DECISION_SPIKE.md) for the earlier
certificate-only milestone and limits of the broader unification proposal.

## Framework lessons from forced signaling

**Reuse:** finite probability, normalized behaviors, exact arithmetic, `Claim`,
transitive axiom auditing and report generation already provided the surrounding
workflow. No new quantum or linear-algebra backend was necessary.

**New reusable contract:** `SharpOptimum admissible score value` bundles a
whole-class upper bound with an admissible physical model attaining the same
value. Its bound and witness exports derive from that one object. This prevents
accidentally combining a bound for one class with a witness from another, or a
physical upper bound with a merely feasible LP witness. It does not prove that
an author's chosen model class faithfully describes nature.

**Domain-specific conveniences:** named response strategies, sparse mixtures,
a proved physical-to-LP adapter, and the budget-driven study remove repeated
indexing and report proofs. The adapter stays explicit: compiling a physical
model into numerical constraints is precisely where a semantic mistake could
hide.

**Next abstraction only when needed:** a second certificate port should test a
generic finite LP/dual interface with observable-preserving maps. This example
alone does not justify a universal physics compiler. Robust/minimax studies also
need their own quantifier order: a best model under a budget is not a single
protocol guaranteed to work for every uncertain model. `SharpOptimum` does not
silently identify those problems.
