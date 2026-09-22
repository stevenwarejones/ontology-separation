# How much imperfect friend readout can an LF conclusion tolerate?

The model now allows asking a friend to disagree with their recorded outcome.
Keep the joint-event extension, locality and independent prior records; replace
perfect readout with an explicit error budget. Lean proves the best possible
score bound for this class and constructs a family that attains it.

## Try the study

Open [`examples/LFReadoutStudy.lean`](../../examples/LFReadoutStudy.lean).
It imports one public facade and sets one parameter:

```lean
def budget : ℚ := 1 / 8
```

This is an upper bound on the **sum** of the two disagreement probabilities,
not the error bound for each friend separately. The example builds three claims
from it: a bound with a satisfying model, a model attaining the bound, and an
exclusion of the existing quantum target. Export the report:

```sh
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/LFReadoutStudy.lean -o examples/lf-readout.html
```

Change the budget to `1 / 10` and rerun: both numerical claims change from
`13/2` to `32/5`. There is no separately typed numerical ceiling to update.
Changing it to `1 / 4` makes the example's **exclusion proof fail**. The generic
bound still holds, but it no longer excludes the quantum target by its score.
The exporter rejects the failed study without replacing the previous valid report.
Remove the exclusion claim and its export if your intended study asks only for
a bound at that larger budget. Failure of this proof does not establish membership.

## What the theorem says

For the same hypothetical joint table P(abcd|xy), define:

- δA = P(a ≠ c | x=0, y=0).
- δB = P(b ≠ d | x=0, y=0).

These are implemented as sums of the actual disagreeing joint events, not as
unconstrained labels attached to an ontology. Locality proves each disagreement
probability is unchanged by the remote setting. Under local, independently
prepared records:

**S ≤ 6 + 4(δA + δB).**

For every total budget t in [0,1], `sharp_total_budget` proves both:

1. Every admissible joint table with δA + δB ≤ t has S ≤ 6 + 4t.
2. An explicitly constructed joint table has δA = δB = t/2 and S = 6 + 4t.

This is optimality over the stated class of joint tables, not a search over a
finite list of recipes. It is also not a claim that the attaining tables are
quantum-realizable: the construction deliberately uses a no-signaling extremal
box. The interval ends at t=1, where the bound reaches the no-signaling ceiling 10.

Separate bounds δA ≤ a and δB ≤ b yield S ≤ 6 + 4(a+b), via
`separate_budgets`. We prove attainability for the total budget, not a separate
sharpness theorem for every asymmetric pair (a,b).

## What the quantum target requires

The existing exact quantum score is 1214656/180625. Any extension satisfying the
retained laws must have total disagreement at least **65453/361250**, approximately
0.18118. Thus a total budget of 1/8 excludes this target; 1/4 does not exclude it
using this score bound. That last statement does not certify that the target's
whole probability table belongs to the larger-budget class.

A violation of this relaxed bound excludes the conjunction of joint-event
existence, conditional locality, independent records and the error-budget
constraint. It does not identify a uniquely false assumption.

## Experimental interpretation and prior art

These are exact probabilities, not confidence intervals. A calibration run on a
modified apparatus does not automatically bound the disagreement in this same
joint table. That connection requires its own physical and statistical assumptions.
Records erased in other settings need not be simultaneously accessible. The
framework has not inferred a laboratory rejection from these theoretical values.

Relaxed LF is established prior art. [Moreno et al., Quantum 6, 785 (2022)](https://quantum-journal.org/papers/q-2022-08-24-785/)
introduce imperfect agreement and give the symmetric 6+8ε bound for this genuine
LF inequality. Setting both error ceilings to ε recovers that form here. This PR
provides a machine-checked connection to our joint-event semantics, a constructive
sharp family, and an editable report workflow; it makes no scientific priority claim.

The [2026 agent-like-observer preprint](https://arxiv.org/html/2609.12527v1) also
uses relaxed LF and explicitly distinguishes its calibration estimate from a
rigorous upper bound. This reinforces why an empirical error bound is a separate
milestone rather than a checkbox on the present report.

## Infrastructure reused

`Shared.moment_positive`, the existing no-signaling extremal box, the saturating
LF model, `Behavior.mix`, and `Shared.LF_mix_score` supply the ingredients.
`LFJoint` supplies conditioning and observable reconstruction. The added linear
bound concerns the LF statistic and recorded disagreement; no new linear algebra,
POVM, quantum-channel or tensor representation is introduced.
