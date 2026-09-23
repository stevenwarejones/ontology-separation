# Design a finite-shot rejection test

Start with `examples/FiniteShotStudy.lean`, using the single public import
`OntologySeparation.Statistics`. Its [report](../examples/finite-shot.html) is a
**prospective design**. No laboratory dataset or observed rejection is asserted.

## The eight-shot example

```lean
def planned := ReturnStatistics.design 8 (1/100) (1/100)
```

The arguments are: fixed number of shots, allowed upward calibration error in
the null success probability, and maximum false-rejection probability α.
Routine rational inequalities are proved automatically. Invalid rates, zero
shots, or an inadequate shot count cause Lean elaboration to fail.

Use the [return-to-source measurement](ENVIRONMENT_DISCRIMINATION_GUIDE.md)
on each shot. `true` means the return test succeeded. The **null** is the
specified irreversible-measurement law; coherent copying is the alternative.
Decide the rule before collecting data:

- Eight successes: reject the specified null **under the stated premises**.
- Any failure: inconclusive. This does not prove the null or an ontology true.

The eight observations have type `Fin 8 → Bool`. Missing/extra shots cannot
silently pass as a complete block. This initial API expects a typed Lean input;
it is not yet a CSV importer or an apparatus control system.

## What the numbers mean

The null Born probability is proved to be 337/625. Add a justified allowance
of 1/100, giving `q = 1373/2500`. The false-rejection bound is `q^8`, approximately
**0.008277**, below the requested 0.01. The report retains the exact rational.

With a separately justified recovery-loss bound of 1/100 under coherent copying,
the probability of eight successes is at least `(99/100)^8`, approximately
**0.922745**. The report expresses the complementary missed-detection bound.
This is a conditional power guarantee, not a measured recovery efficiency.

An all-successes rule is deliberately conservative. At lower recovery success,
its power falls rapidly. It is not sample-optimal and it discards useful evidence
in mixed success/failure blocks. Count thresholds and likelihood-ratio procedures
are subsequent extensions, not silently covered by this proof.

## The assumption that makes repeated trials legitimate

The core input is a normalized **joint distribution of the entire block**;
it may contain trial dependence and memory. Let `prefixMass k` be the actual
probability that the first k outcomes are all successes. The null premise is

`prefixMass (k+1) ≤ q * prefixMass k`, for each `k < shots`.

On a positive-probability prefix this is a conditional success bound. The
multiplicative form also handles impossible prefixes without division. Iteration
proves the all-successes probability is at most `q^shots`.

The physical wrapper `CalibratedNull` uses the proved return probability plus
the allowance in exactly this condition. A single unconditional success estimate
is not enough. For example, two perfectly correlated fair bits each have a 1/2
marginal success probability, but their all-success probability is 1/2, not 1/4.
The regression suite constructs this counterexample and rejects its history bound.

Independent repeats of a calibrated instrument are one way to justify the
premise. Independence is not inferred by the library, and this PR does not
provide an IID quantum tensor-product bridge. Alternatively, a uniform
history-dependent instrument bound can suffice. Both require physical review.

For the power calculation, `RecoveryGuarantee` separately bounds success from
below after each preceding success. The proof uses the coherent Born probability
1 minus the stated loss. It does not derive instrument fidelity from a label.

## Calibration is not free evidence

Choose the allowance from a justified calibration model or independent analysis,
not by adjusting it until the observed block rejects. If calibration itself can
fail with probability ε, the α guarantee here is conditional on valid calibration;
a combined unconditional guarantee needs a further failure budget and proof.
This PR does not supply that calibration-uncertainty analysis.

The rule is for **one predeclared block**. Repeatedly trying blocks until one
rejects, searching for a favorable interval, choosing the sample size after
seeing outcomes, or dropping failed shots changes the test. There is no optional
stopping, repeated-testing correction, detection-loophole closure, or device-
independent significance claim in this example.

## Try a verified edit

Change the first `(1/100)` in `design 8 (1/100) (1/100)` to `(1/200)` and rerun:

```sh
lake build
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/FiniteShotStudy.lean -o examples/finite-shot.html
```

The exact risk changes automatically. Change it to `(1/5)` instead and the
requested 1% guarantee fails to prove; the exporter preserves the previous valid
report. CI exercises both edits in an independent adopter project.

The report's bound constructors include normalized satisfying distributions,
so neither the null bound nor the power bound relies on an empty mathematical
class. Those witnesses establish mathematical non-vacuity, not physical
calibration of your instrument. Every physical premise remains visible.

## Reuse and next research step

Reuse the existing `FiniteDistribution`, deterministic finite channel, and
mathlib finite sums/order arithmetic. The new probability calculation is the
specific prefix-event bound; no new general probability, channel, or POVM
framework is introduced. The measurement probabilities come from #31's checked
quantum model.

The ambitious follow-up is to combine restricted-control/noise optima with a
more efficient verified count or likelihood-ratio test and separately certified
calibration uncertainty. That would turn an ideal separator into an actionable
experimental design without overstating what a finite dataset establishes.
