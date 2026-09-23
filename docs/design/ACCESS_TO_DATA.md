# From access restrictions to an experimental decision

This sequence builds on main after #25–26. The independent LF assumption and
readout-error stack (#27–29) should retain its own review order; these experiments
must not silently reinterpret its joint-event assumptions.

The three stages now have public examples: [physical access](../../examples/EnvironmentAccessStudy.lean),
[discrimination](../../examples/EnvironmentDiscriminationStudy.lean), and
[finite-shot design](../../examples/FiniteShotStudy.lean). The first two use
full complex-QM semantics; the statistical stage uses normalized finite joint
outcome distributions and explicit calibration/history premises. The full-state
Helstrom optimum remains symbolic, and the finite-shot rule is the conservative
all-successes rule described below.

## 1. Physical contract

Implement `RecordEnvironment`: three distinct qubits, tensor order
((system, record), environment), the existing rational source followed by a
proved copy isometry, and an explicitly specified unread measurement alternative.
Laboratory-only access includes arbitrary operations on both system and record.
Prove equivalence for that entire family. Reject attempts to label joint access
as local. Publish the preparation and assumptions in a one-import example.

## 2. Whole-class optimization

Connect accessible density matrices to the pinned Lean-QIT binary hypothesis
API. The objective is **equal-prior single-copy decision error**, not an
unqualified “best experiment.” Prove the Helstrom lower bound for every finite
binary POVM and expose the attaining measurement. In the laboratory class the
error is exactly 1/2 because the states coincide; with full modeled access the
optimum is strictly smaller. Preserve those domains in exported claims.

Also supply a specified complete binary measurement with exact model
probabilities. Distinguish its implemented performance from the mathematical
optimum. A spectral existence theorem does not certify an apparatus capable of
performing that measurement, and an averaged decision error is not a null-model
p-value. No floating-point eigensolver enters the trusted result.

Reuse upstream measurement, state, trace-distance, and Helstrom proofs. If a thin
constructor is missing, document the missing public API and prove the adapter.
Do not reimplement spectral or channel theory.

## 3. Prospective statistical protocol

Start with a conservative, explicit rejection rule for the implemented binary
measurement. Name which law is the null; require an upper bound on its success
probability for every relevant trial history. Distinguish an ideal Born
probability from the assumed/calibrated bound for an actual instrument.

The first procedure may have a deliberately narrow rejection region (all
successes in a predeclared block). Prove its false-rejection bound from normalized
finite distributions and explicit trial assumptions; report its limited power.
A parameter edit must recompute the certificate, and weakening the calibration
past the requested significance must make the proof fail. A failed rejection
must render as inconclusive, never “null proved true.” No actual dataset is
claimed, no optional stopping is silently supported, and no posterior ontology
probability is reported.

Subsequent extensions should add useful count thresholds, power/sample-size
optimization, and calibration uncertainty with a separately budgeted failure
probability. Reuse mathlib probability infrastructure where it provides the
needed finite event/product bounds. Keep the finite adopter interface small.

## What would count as the next scientific leap?

This baseline is standard quantum discrimination, not a new post-LF theorem.
The ambitious follow-up is a parameterized restricted-access optimization:
which environment information, coherent control, or trusted calibration is
necessary and sufficient for a separating experiment? A useful new result would
combine an explicit attainable protocol, a converse over all allowed protocols,
and a noise/finite-data region. Merely adding another example is insufficient.

Compare each target against known Helstrom/data-processing and recovery results
before making novelty claims. Scope the theorem to a reviewable physical class,
and seek outside review of that translation; Lean certifies the stated premises,
not the adequacy of a chosen laboratory model.

The next scoped benchmark and the remaining non-textbook target are tracked in
[the partial-access flagship contract](PARTIAL_ACCESS_FLAGSHIP.md), informed by
[the LF readout/recovery literature audit](../research/LF_READOUT_LITERATURE.md).
