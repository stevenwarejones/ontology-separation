# Two-qubit recipes: scope and trust boundary

## User outcome

Create a Bell study, change preparation/gates/noise/measurement bases, and export
exact CHSH scores through the existing proof-bearing scenario pipeline. No table
of predicted numbers and no per-cell proofs are entered by the adopter.

## Deliverable

- Exactly two named wires, Alice and Bob; four computational amplitudes ordered
  00, 01, 10, 11. Exact rational amplitudes are normalized by their squared norm.
- Product preparations and entangled preparations; local H, X, Z, directed CNOT,
  and SWAP. Wire types and a single CNOT control prevent nonexistent wires and
  equal control/target mistakes.
- Convex mixtures of pure states. Z dephasing is the physical random-unitary
  channel (1-p/2) rho + (p/2) Z rho Z: p=1 removes coherence, not a full Z flip.
- Ordered operations shared across laws. Only explicit exposure steps inspect
  the law; no model-dependent preparation or choice of measurements.
- Two local projective settings per party. Rational basis coordinates are
  orthogonal and normalized by construction; X and Z are convenient presets.
- A universal exact evaluator, normalized Born probabilities, CHSH correctness,
  and a connection to the existing Bell-local bound. Report labels derive from
  the same data evaluated by the proof.

## Architecture

`Operational.TwoQubit` owns amplitude algebra, states, gates, convex mixtures,
and Born probabilities. `Recipes.TwoQubit` owns fixed experiment data, exposure
laws, exact CHSH evaluation, and the existing Scenario adapter. Python only
scaffolds and renders checked exports. The existing Claim/export axiom audit is
used without a second reporting format.

## Explicit limits

This is real-amplitude, rational-input two-qubit quantum mechanics, not an
arbitrary-size or complex-amplitude simulator. It does not include T/S gates,
postselection, adaptive measurements, classical records, or full LF protocols.
Mixture trees can grow exponentially with exposure count; this is an exact,
small-experiment reference backend. Noise is an effective local channel, not a
classification of entire interpretations. Gates occur in preparation before
separated measurement choices; CNOT is not an allowed spacelike communication
operation in a Bell trial. Exclusion of the Bell-local class is conditional on
the mathematical model, not an empirical falsification claim.

## Extension boundary

Keep this backend named TwoQubit and preserve the backend-independent Scenario
and Claim interfaces. A later complex finite-dimensional backend should prove
its own semantic bridge and reuse those interfaces. Do not introduce nominal
arbitrary-qubit support before tensor indexing, channels, and measurement
records have their own proofs.

## Acceptance

Verify product and entangled states, H/CNOT preparation, gate direction/order,
noise endpoints and composition, all joint probabilities, CHSH above/below 2,
and agreement with the existing rational-basis singlet result. Compile and
export a fresh adopter starter. Reject invalid amplitudes, rates, bases, wires,
model-dependent recipes, duplicate rows, and unfinished proofs. Audit universal
semantic theorems and run the existing project verification gate.
