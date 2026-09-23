# Radical foundations program: structured adversary search

This program asks for a Bell -> Local-Friendliness-sized conceptual step while
treating known reductions, benchmark reproductions, and adversarial failures as
scoping information rather than discoveries.

## Common discovery contract

Every candidate theorem must pass the same sequence.

1. Operationalize each premise as a predicate on an explicit model, process,
   record, access policy, or intervention structure.
2. Fix the target behavior, controls, settings, outcomes, access and timing before
   optimization.
3. Define the strongest plausible adversary class first.
4. Let numerical search propose witnesses/facets, but certify the universal claim
   in Lean.
5. Delete every claimed premise and construct a target-realizing adversary whenever
   that premise is removed.
6. Prove a physical bridge from an explicit circuit/channel/process semantics.
7. Stress-test access assumptions, nuisance parameters and quantifier order.
8. Audit prior art after the mathematical object is fixed.
9. Label reproductions and scope results as such.
10. Reserve any novelty claim for a result surviving independent re-derivation and
    the strongest identified adversary.

A rigorous collapse or impossibility result is preferable to a weak positive claim.

## Benchmarks and scoped-out formulations

The consolidated boundary-map work records several useful non-discovery results.
They are not active breakthrough tracks:

- **Operational / Noncontextual Friendliness:** retained as the calibration example
  for the structured-adversary API. The reduced benchmark is reproduction-level;
  a paper-faithful friend-protocol bridge remains useful infrastructure, not a
  novelty target by itself.
- **Reduced timelike 2222 model:** the factorized operational reduction embeds in
  ordinary Bell screening-off. Further work must retain the distinctive
  pseudo-event/time-symmetry structure rather than adding settings to the reduced
  Bell-local abstraction.
- **Unconstrained scalar causal-order tests:** if setting-dependent reporting is
  unrestricted, any scalar table is mimicked. Future P06 work must fix shared,
  calibrated instruments/processes across settings before hull/facet search.
- **Passive nested observers:** arbitrary finite layers that merely copy friend
  records leave the public behavior class equal to ordinary LF. Observer depth
  alone is not a new resource.
- **Locality-free shared facts + faithful contextual readout:** this is ordinary
  contextual marginal gluing (Specker-triangle level structure). Future
  locality-free work must retain friend-specific intervention or record semantics.

These results answer "what must a stronger formulation include"; they are not
presented as candidate post-LF discoveries.

## Active Track 1 — Paper-faithful memory-awareness bridge

Baumann--Brukner's no-signaling/memory result is known prior art. The repository
now has a deletion-minimal operational benchmark and an exact arithmetic
reproduction of a negative B.29 probability.

The remaining useful target is formalization fidelity:

1. encode the entangled source, friend's measurement, Bob's basis choices and
   Wigner's measurement;
2. derive the pre/post friend--Bob probability tables internally;
3. derive the compatibility equations corresponding to B.25--B.29;
4. recover the published signaling obstruction from the circuit semantics;
5. compare every formal premise against the paper.

**Exit criterion:** a paper-to-code bridge with no hand-entered physical formula.
This is a formalization result unless a genuinely weaker/new core emerges.

## Active Track 2 — Calibrated Causal-Order Friendliness

The unconstrained-reporting adversary shows that the next P06 model must share
physical structure across settings.

1. define a finite calibrated instrument/process family before searching;
2. specify definite orders, mixtures, allowed ancillas, communication and control
   access;
3. require cross-setting consistency of the internal implementation;
4. enumerate the resulting definite-order hull;
5. obtain candidate facets and certify them exactly;
6. add explicit friend records/read-reverse operations only after the calibrated
   process witness is nontrivial;
7. run premise deletion against definite order, absolute records, agency and
   record persistence;
8. compare against existing quantum-switch/process-matrix causal witnesses.

**Candidate-new target:** a contradiction that genuinely needs both friend-record
semantics and definite causal order, rather than an ordinary causal witness.

## Active Track 3 — Access-sensitive record monogamy in full quantum mechanics

The effective overlap model gives a useful adversary benchmark, but a zero overlap
factor making a product vanish is not by itself a substantive monogamy theorem.

Next steps:

1. replace overlap lists with an explicit system + friend + finite environment
   Hilbert-space state;
2. define two superobserver access regions as typed register subsets;
3. quantify over the full allowed local recovery channels, not a selected menu;
4. include shared ancillas/classical coordination if physically allowed;
5. derive any recovery tradeoff from the quantum state itself;
6. prove sharpness and deletion-minimality;
7. audit against existing LF monogamy and quantum-Darwinism/recovery no-go results.

**Candidate-new target:** a sharp access-sensitive recovery tradeoff not implied by
known LF monogamy or generic information-disturbance results.

## Active Track 4 — Consensus / redundant records with explicit registers

The product-overlap base case and access accounting are benchmarks. The open
question is whether redundant objective records create a sharp operational barrier
to Wigner-style reversal in a fully explicit register model.

1. build the N-register branching state;
2. prove the reduced state after tracing arbitrary inaccessible subsets;
3. characterize optimal recovery/discrimination with a specified access budget;
4. identify a sharp redundancy threshold if one exists;
5. only then introduce a "consensus fact" law and run the adversary deletion test.

**Candidate-new target:** an access-sensitive theorem quantitatively connecting
redundant objectivity to reversible interference.

## Active Track 5 — Friend-specific contextuality beyond ordinary gluing

The simple locality-free benchmark collapses to contextuality and is therefore
scoped out.

Any follow-up must retain operational structure absent from a standard contextual
marginal problem, such as:

- explicit friend records;
- read versus reverse choices;
- persistence under selected interventions;
- awareness/meta-records;
- constraints linking a stored event to a later undo.

The first task is to search whether these extra friend-specific laws produce a
minimal core that is not equivalent to an existing contextuality scenario.

## Priority order

1. Merge the structured-adversary infrastructure.
2. Consolidate benchmark/negative results into one boundary-map PR.
3. Complete the Baumann--Brukner circuit-to-equations bridge.
4. Build the calibrated definite-order process class and run the first hull search.
5. Upgrade access-monogamy/consensus from overlap bookkeeping to explicit
   many-register quantum semantics.
6. Revisit friend-specific contextuality only with explicit intervention semantics.

A candidate is promoted beyond "benchmark" or "scope result" only when its
strongest plausible adversary fails for a proved reason.
