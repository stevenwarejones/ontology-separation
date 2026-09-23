# Structured adversary search

The discovery workflow treats a proposed no-go theorem as an adversarial object, not
as a score to optimize.

For a finite set of named assumptions and a target behavior:

1. propose a candidate assumption core;
2. prove that every model satisfying the whole core excludes the target;
3. delete each premise in turn;
4. construct an explicit model satisfying every retained premise while realizing
   the target;
5. classify the result as a reproduction, an extension of known work, or only a
   candidate new core pending a focused literature audit.

Core.AdversarySearch.MinimalCore certifies steps 2--4. Search code may suggest
cores or countermodels, but a failed search is not evidence that a premise is
necessary.

## Planned physics passes

The same procedure will be applied in separate reviewable increments to:

- Operational Friendliness, as a known benchmark;
- the 2026 timelike/Causal Time-Symmetric Friendliness theorem, as a known benchmark;
- indefinite-causal-order friend protocols (P06);
- locality-free / contextual friend protocols;
- nested observer-depth protocols;
- monogamy/resource-sharing formulations, with the 2024 causal-marginal results
  treated as prior art;
- redundant-record / consensus protocols connected to environment access and
  quantum Darwinism.

A claimed breakthrough must include a checked exclusion, deletion adversaries for
the stated core, a physically explicit witness/bridge, and a novelty audit. Merely
finding a stronger numerical inequality does not meet this bar.
