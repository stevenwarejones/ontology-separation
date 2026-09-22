# What assumptions does the finite LF model actually impose?

Use [the checked report](../../examples/lf-assumptions.html) or inspect
[the public Lean example](../../examples/LFAssumptionStudy.lean).

The three operational premises have literal mathematical meanings:

| Premise | Meaning in this model |
|---|---|
| Readable records | Selecting setting zero returns the latent Charlie/Debbie record with certainty, at every remote setting |
| Conditional locality | Each latent conditional response table has remote-setting-independent local marginals |
| Independent preparation | The latent-state distribution is the same at every pair of settings |

The new theorem proves that a public behavior belongs to the repository's finite
LF conditional-box class **if and only if** it has such an operational model.
Every output probability is preserved in both directions. This strengthens the
previous one-way bridge into an exact correspondence for this encoding.

A second result supplies a normalized, nonempty model satisfying all three
premises but violating outcome independence. Its inner PR box is allowed by LF;
it is not quantum-realizable. It is used to disprove an implication between
assumptions, not proposed as a laboratory preparation. In particular, the
countermodel makes the explicit conditional probability 1/2 differ from the
product of its two 1/2 marginals, which is 1/4.

The third result transports the existing quantum exclusion to precisely this
operational class. It does not tell us which premise is false in nature.

## Recheck or reuse

From the repository root with the pinned Lean toolchain installed:

```bash
lake exe cache get
lake build
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/LFAssumptionStudy.lean -o examples/lf-assumptions.html
```

Adopters can import `OntologySeparation.Assumptions` and use
`LFAssumptionAtlas.operational_iff_lf` to move between the two representations.
`LFAssumptionAtlas.operational` constructs the reverse model and provides named
proofs of each law. There is no additional axiom to fill in.

## Scope

This is the repository's 3-settings-per-party, binary-outcome, finite latent
mixture formulation. It does not enumerate every LF facet, prove completeness
for arbitrary measurable hidden-variable spaces, or model conscious observers.
The report is a known-physics baseline for the [research program](PROGRAM.md),
not a new no-go theorem or a priority claim about formalization.
