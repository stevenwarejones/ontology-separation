# Structured comparison reports

Automatic comparison already returns proof-bearing agreement or an oriented
separator. This layer makes the same checked result readable without asking a
physicist to decode the full Lean proposition.

A structured comparison report derives:

- model labels from the compared model values;
- the covered protocol labels from the supplied finite family;
- the verdict from the checked result constructor;
- for separation, the actual witness protocol, setting and outcome;
- exact rational probabilities from the checked backend;
- the exact oriented probability gap;
- the ordinary audited Claim that remains authoritative for the theorem.

Reverse-oriented separators preserve the order actually proved. If the checker
finds that model B exceeds model A, the report displays B first and computes
B minus A. It does not silently keep the caller's original order.

The public automatic comparison example exports both the ordinary Claim and this
structured view. The HTML renderer presents a short physical summary first and
keeps the formal proposition and logical-axiom audit immediately below it.

## Scope

Labels explain checked objects; they are not additional physical assumptions.
The theorem is still the embedded proof-bearing Claim.

Agreement wording remains deliberately scoped to the supplied, completely
covered finite family. A structured report never upgrades that result to
agreement over experiments that were not represented.

This reporting layer is also deliberately distinct from future continuous
robustness theorems. A finite comparison says what was checked over a supplied
finite family. A symbolic threshold will need a separate claim saying what is
proved for every parameter in a region.
