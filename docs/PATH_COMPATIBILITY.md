# Complete-table compatibility boundaries

This extension of the path-contextuality model asks how far its explicitly
specified representation assumptions must be relaxed to fit the entire reference
table, rather than only the negative-success witness.

For negative success a, positive success b, and bypass f, every finite model has

- negative marginal ≤ q;
- a+b ≤ f+d(1−f);
- a ≤ qf+d(1−f);
- b ≥ (1−d−q)f.

The last inequality follows from the probe's diagonal mass: at least 1−d stays
at the same state, and at most q occupies the negative branch. Shared preparation
and final response remain essential. No deterministic final response is assumed.

At the reference table, the proposed sharp boundary for 337/625 ≤ q ≤ 1 is

d_min(q) = max(1/50, (1369/15625−q·49/625)/(576/625), 1−q−144/1225).

The necessary inequalities are encoded in `PathCompatibility.lean`; construction
and certification of the full attaining family are in progress. Do not interpret
an incomplete draft as a Lean-certified iff theorem. The empirical companion
independently verifies candidate two-state models using exact fractions.

This is a reduced-interface compatibility result. It does not establish that the
models reproduce the full quantum tomography family, convert calibration residuals
into ontological distances, or resolve trajectory interpretations. Literature
novelty is not claimed.
