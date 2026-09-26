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

At the reference table, the sharp boundary for 337/625 ≤ q ≤ 1 is

d_min(q) = max(1/50, (1369/15625−q·49/625)/(576/625), 1−q−144/1225).

The necessary inequalities and the full attaining family are encoded in
`PathCompatibility.lean`, culminating in `reference_finite_compatible_iff`. Formal CI
is still pending; do not interpret the draft as a verified formal certificate.
The empirical companion independently verifies the models using exact fractions.

The algebraic helper `reference_phase_invariant` expresses the phase ambiguity of the local pointer
bilinear. `indistinguishable_error_sum` is the complementary-expectations identity. A
no-testing application separately requires a distribution shared by both hypothesis
classes; neither helper proves that physical premise.
These identities have separate physical premises in the empirical reconstruction.

Every public definition/theorem is registered in `Tests/Audit.lean`.
`examples/PathCompatibilityStudy.lean` exports the theorem report; run the full
`sh scripts/check.sh` and commit the regenerated audit and report before review
readiness.

This is a reduced-interface compatibility result. It does not establish that the
models reproduce the full quantum tomography family, convert calibration residuals
into ontological distances, or resolve trajectory interpretations. Literature
novelty is not claimed.

At q=16/25, the positive-success cell is a second witness, with disturbance
threshold 297/1225 rather than 13/320 from the negative-success inequality.
At d=1/50, however, its gap is 109/6250 (0.01744), below the negative gap
297/15625 (0.019008); its observed cell is rare (144/15625). This establishes
improved tolerance to disturbance, not improved statistical power. The empirical
companion tests both witnesses with simultaneous confidence coverage.

The positive floor is an elementary consequence of the same cap and disturbance
premises. We make no novelty claim. KLP (2019), published Theorem 3 and Appendix B,
provide the finite-pointer upper witness and discuss tightness; their published
technical template is Lemma 1 (numbering differs from the arXiv version).
