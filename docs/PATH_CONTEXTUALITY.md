# A finite path-projector contextuality test

This development specializes the finite-pointer theorem of
[Kunjwal, Lostaglio and Pusey (2019), Theorem 3 / Appendix B](https://arxiv.org/abs/1812.06940v2).
It is formal verification of established physics, with an exact finite-strength
example. No measurements or apparatus calibrations are supplied here.

## Bound and the model it excludes

A model has a setting-independent distribution μ(λ), a normalized probe kernel
K(m,λ′|λ), and stochastic final response r(f|λ′). The negative pointer event is
m=false; final success is f=true. The two relevant measured probabilities are

- a = P(m=false,f=true | probe), a joint probability per eligible trial;
- f = P(success | bypass), measured with the same preparation and final readout.

Measurement noncontextuality applied to a noisy binary measurement equivalence
implies Σλ′ K(false,λ′|λ) ≤ q, with q=(1+p_m)/2. Transformation
noncontextuality, convex mixing and the identity's diagonal representation imply
Σm K(m,λ′|λ)=(1-d)δλ′λ+dD(λ′|λ), where D is a stochastic kernel.
`Model.bound` proves a ≤ q f + d(1−f). `Model.full_bound` also includes a≤q.
No deterministic path or sharp final response is required. Consequently the
exclusion covers the definite-occupancy subclass as well as stochastic responses.

Alongside these two representation premises, the model assumes the same preparation
μ in probe and bypass runs and the same final response r after the probe and in
the bypass. These shared-procedure premises are enforced by the model type.
Setting-dependent preparation is illustrated only in the Python companion.

These representation premises are explicit inputs. Operational equivalence is
an equality of observed procedure probabilities across all allowed tests;
noncontextuality identifies their representations. Neither concept is a synonym
for small residuals in a finite calibration dataset.

The proof holds at every finite ontic cardinality and does not enumerate vertices.
No finite-cardinality completeness theorem for arbitrary measurable ontologies is
claimed. The standard integral argument in the cited paper covers its measurable
models; the present Lean theorem has the finite scope in its type.

## Exact instrument and all its outcomes

In path basis (Q,P), use K₋=diag(4/5,3/5), K₊=diag(3/5,4/5), preparation
|ψ⟩=(4,3)/5 and success vector |φ⟩=(4,−3)/5. The orthogonal failure vector is
(3,4)/5. `kraus_complete` proves normalization. `effect_equivalence` proves the
measurement equivalence with p_m=7/25. `channel_equivalence` proves the full
matrix identity M(X)=49X/50+ZXZ/50 for every complex X; `referenceD` is 1/50.
`reference_cap` derives 16/25 from `referencePm` = 7/25 through
`cap_of_measurement_equivalence`. `quantum_exclusion_of_representations` uses
this bridge and the disturbance representation at `referenceD`. The operator
identities motivate these representations; noncontextuality and convex mixing
remain additional ontological premises.

The complete POVM `jointReadout` is constructed by pulling each final effect
back through its Kraus branch. `quantum_realizes_table` identifies its complex
Born probabilities with this normalized table:

| Pointer | Success | Failure |
|---|---:|---:|
| Negative | 1369/15625 | 7056/15625 |
| Positive | 144/15625 | 7056/15625 |

`bypass_probability` gives f=49/625. `exact_gap` gives a−qf−d(1−f)=297/15625>0.
`quantum_exclusion` excludes every finite model satisfying both representation
premises and matching the joint and bypass probabilities. This is an actual
instrument construction, not an arbitrary table or a first-order expansion.

The normalized one-state `nullModel` has a fair pointer, zero disturbance and
stochastic final success 1/4. Its joint negative-success probability is 1/8.
Thus the null is nonempty and stochastic final readout is supported.

## Calibration and physical scope

The conditional design requires a heralded two-mode input, an ancilla coupling
realizing the stated Kraus operators, access to both final outputs, a bypass,
and a randomized identity/Z control. Measurement calibration uses four qubit
preparations spanning the Hermitian operator space; channel calibration also
uses X/Y/Z readouts. A finite tomography claim assumes the two-mode operational
space is complete and that preparations/readouts are characterized. Additional
modes, drift and unrecorded trials invalidate that inference unless bounded.

`Model.robust_bound` propagates explicit probability discrepancies from a model
satisfying the premises: a ≤ q f+d(1−f)+ε_a+|q−d|ε_f. It does not turn measured
operational discrepancies into ontic error bounds. Exact equivalences or an
additional defended model premise remain necessary. `ceiling_mono` and
`Model.full_bound_of_upper` justify replacing q and d by upper confidence bounds
when 0≤f≤1. The empirical companion specifies loss, confidence coverage and calibration cost separately.

Relative to [#85's local-phase model](PHASE_INTERVENTION.md), this tests a different
conjunction: measurement/transformation noncontextual representations of specified
procedures, rather than occupation matching and invariant empty-arm response.
The phase fringe alone does not supply these controls. Contextual or invasive
trajectory models remain possible; there is no velocity, relativistic causality,
or negative chronological-time inference.

## Verification

Source: `PathContextuality.lean`, `PathContextualityQuantum.lean`,
`PathContextualityCountermodels.lean`; regressions:
`Tests/PathContextuality.lean`; report: `examples/PathContextualityStudy.lean`.
All constructors and theorem roots are registered in `Tests/Audit.lean`.
Run `sh scripts/check.sh`; generated reports and the complete axiom snapshot
must match the verified head. The companion study is
[path-contextuality](https://github.com/stevenwarejones/path-reality-tests/pull/5).

## Complete countermodels

`invasiveModel` resets a fair hidden bit to a fair pointer; its final marginal is
unchanged, but the joint negative-success rate is 1/2 instead of the d=0 ceiling
1/4. `unchanged_marginal_not_zero_disturbance` proves that its actual transition
cannot satisfy the zero-disturbance premise. `contextualPointer` leaves the bit
unchanged and reveals it as the pointer; the observed pointer is fair but the
pointwise cap fails. `countermodels_same_joint` proves equality of their entire
joint tables. These illustrate different omitted premises, not complete rivals
for the quantum tomographic calibration family.

The reduced null is also inhabited at the reference q=16/25, d=1/50 and
bypass probability 49/625: `reference_null_nonempty` supplies a fair probe,
identity transition and stochastic final response. Its joint probability is
49/1250. Thus the violating example is not exploiting incompatible calibration
parameters in the reduced ontic class. This one-state example is not claimed
to reproduce the complete quantum calibration family.

`drop_cap_realizes_quantum` and `drop_disturbance_realizes_quantum` each match
the entire reference quantum joint table and bypass probability 49/625. The
first retains disturbance 1/50 but violates the response cap; the second retains
the cap 16/25 but violates disturbance 1/50. Thus each representation premise
is needed at these reference data. These reduced-interface models are not
claimed to match every quantum tomographic calibration procedure.
