# White-noise LC4 forced signaling

This study asks an experiment-facing version of the exact LC4 question: if the
prepared state has visibility (p) against white noise, how much operational
signaling must a finite stochastic conditional-local explanation have in the
repository's blind-pair model class?

The target state is

[
\rho_p = p\,|LC_4\rangle\!\langle LC_4| + (1-p)\,I/16.
]

For (0 \le p \le 1), Lean proves the exact forced-signaling curve

[
\Sigma(p)
  = \max\!\left\{0,\frac{p(4+2\sqrt2)-6}{8}\right\}.
]

This is not a numerical fit. The lower bound is the already-certified
measured-signaling inequality. Attainment is proved with explicit physical
response models: an exact zero-signaling model at the visibility threshold, an
exact rational white-noise model at (p=0), the exact LC4 model at (p=1),
and convex interpolation between those checked endpoints.

The same exact curve is also stated for the finite stochastic
conditional-local class formalized in PR #77. The stochastic theorem follows
through the checked determinization and signaling-preservation bridge; it is not
a separate numerical assumption.

## Visibility threshold

The onset is

[
p_* = \frac{6}{4+2\sqrt2}
    = 3-\frac{3\sqrt2}{2}
    \approx 0.8786796564.
]

This is the familiar (S_4) white-noise visibility threshold, not a newly
discovered threshold. The new content here is the exact amount of signaling
required *above* that threshold.

At or below (p_*), the noisy no-blind-pair marginals admit a zero-signaling
conditionally-local model. Above (p_*), the exact minimum rises linearly.

Two laboratory-relevant examples are checked symbolically:

| Visibility | Exact forced signaling | Approx. |
|---:|---:|---:|
| 0.90 | ((9\sqrt2-12)/40) | 0.0181981 |
| 0.95 | ((19\sqrt2-22)/80) | 0.0608757 |
| 1.00 | ((\sqrt2-1)/4) | 0.1035534 |

These values are expectation-level model-class minima. They are **not**
finite-sample confidence bounds, apparatus-calibration guarantees, or a
complete experimental rejection analysis. A laboratory analysis must still
combine a lower confidence bound on the completed (S_4) witness with a
simultaneous upper confidence bound on operational signaling.

## Checked proof chain

- `NoisyLC4.noisyABD` / `noisyACD`: exact white-noise marginal family.
- `NoisyLC4.Threshold.model`: exact `Q(sqrt 2)` zero-signaling model at
  (p_*), with all marginal equalities and signed signaling differences
  rechecked by the Lean kernel.
- `NoisyLC4.White.model`: exact rational zero-signaling model at (p=0).
- `NoisyLC4.matches_score`: every matching deterministic model has completed
  score (p(4+2\sqrt2)).
- `NoisyLC4.lower_bound`: universal signaling lower bound.
- `NoisyLC4.exact_curve`: lower bound plus an explicit attaining model for
  every (p\in[0,1]).
- `NoisyLC4.exact_curve_stochastic`: the same exact curve for arbitrary finite
  stochastic conditional-local hidden-state models, with an explicit attaining
  stochastic representative.
- `sigma_ninety_percent` and `sigma_ninetyfive_percent`: exact values at the
  two visibilities used in the source paper's event-budget discussion.

The floating-point LP was used only to discover sparse endpoint supports. It is
not a proof rule. The committed endpoint data are checked exactly in Lean.

## Scope

The theorem inherits the forced-signaling model assumptions: finite stochastic
conditional-local hidden variables, the stated measurement-independence and
no-postselection setting, and the LC4 measurement family. Standard finite
convex-hull reasoning extends the observable finite behavior class beyond
finite hidden-support presentations, but that measure-theoretic extension is
not formalized here. Whether this model class is the correct physical
description of all finite-speed mechanisms remains an interpretive question
for expert review.
