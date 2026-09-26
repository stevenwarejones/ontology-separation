# Recommended follow-up: phase intervention with explicit loss

Status: proposed experiment and analytical design; no data collected, apparatus feasibility not yet established, and no new contextuality theorem claimed. This closes the design portion of work package 3 while its empirical replication remains blocked. It provides a concrete handoff to package 2.

## Question, model classes and predicted contrast

Can a controlled intervention at an intermediate plane distinguish coherent propagation from a specified model that has lost coherence between a region R and its complement? Choose the region and output bin on training data, then freeze them before confirmation. Use P for the region projector and Q=I−P. For state ρ at that plane, a phase intervention is Vθ=Q+exp(iθ)P. Include downstream propagation and calibrated detection in a fixed effect 0≤E≤I.

Define A=Tr(EQρQ)+Tr(EPρP) and c=Tr(EPρQ). Direct expansion gives

\[
p_\theta=A+2\operatorname{Re}(e^{i\theta}c),\qquad
p_0-p_\pi=4\operatorname{Re}c,\qquad
p_{\pi/2}-p_{3\pi/2}=-4\operatorname{Im}c.
\]

The dephased model D(ρ)=PρP+QρQ predicts the constant A under this same phase intervention. The null includes mixtures of such states with setting-independent preparation, downstream effects and loss. A broader model allowing setting-dependent preparation, efficiency or response need not obey the constant prediction. Calibration and randomization therefore belong to the model test, not optional laboratory housekeeping.

For a pure input and a rank-one output, c reduces to a* b with a and b the complementary-region and selected-region transition amplitudes. No separate record of which region the individual photon occupied is assumed. Path-sum and transfer-matrix quantum descriptions predict exactly the same curve. A nonzero contrast rejects the stated dephased class; it does not select an ontology of literal paths. Zero contrast does not establish dephasing: c can vanish for a coherent state and an unsuitable detector.

## Acquisition and controls

1. Characterize the source, preparation, selected region and detection effect. Establish whether a phase-only intervention can be implemented at the desired intermediate plane without changing apertures, mode coupling or polarization unintentionally. Use the finite-window obligations in `physical-bridge.md` to define the forward model.
2. Use independent training/calibration data to select R and an output bin with predicted contrast. Freeze geometry, model parameters, binning, nuisance allowance, sample size and analysis before confirmation. Do not fit the confirmation fringe and call that same fit an independent prediction.
3. Randomize the four phase settings 0, π/2, π and 3π/2 across trials or short balanced blocks. Log the actual phase, timestamp, acquisition order and calibration state. Wait for modulator settling according to a declared rule, independent of detector result.
4. Define a trial with a source herald independent of the later detection outcome and setting. Count each trial in a complete outcome space: selected bin, other detected outcomes, no detection, and multiple detections with a preregistered assignment. Use the selected-bin count divided by all eligible heralds. Archive integer counts, including failures; do not normalize each setting by its detected subset.
5. Interleave source-off backgrounds, detector calibration and a deliberately randomized phase control. Averaging independent uniform phases implements the P/Q dephasing map ideally. Verify its implementation and loss; a physical blocker changes boundary conditions and is not automatically an equivalent control.
6. Bound setting-dependent transmission, preparation drift, phase error, detector response and uncertainty in the projection/effect description. If they cannot be bounded, report an unresolved model bridge rather than an exclusion. A successful control does not by itself prove there are no unmeasured degrees of freedom.

## Finite-data decision rule

For n independent Bernoulli trials per setting with fixed setting probabilities, let p̂θ be the selected-bin fraction. With family error α, the union bound and Hoeffding inequality give simultaneous radii

\[
r=\sqrt{\log(8/\alpha)/(2n)}.
\]

Let B be a justified upper bound on the absolute contrast that the calibrated null could produce through setting dependence. Reject this null only if

\[
\max(|\hat p_0-\hat p_\pi|,|\hat p_{\pi/2}-\hat p_{3\pi/2}|)-2r>B.
\]

If each setting differs from a common null probability by at most δcal, B=2δcal suffices. If calibration is statistical with failure probability αcal, allocate it separately; total error is at most α+αcal. Do not subtract backgrounds into non-Bernoulli pseudo-counts and then apply this rule. Model backgrounds and multiphoton contamination in the outcome probabilities/nuisance bound. No optional stopping is permitted with this fixed-sample calculation. Dependence or appreciable drift requires a justified sequential or block analysis before claiming this error rate.

With α=0.01 and n=10,000 per phase, 2r≈0.03656. To target a contrast uncertainty at most h, choose n≥ceil(2 log(8/α)/h²); this sets precision, not detection power. Power must be computed from an independently justified anticipated contrast and nuisance margin. Testing extra regions/bins requires its own multiplicity allocation or independent holdout selection.

`intervention_checks.py` verifies the complex phase/sign convention against direct density-matrix calculations, full outcome normalization with loss, the constant dephased prediction, and the intermediate-window counterexample. Its numbers are synthetic. The existing Lean certificate covers the balanced two-route/two-phase special case; it does not certify this generalized apparatus bridge or statistical rule.

## Prior work and package-2 handoff

This is an established interference mechanism, not a claim to invent single-photon interference. Its value here is an intervention tied to explicit models, failure outcomes and a checked audit trail. [Lundeen et al. (2011)](https://doi.org/10.1038/nature10120) illustrates the model and ensemble dependence of direct optical inference; [Matzkin (2020)](https://doi.org/10.1103/PhysRevResearch.2.032048) relates weak probes to path amplitudes. [Magaña-Loaiza et al. (2016)](https://doi.org/10.1038/ncomms13987) shows why modifying apertures requires care about changed boundary conditions. See `literature-comparison.md` for review depth and limits.

For stronger ontology exclusion, package 2 should assess the finite-pointer Theorem 3 in [Kunjwal, Lostaglio and Pusey (2019)](https://arxiv.org/html/1812.06940v2): p−≤pF(1+pm)/2+(1−pF)pd. Here p− is the joint pointer-negative/postselection-success probability, not the postselected fraction. Applicability requires the measurement and transformation equivalences in Eqs.29–30; polarization data alone do not establish them. Section IV explains secondary procedures and a remaining tomography assumption. First derive the exact instrument map and finite-data calibration requirements; only then implement a witness. This is a separate stronger objective, not a result of the phase-contrast test.

## Completion and literature gates

Before committing resources, refresh primary literature on regional phase interventions, reconstructed propagators, lossy contextuality experiments and the chosen apparatus; record the closest protocol and whether this proposal adds any experimental novelty. Before locking analysis, search for applicable finite-data treatments of approximate operational equivalences and setting-dependent loss. After pilot results, seek adverse explanations using the measured instrument model. Before final claims, refresh corrections and compare every claim with its supporting data/proof.

Unresolved obligations have named entries Q21–Q24 in the question register. A failed feasibility or calibration check must produce an explicit negative result or revised model, not disappear from the report. New questions receive evidence, next action and closure conditions. Exhausting accessible evidence is a documented external dependency, not permission to invent a resolution. Do not contact researchers without user authorization.
