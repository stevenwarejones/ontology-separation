# What does a controlled phase change rule out?

A four-phase intervention distinguishes a specified dephased model from coherent
quantum propagation when the chosen detector sees a nonzero interference term.
It does not distinguish a path-sum formulation from an equivalent transfer
calculation, or exclude every theory assigning definite trajectories.

This extends the [two-path case study](PATH_INTERFERENCE_CASE_STUDY.md) to arbitrary
finite mixed states, orthogonal region projectors and complete POVMs. The
[checked report](../examples/phase-intervention.html) exposes the theorem statements.
No published measurements are inputs to these proofs.

## The physical model and its observable signature

Fix a density matrix ρ, an orthogonal projector P, Q=I−P, and a complete readout
with effects Eₒ. Propagation after the intervention can be included in the fixed
readout. The four unitary interventions are Vθ=Q+e^{iθ}P at θ=0, π/2, π, 3π/2.
Preparation, the region and the readout are the same at every setting.

The module constructs normalized quantum probabilities and proves, from the
matrix Born rule,

\[
p_\theta(o)=A_o+2\operatorname{Re}(e^{i\theta}c_o),\qquad
A_o=\operatorname{Tr}[(Q\rho Q+P\rho P)E_o],\quad
c_o=\operatorname{Tr}[P\rho Q E_o].
\]

Consequently p₀−pπ=4 Re(cₒ) and pπ/₂−p₃π/₂=−4 Im(cₒ). The sign follows the stated
phase convention. Two opposite phases alone can miss purely imaginary coherence.
All four predictions agree with the dephased state D(ρ)=PρP+QρQ exactly when every
*measured* cₒ vanishes. That is a statement about this readout, not state tomography:
a coordinate detector can miss coherence even when ρ≠D(ρ).

D(ρ) is proved positive and normalized, and invariant under every Vθ. Averaging
the probabilities at phases 0 and π gives the direct readout probability on D(ρ).
Thus the dephased-access procedure has a physical interpretation, rather than
being an arbitrary replacement table.

## Which classes are excluded?

`PhaseBlind p` means that the complete observed distribution is independent of
phase. The quantum P/Q-dephased class has this property. A definite-region model
is guaranteed to be phase-blind under fixed preparation and readout only when
the phase element has no response-relevant effect even on particles that traverse
it, as well as no effect on particles in the other region. Models in which the
element acts on traversing particles are not excluded by that premise; the
local-phase class below allows them. Particular mixtures can also be phase-blind
by cancellation despite phase-sensitive hidden responses, so observed blindness
alone does not establish microscopic inertness. In an ordinary Mach–Zehnder
interferometer, rejecting the dephased class is the expected outcome: it confirms
coherence, not a claim about trajectories.

Fixed preparation mixtures and fixed stochastic outcome processing preserve
phase blindness, including fixed losses when failure outcomes are retained.

`NearBlind p δ` allows one common phase-blind behavior q with
|pθ(o)−q(o)|≤δ at every setting/outcome. The module proves

\[
|p_s(o)-p_t(o)|\leq2\delta.
\]

If estimates satisfy a justified simultaneous bound |p̂θ(o)−pθ(o)|≤r, the null
implies |p̂s(o)−p̂t(o)|≤2δ+2r. A strict violation excludes the entire declared
`NearBlind` class. The confidence statement supplying r is an external premise;
there is no formal Hoeffding theorem or experimental p-value in this development.

The pairwise test is sound but conservative in general: it forgets that q is
normalized. For the four three-outcome distributions (1,0,0), (0,1,0), (0,0,1)
and (1/3,1/3,1/3), every pairwise entry difference is at most 1. The pairwise
condition passes at δ=1/2+ε for 0≤ε<1/6, but each q entry is at least 1−δ,
forcing δ≥2/3. The latter threshold is attained by uniform q. The module proves
this counterexample and the exact finite feasibility formulation: choose
nonnegative qₒ with sum one in every interval
[maxₛ pₛ(o)−δ, minₛ pₛ(o)+δ]. With two outcomes the pairwise criterion is exact:
the midpoint of the maximum and minimum probabilities for one outcome has a
normalized complementary entry. The four-setting arithmetic average is not
generally the minimax center; it is one for the symmetric lossy family below.

The threshold is sharp for an explicit lossy two-mode family:

\[
p_\theta(+)=\eta(1+v f_\theta)/2,\quad
p_\theta(-)=\eta(1-v f_\theta)/2,\quad
p_\theta(\varnothing)=1-\eta,
\qquad f=(1,0,-1,0),\quad 0\leq\eta,v\leq1.
\]

The family belongs to `NearBlind δ` **if and only if ηv≤2δ** (δ≥0), including the
boundary. Lean also constructs its density matrix and complete inefficient POVM
and proves that their Born probabilities equal this table. This is a physical
quantum realization of the threshold, not only a normalized probability example.

## Definite region with a local phase element

`LocalPhaseModel` has a finite ontic space Λ, setting-independent preparation μ,
a region map r:Λ→{P,Q}, and normalized stochastic responses Rₛ(o|λ). Responses
for Q states are invariant across settings; P responses are arbitrary, including
loss. This is a response-level locality premise, stronger than spatial locality:
a phase-sensitive field in an otherwise empty arm can propagate locally to the
recombiner and change a Q particle's eventual response.

The occupation premise identifies μ(P)=w with the probability reported by a
which-region measurement on the same preparation. Then

\[
p_s(o)-p_t(o)=\sum_{\lambda\in P}\mu(\lambda)
[R_s(o|\lambda)-R_t(o|\lambda)],\qquad |p_s(o)-p_t(o)|\leq w.
\]

Every response difference is in [−1,1]; summing its preparation weights proves
the bound, including the failure outcome. The balanced `visibilityState` has
Tr(Pρ)=1/2. Its complete lossy quantum table has contrast ηv and is compatible
with the class **if and only if ηv≤1/2**. The η=1, v=3/5 example violates the
bound. At the boundary the null remains nonempty and admits interference.
A two-state construction reproduces every compatible table: with weights 1/2,
use P/Q responses (2η,v)/(0,0) when η≤1/2 and (1,2ηv)/(2η−1,0) otherwise,
where each pair denotes a `lossy` efficiency/visibility parameterization.

The three premise countermodels reproduce any target table. Dropping occupation
matching permits all weight in P. Dropping Q invariance permits both regions to
use the target lookup response with fixed equal weights. Dropping setting
independence permits μₛ(r,o)=pₛ(o)/2, fixed deterministic outcome responses and
occupation 1/2 at every setting. Each construction is normalized.

If each actual probability is within δ of a local model, estimates have
simultaneous radius r, and |μ(P)−ŵ|≤r_w, then

\[
|\hat p_s(o)-\hat p_t(o)|\leq \hat w+r_w+2\delta+2r.
\]

A strict violation excludes the calibrated conjunction. Confidence coverage and
experimental calibration remain external premises. With the phase element in
the other arm the separate bound is 1−w. The bound min(w,1−w) for a single
contrast additionally requires that the two placements implement the same
observable contrast and have complementary occupations; two unrelated fringes
do not justify taking their minimum.

A violation rejects definite region, occupation matching across measurement
contexts, Q-response invariance and setting independence **jointly**. It does not
identify which premise failed. The occupation equality is a noncontextuality-type
identification, not something proved by measuring a frequency. Context-dependent
occupation theories, Bohmian-style theories and empty-arm field models can survive.
The companion [empirical protocol](https://github.com/stevenwarejones/path-reality-tests/tree/study/audit-completion/studies/phase-intervention-design)
uses this bound as its occupation-calibrated target, with complete heralded
outcomes and simultaneous binomial intervals.

## Checked failure cases and access limits

- The state (3/5)|0⟩+(4i/5)|1⟩ has equal 0/π probabilities but a −24/25 contrast
  in the other quadrature under the specified plus/minus readout.
- The same coherent state is phase-blind under coordinate detection.
- At zero efficiency every trial fails; unit visibility alone provides no gap.
- A complete three-outcome table has constant selected-bin probability 1/4 but
  detection-conditioned fractions 1/2 and 1/4. Selected counts divided only by
  detections can therefore produce a contrast absent in herald-denominated counts.
  This example has setting-dependent other-bin/loss probabilities and is not
  claimed to belong to the full phase-blind class.
- An unrestricted stochastic response to the setting reproduces any table exactly.
  It is a lookup simulator without a trajectory law or noncontextuality constraints.
- Erasing the outcome destroys all distinctions. The `ExperimentAccess` comparison
  also proves agreement under dephased access, with full-access equivalence exactly
  characterized by the measured cross terms.

## Prior work and physical correspondence

The phase-unitary/POVM formulation is established physics
([Biswas, García Díaz and Winter, v3](https://arxiv.org/html/1701.05051v3)).
[Hardy, v3 (2012), Section 3](https://arxiv.org/html/1205.1439v3) gives a closely
related interferometer argument. His localized-preparation ontic indifference
is distinct from the Q-response premise here. The present contribution is
finite formal verification with occupation and robustness bounds; no priority
claim is made for the inequality.

[Dahlsten–Garner–Vedral, v2](https://arxiv.org/abs/1206.5702v2) define operational
branch locality for preparations certainly in one arm. That condition, which
quantum theory satisfies, does not identify Q-located hidden components of a
coherent preparation with operationally preparable Q states.

[Pusey, v2 (2014)](https://arxiv.org/html/1409.1535v2) and
[Kunjwal–Lostaglio–Pusey, v2 (2019)](https://arxiv.org/html/1812.06940v2) make
noncontextuality operational through measurement/transformation equivalences
and disturbance bounds. Occupation matching here is one cross-context premise;
it neither supplies their equivalences nor proves their contextuality theorems.
Their joint pointer/postselection statistics differ from this unconditional
phase-contrast statistic. The empirical study's literature comparison also
reviews modular variables, weak traces and explicit empty-arm countermodels.

Preparation stability, the regional map, complete trial outcomes, nuisance bounds
and statistical coverage require apparatus evidence. Spatial discretization adds
aperture and projection errors. No spacetime signaling or relativistic trajectory
test is established. The empirical work lives in
[path-reality-tests](https://github.com/stevenwarejones/path-reality-tests).

## Verification and source review

The development is in
[PhaseIntervention](../OntologySeparation/Experiments/PhaseIntervention.lean),
[PhaseInterventionModels](../OntologySeparation/Experiments/PhaseInterventionModels.lean)
[PhaseInterventionExamples](../OntologySeparation/Experiments/PhaseInterventionExamples.lean),
[PhaseInterventionGeometry](../OntologySeparation/Experiments/PhaseInterventionGeometry.lean)
and [LocalPhase](../OntologySeparation/Experiments/LocalPhase.lean).
[Tests](../Tests/PhaseIntervention.lean) exercise the missed quadrature,
phase-insensitive readout, restricted access, quantum realization and both sides
of the exact calibration boundary. The proof/constructor roots are registered in
`Tests/Audit.lean`; the only permitted axioms remain `propext`, `Classical.choice`
and `Quot.sound`. The repository verification command is `sh scripts/check.sh`.

Primary sources checked on 2026-09-26 UTC: Biswas et al. arXiv:1701.05051v3,
Hardy arXiv:1205.1439v3, Dahlsten–Garner–Vedral arXiv:1206.5702v2, Pusey arXiv:1409.1535v2 and
Kunjwal–Lostaglio–Pusey arXiv:1812.06940v2.
