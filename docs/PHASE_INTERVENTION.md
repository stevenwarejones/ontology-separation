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

`PhaseBlind p` requires the entire outcome distribution to be setting-independent.
Every dephased quantum model above belongs to this class. Finite preparation
mixtures with fixed weights and fixed stochastic outcome processing preserve it.
Any unequal pair of probabilities excludes any finite convex class whose
members satisfy that condition. This includes fixed losses when failure outcomes
are retained. The proof makes no claim that arbitrary trajectory theories are
phase-blind.

`NearBlind p δ` allows one common phase-blind behavior q with
|pθ(o)−q(o)|≤δ at every setting/outcome. The module proves

\[
|p_s(o)-p_t(o)|\leq2\delta.
\]

If estimates satisfy a justified simultaneous bound |p̂θ(o)−pθ(o)|≤r, the null
implies |p̂s(o)−p̂t(o)|≤2δ+2r. A strict violation excludes the entire declared
`NearBlind` class. The confidence statement supplying r is an external premise;
there is no formal Hoeffding theorem or experimental p-value in this development.

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

## Prior work and remaining physical obligations

The phase-unitary/POVM formulation is established interference physics; see
[Biswas, García Díaz and Winter (2017), Eqs. 1–4](https://arxiv.org/html/1701.05051v3).
This contribution is formal verification, an explicit model-class comparison,
and a sharp probability-budget calculation. No new interference mechanism is claimed.

[Pusey (2014)](https://doi.org/10.1103/PhysRevLett.113.200401) and
[Kunjwal–Lostaglio–Pusey (2019)](https://arxiv.org/html/1812.06940v2) motivate stronger
contextuality tests. Their operational-equivalence and disturbance premises are
additional obligations; a phase fringe alone does not satisfy them.

An experiment must justify preparation stability, its physical regional phase
map, complete trial outcomes, setting-dependent nuisance bounds and statistical
coverage. A spatial quadrature also needs aperture and discretization controls.
None is supplied by the formal model. There is no spacetime signaling test or
relativistic trajectory claim here. Empirical designs and the Wen data audit live
in [path-reality-tests](https://github.com/stevenwarejones/path-reality-tests).

## Verification and source review

The development is in
[PhaseIntervention](../OntologySeparation/Experiments/PhaseIntervention.lean),
[PhaseInterventionModels](../OntologySeparation/Experiments/PhaseInterventionModels.lean)
and [PhaseInterventionExamples](../OntologySeparation/Experiments/PhaseInterventionExamples.lean).
[Tests](../Tests/PhaseIntervention.lean) exercise the missed quadrature,
phase-insensitive readout, restricted access, quantum realization and both sides
of the exact calibration boundary. All 41 new proof/constructor roots are in
`Tests/Audit.lean`; the only permitted axioms remain `propext`, `Classical.choice`
and `Quot.sound`. Run the standard `sh scripts/check.sh` gate.

Primary-source review on 2026-09-26 UTC checked Biswas et al. v3's finite
phase-unitary/POVM formulation and Kunjwal et al. v2's Theorem 3 and Sections III.2/IV.
Searches included `phase cycling four step interferometry density matrix coherence
dephasing phase shift` and `coherence witness interferometer visibility dephasing
phase shift`. They identify known interference results, not exhaustive priority.
The staged apparatus/statistics review is recorded with the empirical study.
