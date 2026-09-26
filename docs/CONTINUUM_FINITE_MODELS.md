# Continuum dynamics versus finite models

**Draft: final combined verification and generated artifacts are in progress.**
The infinite spectral evolution, exact finite embedding, cyclic spectrum,
product-TV, Born continuity, global cosine remainder and normalized truncation
modules have compiled in CI. New composition and witness additions require
verification at the final head. This document distinguishes those checks from
mathematical claims; the draft is not a merge recommendation.

## Common models and accessible experiments

The continuum state space is all square-summable complex Fourier coefficients
indexed by the integers, represented by `SpectralVector` and identified explicitly
with the Hilbert space `lp (fun _ : ℤ => ℂ) 2`. A circle has positive circumference
L, mass m and hbar. The frequencies E/hbar are hbar*(2πj/L)²/(2m).
Spectral evolution multiplies each coefficient by exp(−itE/hbar). The group law,
inverse, norm preservation and distance preservation are proved.

| Finite object | Interpretation |
|---|---|
| Terms in a finite path sum | Same amplitude as the corresponding matrix product |
| Time slices with continuous integrations | Infinitely many intermediate positions remain |
| Sites on an N-site ring | Specified periodic nearest-neighbor dynamics; continuous time |
| Accessible Fourier modes | A finite spectral model can match the continuum exactly |
| Detector outcomes | Finite readout does not imply finite microscopic trajectories |
| Ontic states or occupied paths | A separate ontology claim, not inferred by a dispersion test |

The common interface fixes preparation, mode labels, time, phase reference and
complete measurement outcomes. A finite preparation is zero-extended into the
infinite space. `finiteEmbedding_intertwines` proves exact transport of finite
spectral evolution. The spectral finite model agrees exactly on every accessible
mode and therefore on every shared detector outcome. Its position couplings need
not be nearest-neighbor. Thus finite dimensionality alone is not excluded.

## Cyclic dynamics, approximation and finite resources

`FiniteDispersion` defines the actual directed periodic shifts on Z/NZ, including
N=1,2, and derives the character eigenvalue 2−chi(j)−chi(−j). Converting characters
to phases gives 2(1−cos(2πj/N)). Fourier columns are normalized and orthogonal.
The strict condition N>2J excludes aliases for all integer modes |j|≤J.
`FiniteFourier` constructs normalized Fourier synthesis, norm preservation and
intertwining with the cyclic operator. `bandSynthesis` explicitly maps the
alias-free retained integer modes to N-site states, preserves their mass, and
transports the same lattice frequencies used in the approximation theorem.
`cyclicKinetic_spectrum` supplies physical
units: E_a=hbar²(1−cos(ka))/(m a²), with a=L/N.

The older local 5/96 estimate remains available under |ka|≤1. A separate
`cosine_remainder_global` proves

    0 ≤ x²/2 − (1−cos x) ≤ x⁴/24

for every real x, using derivative monotonicity. `frequency_error_global` and
`frequency_error_band` give the global coefficient used by the companion study.
For |k|≤K and |t|≤T the retained-band norm error is bounded by
T*hbar*a²*K⁴/(24m). No computational time step enters this result.

`projection` is an actual finite Hilbert projection. `tail_sum` identifies its
squared distance with the discarded probability. `normalizedProjection` has unit
norm when retained mass is nonzero; `zero_retained_iff_tail_one` handles the
excluded endpoint exactly. The proved conservative norm bound is 2*sqrt(tau).
This is not the sharper pure-state trace-distance sqrt(tau) derivation in the
numerical guide. The composed bound therefore uses **2*sqrt(tau)+epsilon**.
Normalized projections converge strongly for each fixed infinite state.

`BornInstrument` consists of bounded complex-linear Kraus operators with
completeness sum_o ||K_o u||²=||u||². Probabilities are ||K_o u||². Their
TV continuity is derived from this structure, not assumed. The arbitrary
normalized `Detector` remains restricted to exact-equality results.
`born_tv` proves TV≤||u−v||. `ContinuumStatistics` proves the complete product-law
bound TV(p^n,q^n)≤min(1,n TV(p,q)) and every randomized test's error bound
alpha+beta≥1−TV, with TV=half L1.

`lattice_strong_convergence` chooses a finite cutoff and site threshold for a
fixed normalized state, bounded times and any positive norm tolerance. Every
larger N excludes aliases and meets the tolerance. `finite_resource_nonseparation`
and `finite_resource_test_error` compose this with actual Born joint data at any
fixed finite trial count. The cutoff may depend on the state and requested
precision. This is not unrestricted operator-norm convergence and does not say
that a fixed finite lattice is forever untestable.

## A separating fixed alternative

`ContinuumWitness` constructs the balanced recombiner as explicit complex
matrices and proves Kraus completeness. Diagonal two-mode evolution produces a
relative phase −t*(w1−w0); the Born probability after the common reference q is
(1+cos(q−t*(w1−w0)))/2. Loss and symmetric visibility randomization give the
complete plus/minus/failure table used by the numerical protocol.

For L=2π, m=hbar=1, modes 0 and 1 and N=4, the frequencies are 1/2 and 4/π².
Their positive gap is d=1/2−4/π². At t=π/d with reference q=t/2 the continuum
plus probability is 1 and the lattice plus probability is 0. These explicit
controls separate this fixed nearest-neighbor alternative. Symmetric modes
−j,j have no relative energy signal. General phases can wrap into blind spots;
there is no monotonic exclusion claim.

The noisy readout is physically calibrated. `free_reference_born_equivalence`
shows equality of the entire outcome table if a separate unconstrained reference
can be refitted. Full loss and zero visibility are other exact failures.
`robust_coordinate_separation` gives the sufficient probability-interval criterion
used in the companion fixed-allocation design. Its shared-scale interval test
exploits several momenta while preserving one scale across settings.

## Evidence and limits

All new trust roots are registered in `Tests/Audit.lean`; the report source
exports the approximation, joint-law and witness chain. The committed generated
audit/report must be refreshed from a successful combined build before readiness.
The companion [numerical study](https://github.com/stevenwarejones/path-reality-tests/pull/9)
contains independent cyclic matrix, Born-rule, tail, joint-law and count-decision
tests, 660 baseline scenarios, and a shared-scale sensitivity comparison.
Numerical corroboration is distinct from Lean checking and experimental evidence.

The Fourier identification with position-space L² on the circle is external.
The benchmark is a nonrelativistic free massive particle, not photon dynamics.
The repeated-data theorem covers independent fixed allocations, not adaptive
controls, correlated trials, ancillas or optional stopping. No compatible dataset
currently supplies the apparatus and calibration certificates for an exclusion.
No general exclusion of finite ontologies, count of occupied trajectories, or
construction of a real-time path measure is claimed.

## Closest primary sources

- Guth, MIT 8.323 notes (2008), Eqs. 5.3–5.10: finite time slicing retains continuous
  position integrations and real-time oscillatory kernels.
  https://web.mit.edu/8.323/spring08/notes/ft1ln05-08-2up.pdf
- Tarasov, *Physics Letters A* 380 (2016), 68–75: standard nearest-neighbor
  discretization versus long-range exact discretization. His infinite lattice
  is not the finite accessible-mode counterexample here.
  https://theory.sinp.msu.ru/~tarasov/PDF/PLA2016.pdf
- Brun–Mlodinow, arXiv:1802.03911v1, Eqs. 17–23, published PRD 99, 015012
  (2019): dispersion-sensitive interference in a different, anisotropic Dirac
  quantum-walk model. Its sensitivity estimates do not transfer to this ring.
  https://arxiv.org/html/1802.03911v1
- Watrous, author pre-publication text (2018), Theorem 3.4 / Proposition 3.5:
  state discrimination and measurement norm bounds, with trace distance defined
  as one half the trace norm. This project seeks formal verification and
  calibrated access bounds, not novelty in these mathematical facts.
  https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf

Sources inspected 2026-09-26 UTC. Trotter's product theorem is not used as a
substitute for spatial convergence. Exact diagonal evolution requires no
computational time step. Euclidean positive measures and real-time oscillatory
integrals are different constructions and remain outside this benchmark.
