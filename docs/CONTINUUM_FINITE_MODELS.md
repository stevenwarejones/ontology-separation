# Continuum dynamics versus finite models

**Development status: incomplete; not review-ready.** At 49c6daa the focused build, all 30 new audit roots, and the full
`scripts/check.sh` pass have been checked; the final CI gate identified only
uncommitted generated artifacts. The current branch adds further lattice and
statistical proofs, which require their own final-head verification. Both PRs
remain drafts. Existing verification gates are retained.

The question concerns complete observable probability distributions under common
preparation, evolution and measurement controls. A finite path sum equal to a
matrix product is one calculation in two forms. It is not a competing theory.

## Defined continuum benchmark and exact counterexample

`ContinuumSpectral` represents all square-summable complex sequences indexed by
Z, not a finite list of modes. It defines norm mass and real-frequency spectral
evolution. Proof terms establish preservation of mass and coefficient distance,
the group law and inverse. `Circle` fixes positive circumference, mass and hbar;
its frequencies are hbar*(2πj/L)²/(2m).

A finite support is an explicit restriction on this infinite space. On that
support, replacing every inaccessible frequency by zero preserves the evolved
state exactly, hence every outcome of every common normalized detector. This
is the exact restricted spectral counterexample. The `finiteEmbedding` constructor zero-extends a genuinely finite coefficient
vector. Its mass theorem identifies the infinite norm sum with the finite
norm sum, and `finiteEmbedding_intertwines` transports finite diagonal evolution
exactly. Normalized finite preparation and all common detector outcomes are
preserved. These results compiled at 49c6daa.
The position-space Fourier identification with L² of the circle is external.
The development does not yet bundle a Hilbert-space unitary or strong continuity.

`ContinuumSeparation` defines a complete plus/minus/failure probability table,
normalization, positivity, cosine contrast and a phase Lipschitz bound. It proves
zero-visibility/full-loss failures, absorption by an unconstrained reference,
and disjointness under calibrated probability perturbations. These are readout
lemmas: they do not yet connect the lattice generator to an actual Born POVM.
The arbitrary normalized `Detector` interface supports **exact equality only**.
It permits discontinuous responses and supplies no approximation guarantee.
Approximation requires a separate Born-rule interface.
`ContinuumApproximation` at 49c6daa proves a conservative local cosine remainder
5/96 for |ka|≤1, a frequency-error bound, scalar phase Lipschitzness and a
dimension-independent finite coefficient error. It does not certify the empirical
global 1/24 estimate.
The added `ContinuumStatistics` develops complete product-law TV and test-error
proofs; it remains to connect these to a Born detector and approximant family.

## Mathematical obligations before review readiness

| Obligation | Current disposition | Required result |
|---|---|---|
| Infinite spectral evolution | Compiled and audited at 49c6daa | Final-head audit/report refresh |
| Finite spectral counterexample | Finite embedding, mass, intertwining and complete detector equality compiled at 49c6daa | Final-head checks |
| Nearest-neighbor lattice | Cyclic character spectrum, normalization, orthogonality and strict alias exclusion added | Compile and connect physical constants |
| Cosine remainder | Local 5/96 frequency estimate compiled at 49c6daa | Global 1/24 is separate and not certified by this theorem |
| Approximation | Finite phase/vector estimate compiled at 49c6daa | Born TV conversion, normalized truncation and tau=1 case |
| Strong convergence | Not yet formalized | Fixed state, bounded time, explicit cutoff/site quantifiers |
| Finite-resource impossibility | Full product TV and randomized-test proofs added | Compile; connect to approximant family |
| Separating experiment | Probability-level lemmas written | Born realization, explicit dynamics/parameters, phase interval and nuisances |
| Trust/report | Roots registered; snapshots absent | Full check and exact generated-file equality on final head |

No acceptance item is closed merely because this table lists it. The remaining
analysis bridges are necessary dependencies of the intended approximation and
no-uniform-separation claims. They are not replaced by assumed error bounds.

The companion empirical study develops the mathematical derivations and
independent matrix/probability checks. It labels these as non-formalized and
supplies no experimental exclusion. No general exclusion of finite ontologies,
count of occupied trajectories, or construction of a real-time path measure is
claimed. Continuous-time lattices can have infinitely many histories; a finite
mode description can exactly summarize restricted continuum experiments.

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
