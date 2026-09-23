# Which flagship should we build?

Decision spike, 22 September 2026. **Proceed with a staged certificate-to-physics
unification effort; do not yet promise a common physical theorem.** The first
external rational certificate is tractable in Lean. The larger operator proofs
have identifiable proof obligations, but have not been ported. Minimax remains
a possible research direction, not an automatic consequence of the four bounds.

For a physicist: the useful question is whether the same *reason* forces these
tradeoffs, not whether their formulas can be made to look alike. This increment
checks one actual external certificate and records what would have to be proved
to establish a shared reason.

## Follow-up implementation

The [signaling guide](../SIGNALING_GUIDE.md) now documents the physical
response-model → LP bridge and an attaining model for every nonnegative budget.
It proves fixed-completion sharpness in the stated finite response class. The
certificate-only findings below remain the historical scope of this spike;
cluster-state marginal matching and the broader unification remain open.

## Exact sources and stack

These pins, rather than repository names or current default branches, identify
what was inspected. No open PRs were returned for the three external repositories
at inspection time. Their README claims are not treated as Lean proofs.

| Source | Pinned commit | Role |
|---|---|---|
| [ontology-separation main](https://github.com/stevenwarejones/ontology-separation/tree/8283b1a599bdc6a3c6145d49ec6e846ab38a616f) | `8283b1a599bdc6a3c6145d49ec6e846ab38a616f` | Main after merged #27; this PR branches directly from it |
| [LF readout, #29](https://github.com/stevenwarejones/ontology-separation/tree/cdf577c0a53b64ac83bb22321873de635fdf66bb) | `cdf577c0a53b64ac83bb22321873de635fdf66bb` | Implemented open branch, depends on #28 |
| [forced-signaling](https://github.com/stevenwarejones/forced-signaling/tree/bae83b865ea60b1fbc4b808e66dc9bbaf7da2d4b) | `bae83b865ea60b1fbc4b808e66dc9bbaf7da2d4b` | Rational LP dual and algebraic primal/dual |
| [coherent-subsystem-recovery](https://github.com/stevenwarejones/coherent-subsystem-recovery/tree/66afe8f1ac5427de192134c627c863d6d8070f6c) | `66afe8f1ac5427de192134c627c863d6d8070f6c` | Free-unitary PSD certificate and recovery interpretation |
| [schmidt-number-witness](https://github.com/stevenwarejones/schmidt-number-witness/tree/f727a085f43d01ce3f544275675b72911d7b4917) | `f727a085f43d01ce3f544275675b72911d7b4917` | Partial-local geometry, qubit SOS, strengthened dimension witness |

#28 remains the paper-to-joint-event correspondence; #29 is its sharp total
readout-budget extension. #30 → #31 → #32 → #33 remains an independent stack:
physical environment → discrimination → prospective fixed-block statistics →
partial-environment benchmark and literature audit. This spike does not duplicate,
rebase, or require their code. In particular, #33 is a known-phase benchmark,
not the promised restricted-access minimax flagship. Check live PR state before
integrating any follow-up; these are inspection-time descriptions.

## Reconciliation: four different physical objects

| Result | Physical class and score | Resource or penalty | What is sharp / what is not |
|---|---|---|---|
| LF readout | Joint-event tables with local conditional responses and setting-independent record weights; genuine LF score S | Actual total record/readout disagreement t = δA+δB | S ≤ 6+4t; #29 has matching tables for t∈[0,1]. Their quantum attainability is not asserted. |
| Forced signaling | Conditional-local hidden-response weights in a four-party blind-pair setting; a **specified completion** of S₄ | Δ is maximum recipient total variation over setting changes, not record error | S₄ ≤ 6+8Δ. Source claims slope optimality and a separate marginal-matching optimum (√2−1)/4. This Lean spike ports the upper LP certificate, not those two sharpness results. |
| Recovery | Three protected coherent branches I,U,V on addressed M; test decoder can use bypass B; target recovery acts on M alone | Test infidelity 1−f; target is optimal squared entanglement fidelity R | Source curve max{1/4,3f/4,(3f−1)/2}. The high-score line is 1−R ≤ (3/2)(1−f). Its existential decoder is not the same as a fixed forward-query circuit. |
| Schmidt witness | 3×3 binary quantum behaviors of Schmidt number ≤2; strengthened score G = F+εp | p=P(00\|10), a particular event probability | G≤7 for a certified ε. With M_A=F+4p−1, this becomes M_A≤6+(4−ε)p. The optimal slope α* is bracketed, not determined. |

Consequences of checking the definitions:

- The LF witness used for `65453/361250` is a **two-qubit singlet with real
  projective readouts**, not a qutrit. The number is a necessary total disagreement
  for this target score, not a universal efficiency or environment fraction.
- The Schmidt local deterministic saturators have **F=7**. The ceiling 6 belongs
  to a different functional, M_A. There is no contradiction after using
  `M_A=F+4p−1`. At the supplied positive penalty's local equality points, p=0.
- F≤7 also holds on a two-sided partial-local hull H, but **G≤7 does not**.
  A source facet point has F=7 and p=1/3, hence G=7+ε/3 for every ε>0.
  A universal “all four are partial-local facets” premise would already be wrong.
- Multiplying and shifting recovery to manufacture a leading 6 does not relate
  its physical resource to any of the other three. A valid coordinate relation
  must map the domains, measurements, and quantifiers as well as numbers.
- Different face dimensions do not exclude a general theorem. Conversely, common
  affine syntax and “positive certificate + witness” do not establish one.

## What was actually checked here

**Source checks run successfully:** forced-signaling `verify_K8.py`,
`verify_Sigma.py`, `verify_directional.py`; recovery `verify_sharp_recovery.py`
and `verify_full_curve.py`; Schmidt `verify_sharp_qubit.py`, `verify_facet.py`,
`verify_penalty_endpoint.py`, `verify_penalty_not_partial_local.py`, and
`verify_m3322_corollary.py`. The last independently checks the two score
normalizations and the one-sided positivity/CHSH derivation. These are executions
of the pinned source checkers, not independent formalizations of their semantics.
We did not run every source test, the singular penalty-boundary checker, or the
full equality-face chain. The tighter 0.16310672 endpoint is inspected source
status, not a newly reproduced endpoint in this spike.

**New Lean proof:** [ForcedSignaling.lean](../../OntologySeparation/Certificates/ForcedSignaling.lean)
reconstructs 384 variables (256 hidden-response weights, 128 auxiliaries), 272
inequality rows and four normalization equations. The objective and row
coefficients are defined from setting/output indices; an opaque imported matrix
is not treated as physics. The 36 nonzero dual entries are copied from the pinned
MIT certificate. Lean's kernel checks every column inequality. Finite-sum order
arithmetic then proves the upper bound for **every real feasible LP point**.
An explicit zero-budget deterministic point attains 6, proving nonemptiness and
the intercept, not the slope's optimality.

A separate executable check compares every coefficient and dual entry with
fingerprints of the upstream verifier's independently reconstructed arrays.
[The manifest](certificates/forced-signaling-k8.json) pins source file hashes and
array hashes. This checks transcription consistency; it is not part of the
logical trust base. Kernel checking, transitive axiom auditing, and reporting
continue through the existing machinery. Tests also exhibit the exact auxiliary
column left uncontrolled when a TV-budget row is deleted.

**Still outside that theorem:** equivalence of this LP with a physically stated
conditional-local model; construction of its variables from Born probabilities;
total-variation calibration; source coefficient-optimality and cluster-state
primal/dual certificates; finite-shot evidence. Calling the exported LP theorem
a complete forced-signaling theorem would overstate the result.

## Feasibility and reuse

| Port | Evidence from this spike | Remaining proof obligations / decision |
|---|---|---|
| Rational LP dual | Implemented and kernel-checked over the full finite LP | **Go**: add the physical behavior/decomposition/TV bridge and matching sharp witness next. Reuse mathlib finite sums/order; generalize only when a second actual certificate needs it. |
| Recovery free-unitary certificate | Source checker reconstructs Q−S=H and Tr_A Q=I; 53 reduced words, positive reduced Grams of sizes 46 and 48 | **Conditional go, not cost-proven**: certify exact factorizations, prove evaluation of reduced words in arbitrary-dimensional unitaries respects multiplication/star, lift Gram positivity, and connect the normalized Choi operator to a recovery channel and the measured score. Passing numeric matrix instances cannot establish this universal claim. |
| Schmidt SOS | Source checker validates a 70×70 rational Gram and the qubit polynomial identity | **Conditional go, higher semantic burden**: qubit/Clifford evaluation, deterministic-observable branches, binary POVM reduction, Schmidt compression and mixtures. Facet rank, equality face, and optimal penalty remain distinct obligations. A facet LP alone cannot prove the dimension bound. |

Pinned mathlib already provides `Matrix.PosSemidef`, positive conjugation,
`posSemidef_conjTranspose_mul_self`, and `FreeGroup` reduction/evaluation
infrastructure. Pinned Lean-QIT provides channels, Choi/Kraus constructions and
recovery/discrimination infrastructure. Reuse those; do not build replacement
matrix, channel, or free-word foundations. A certificate-specific factorization
checker may be needed. Its output must prove a matrix identity and positivity in
Lean, not import an external checker's Boolean verdict. This inventory does not
claim that the complete recovery/SOS adapters already exist upstream.

## Recheck or inspect the result

```sh
lake build OntologySeparation.Certificates.ForcedSignaling Tests.TradeoffSpike
python3 scripts/check_external_certificate.py
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/ExternalCertificateStudy.lean -o examples/external-certificate.html
```

The [HTML report](../../examples/external-certificate.html) exports the exact
universal theorem and the explicit zero-budget witness through the existing
axiom-audited path. Its theorem names and types expose the LP scope. The main
adopter path stays unchanged: this is advanced certificate review, not a new
recommended way for a physicist to hand-enter LP constraints.

To reproduce the source fingerprint, use the pinned `paper/verify_K8.py`'s
`obj` (append 128 zeros), `Aub`, `A_eq` (append 128 zeros per row), the ordered
`nonzero_dual_entries` keys, and `mu`. Serialize each as integer lists with
`json.dumps(value, separators=(',', ':'))`, UTF-8, then SHA-256. Do not regenerate
these expectations from Lean: that would erase the independent transcription
check. Source license and hashes are retained beside the manifest.

## Decision and PR sequence

1. **This PR — reconciliation and a real feasibility proof.** Establish the
   meanings, pinned evidence, successful LP port, and explicit missing semantic
   bridges. No new generic `PenalizedFacet` hierarchy.
2. **Next — forced-signaling physical bridge and sharpness.** Define a physical
   finite behavior/decomposition and actual recipient TV in the existing finite
   probability vocabulary; map it to the checked LP. Add a matching valid model
   for coefficient optimality, then the cluster marginal-matching example only
   if its algebraic certificate and Born construction are both checked. A
   physicist supplies a supported budget and gets a scoped bound plus its
   physical witness. Failure to build the physical bridge blocks that claim.
3. **Then — universal operator-certificate vertical slice.** Port one reduced
   Gram factorization and its interpretation for arbitrary finite-dimensional
   U,V; connect one recovery inequality to Lean-QIT's channel semantics. Keep
   exact evaluation an optimization, not an extra physical premise. Stop and
   re-scope if the only working proof checks finitely many U,V matrices.
4. **Decision checkpoint — substantive H4 or robust access.** Only pursue H4 if
   a common structural hypothesis actually derives at least two physical
   tradeoffs and predicts something not supplied as a per-instance premise.
   Otherwise retain the useful certificate infrastructure and pursue a
   constrained-access minimax question. No “unification achieved” label for a
   record that merely stores four already-proved inequalities.

These are sequential reviewable milestones, not four speculative PR shells.
Any common `CertifiedTradeoff` / `AttainedTradeoff` data wrapper can be extracted
from working cases later. A `FacetCertificate` is optional geometric evidence;
there is no reason to require one for all quantum recovery statements.

## Minimax: exact exit criterion, not a renamed pointwise optimum

A robust value v needs **one allowed protocol** with gap at least v for every
admissible model, and a matching converse: for every allowed protocol there is
an admissible model with gap at most v. Include existence of admissible models,
allowed operations, available calibration, permitted randomization and the order
of choices. Never move `∃ protocol` through `∀ model` without a theorem.
`Tests/TradeoffSpike.lean` checks a two-model counterexample: each model has a
perfect tailored protocol, but no single deterministic protocol works for both.

The #33 known-phase overlap interval has a common optimal readout, so its robust
endpoint follows from a special monotonicity property. That does not settle
fragment selection, unknown phase, restricted feedback or correlated uncertainty.
A stronger question must couple at least one genuine control restriction with
uncertainty that changes the best experiment. Compare it against existing robust
state discrimination before calling it new. If the result reduces to the known
erasure/trace-norm formula with renamed variables, change the physical question.

## Literature boundary

- [Moreno et al., Quantum 6, 785 (2022)](https://quantum-journal.org/papers/q-2022-08-24-785/):
  relaxed absolute events and LF inequalities are prior art. #33 has the detailed
  setting and normalization audit; this spike does not duplicate that branch.
- [Bancal et al., Nature Physics 8, 867 (2012)](https://arxiv.org/abs/1110.3795):
  finite-speed hidden influences and operational signaling precede this program.
  The new source's Li–Hu–Deng–Scarani cluster preprint (2608.05271) was not
  retrievable in this check; its Born construction needs direct verification.
- [Quintino et al., PRL 123, 180401 (2019)](https://arxiv.org/abs/1902.05841):
  device-independent tests of incompatibility supply the relevant partial-local
  comparison. The source repository's exact corollary checker was run; Appendix G
  was not independently reread here because full-text retrieval failed.
- [Berta–Coles–Wehner (2014)](https://arxiv.org/abs/1302.5902):
  a relationship between guessing and recoverable entanglement already exists.
  Matching affine formulas do not identify its score with the coherent-test f.
  Source `docs/PRIOR_ART.md` records a counterexample and unresolved reductions.
- [Fujiki–Tanaka (2026 preprint)](https://arxiv.org/abs/2609.04020):
  the abstract explicitly treats common unknown-unitary nuisance, least-favorable
  priors and finite-grid minimax discrimination. This was an abstract-level check,
  not a proof audit; it is close enough to forbid a generic “first robust quantum
  discrimination” claim. Continuous guarantees cannot be inferred from a grid.

This bounded reconciliation does not establish priority or publishability. The
scientific ambition remains a new, independently reviewed physical result.

## Validation of this increment

The complete local `sh scripts/check.sh` passed: Lean library/tests, transitive
axiom audit, 65 Python tests, HTML logic, independent downstream examples,
24 invalid-input guardrails, all reports, and the new exhaustive source/Lean
coefficient comparison. The certificate's executable representation was changed
from a nested vector to an array after a compilation-performance issue; its
proofs, regression tests, full coefficient comparison, report and axiom audit
were rechecked on that final representation. No additional trusted axiom,
external solver result, or native evaluator verdict is used to prove the bound.
GitHub CI remains a separate merge gate.
