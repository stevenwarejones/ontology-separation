# Finite-speed hidden influences: definitions audit

This audit separates a fixed-layout classical causal model, conditional-local
completion tables, and conditional locality **intersected with no-signaling**.
It makes no novelty claim and is not an empirical justification of screening-off.

## Primary sources and conventions

- [Bancal et al., Nature Physics 8, 867 (2012), arXiv:1110.3795v2](https://arxiv.org/html/1110.3795v2): Fig. 2, Lemma 1, Fig. 3 and the timing-switch argument following it.
- [Barnea et al., PRA 88, 022123 (2013), arXiv:1304.1812v3](https://arxiv.org/html/1304.1812v3): Secs. II, III.1, Eq. (5), and III.3. The arXiv identifier is 1304.1812.
- [Li et al., arXiv:2608.05271v1](https://arxiv.org/html/2608.05271v1): Eqs. (1), (3), supplement S1–S4, S.I.4, and the delay lemma S18–S19.
- [Forced-signaling manuscript](https://github.com/stevenwarejones/forced-signaling/blob/main/paper/main.tex): setting/definitions, pinned-marginal lemma, accessible-signaling proposition, and four-site restoration. Reviewed source blob: `a2e24014f3afd2e7cc25d46f4f7394f3275f957b`.
- Scarani et al., Foundations of Physics 44, 523–531 (2014), DOI
  [10.1007/s10701-014-9785-1](https://doi.org/10.1007/s10701-014-9785-1),
  [arXiv:1304.0532](https://arxiv.org/abs/1304.0532). Bibliographic identity
  verified; no equivalence to its additional model variants is asserted here.

The table uses equation pointers and paraphrases rather than long reproduced
passages. A source's silence about a cone boundary is not evidence for a chosen
convention. Lean uses open hidden cones (Li S.I.5) and closed ordinary light
cones. The concrete examples have strict hidden-link and sender-exclusion margins;
recipient-to-collector links may lie on a closed light-cone boundary.

## Comparison

| Concept | Bancal 2012 | Barnea 2013 | Li 2026 | Manuscript | Lean and verdict |
|---|---|---|---|---|---|
| Physical hypothesis | Bell local causality with speed v; shared randomness and communication (Fig. 2) | Complete common-past description (Sec. II) | Preferred frame and hidden cones (S.I.1) | Preferred-frame model | `VCausal.Protocol`, `GeometryOrder`, `LC4Layout`: finite classical, fixed-layout specialization; **not established** as all finite-speed theories |
| Blind pair | B,C mutually outside v-cones (Fig. 3) | A,C are the blind pair (different labels) | B~C (S.I.1) | B,C late | `LC4Layout.bc/cb`: **identical** causal exclusion after relabeling; boundary choice explicit |
| Conditional locality | Lemma 1(a), conditioned on axdw | Eq. (5), conditioned on by | Eq. (3)/S1, subnormalized early-event weights | Context-dependent response mixtures | `StochasticModel`, finite disintegration and `Protocol.full_behavior`: same finite conditional-local table semantics; geometric early restrictions are additional |
| Early structure | A before D in Fig. 3; earlier output cannot use later choice | Only common-past information may condition locality (III.1) | Projected early-side description does not impose every internal early causal constraint | Completion class permits whole early context | Existing `StochasticModel` is **Lean larger** than a fixed physical layout. `EarlyAllowed` imposes the correct order. `backwardsTable_not_allowed` refutes unrestricted equality |
| Measurement independence | Free choices independent of initial state (Fig. 2) | Common-cause distribution plus free inputs | Explicit main-text assumption; random independent delay choices in S.I.5 | Assumed | `Protocol.shared` is independent of actual settings; **identical** within the finite model. A posterior distribution conditioned on early records may depend on early settings without violating this |
| Conditioning/postselection | Conditioning on early records, not arbitrary future selection | III.1 distinguishes conditioning before/after blind events | Non-null early events; no postselection in S.I.4 | No postselection | `FiniteKernel.condition_weight` handles null fibers; **identical** finite conditional semantics. Future acceptance filtering is outside the model |
| Observable data | ABD and ACD (Lemma 1) | AB and BC, after relabeling (III.2) | LC4 ABD/ACD; common operational distribution (S.I.4) | Same LC4 families | `MatchesCluster`: **identical** families. Full table preservation is stronger than merely matching these marginals |
| No-signaling | Separate condition in Lemma 1(b) | Separate hypothesis in Lemma 1(i) | HIC = NS ∩ CL (Eq. 1/S2) | NS relaxed and violation quantified | `StochasticModel` alone is **Lean larger** than HIC by design; do not identify it with HIC |
| Signaling size | Existence of dependence, no numerical TV normalization | Existence of dependence (III.3) | No-signaling constraints | Maximum single-input-switch TV to full complement | `Model.signaling`: **different quantity** from a Boolean NS violation. For normalized finite distributions, TV=0 iff all recipient probabilities agree; positive TV witnesses a violation |
| Usable communication | Joint records collected outside sender light cone (Fig. 3) | III.3 distinguishes inaccessible geometry | Explicit collection events S10 | Direct collection; fixed settings; no adaptive extensions | `Collectible` in follow-up PR: same closed-light-cone criterion in 1+1. A signaling table alone does not prove accessibility |
| Timing consistency | Random measurement-time choices transfer marginals | Delaying one blind party preserves other marginal (III.2) | S18–S19, choices at original events | Separate physical premise | Fixed-layout `Protocol` alone does **not establish** cross-layout consistency; follow-up constructs a common timing protocol |

## Consequences for the Lean results

1. The larger completion class gives valid lower bounds for every subclass
   embedded by the full-behavior theorem. It does not automatically transfer
   attainment or slope optimality. Each upper/attainment claim needs a witness.
2. A connected early pair does **not** make every completion causal. For A before
   D, P_A must be independent of w; for D before A, P_D must be independent of x.
   For disconnected early parties, P_AD must admit a Bell-local decomposition.
3. The finite realization construction accepts an early common-cause model whose
   projected law matches the completion, and reconstructs the **whole** behavior.
   The LC4 uniform-product early law supplies such a model in every early order.
4. There is no claimed `Lean smaller` result within the explicitly finite,
   classical, fixed-layout class. Infinite hidden spaces and unrestricted physical
   ontologies are **not established**, not silently classified as equivalent.
5. Classical screening-off is a physical assumption. Cone geometry restricts
   communication paths; it does not by itself imply Bell factorization.
6. Local choice and outcome events have separate geometry in `MeasurementLayout`.
   The LC4 table theorems currently use its explicit instantaneous specialization.
   A general two-event-per-party stochastic semantics is not claimed.
7. `relay_inside_cone` proves geometric closure under finite paths. Absorbing a
   finite random tape in the shared seed models finite internal memory, but no
   universal theorem about arbitrary field dynamics or arbitrary networks is
   asserted.

## Scope of the exact optimum

The exact LC4 minimum is over the finite classical protocol class in one fixed
preferred-frame layout. Rational spacetime coordinates do not restrict the real
probability weights. It is not yet a sharpness statement for a single theory
reproducing quantum mechanics across every possible measurement arrangement.
The follow-up timing PR must state separately what it establishes about a finite
menu of interventions and the extension of an attaining witness.

## Why the response-table semantics is causal

The fixed-layout protocol samples one finite response table before any actual
setting is selected. In the A-before-D case, `EarlyAllowed` makes A a function
of its own setting and this seed, whereas D may also use A's setting. Dependence
on A's already-produced outcome can be folded into the same deterministic
function. The reverse order is symmetric. In the disconnected case both early
responses use only their respective settings and the common seed; this is the
finite deterministic-response presentation of a Bell-local early law.

Each late party receives both early settings and may reconstruct the early
outcomes from the seed. Its response table is evaluated only at its own late
setting. Thus B and C cannot use each other's choice or output. Evaluation in
the early causal order followed by B and C is canonical; swapping the two late
evaluations changes nothing because these are separate pure functions of the
same seed. The reservoir construction pre-samples potential tables for every
context, before learning which context is actual. Its shared distribution can
depend on the specified model, but not on the actual settings. This distinction
is essential to measurement independence.

The existing finite stochastic completion interface has the explicit form

\[
P(a,b,c,d\mid x,y,z,w)=\sum_\omega\mu_{xw}(\omega)
 A_{xw,\omega}(a)D_{xw,\omega}(d)
 B_{xw,\omega,y}(b)C_{xw,\omega,z}(c).
\]

This is conditional locality of the blind pair after early information has been
included in the conditioning state. The physical interface instead starts with
one setting-independent law \(\rho(\lambda)\) and causal response functions.
`EarlyMatches` expresses the extra compatibility condition on its AD marginal.
`realizable_iff_early` is an exact finite response-law characterization under
that condition; `realize_full_behavior` and `realizeLC4_behavior` state the
observable consequences. An early-context-dependent posterior in the first
formula does not make the initial \(\rho\) depend on settings.

## Finite support in arbitrary hidden spaces

`SupportedProtocol order Ω` does not require `Fintype Ω`. It specifies a finite
support, a nonnegative normalized weight function that vanishes outside it,
and causal response tables. `SupportedProtocol.toProtocol` restricts to the
finite support subtype, and `SupportedProtocol.full_behavior` proves exact
preservation of the complete observed law. Thus an infinite ambient label space
is allowed when the law has finite support. This is not a measure-theoretic
extension to genuinely infinite support; the usual deterministic-strategy
convex-hull argument for that case is standard but not formalized here.


Timing consistency is needed for transferring data between interventions, not
for the fixed-layout exclusion with LC4 matching already assumed. The PR-box
examples in `VCausalAssumptions` are not LC4-specific deletion adversaries and
do not certify a four-premise `MinimalCore`.
