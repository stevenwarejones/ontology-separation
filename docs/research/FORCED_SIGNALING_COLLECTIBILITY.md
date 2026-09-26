# From forced signaling to collectible records

## Physical assumptions

The results assume a fixed preferred frame; 1+1 dimensions; instantaneous
measurement events; finite classical randomness; Bell screening-off;
measurement independence; no postselection; and, for the timing results,
the specified finite menu of blind, delayed-B and delayed-C interventions.
Coordinates are rational, with c=1; probabilities are real. Settings other than
the switched input are held fixed. Timing consistency is an additional premise
for transferring connected-branch data, not for the direct fixed-layout bound.

The results do not supply an unknown-frame delay cover, arbitrary adaptive
communication, finite-sample statistics, or an all-layout physical theory.

## Collection geometry

`VCausal.Collectible s R` requires a nonempty finite set of recipient events and
a point receiving every record through a closed ordinary light cone while
remaining outside the sender's closed light cone. Records must actually have
been produced at their specified events. Empty records are excluded by
convention; they cannot carry information.

Write u=t+x and w=t−x. For a nonempty R, the intersection of its future light
cones has apex

    u*=max_R u, w*=max_R w, t*=(u*+w*)/2, x*=(u*−w*)/2.

`collectible_criterion` proves that collection is possible exactly when
`u* < u(sender)` or `w* < w(sender)`. Thus the criterion is a finite rational
calculation and includes an explicit collection point. Hidden-influence cones
are open; ordinary light cones are closed. The sender-exclusion margins are strict. In the minimal example the
collector at (39/20,1) lies exactly on B’s light-cone boundary (and the
mirror collector on C’s). The cone is closed, so this is allowed. Delaying
either collector by any positive amount less than 1/20 preserves receipt
of every record and keeps both collectors outside their respective sender
cones; the strict margins are 1/20 and 3/5, respectively.

## Recipient sets and the segment obstruction

The LC4 target pins BD and CD against A-input changes, and AB and AC against
D-input changes. `ForcedSignalingPinned.pinned_BD`, `pinned_CD`, `pinned_AB`, and
`pinned_AC` derive these equalities from the original exact quantum matrices and
`MatchesCluster`. `ForcedSignalingAccessible.pinned_A_subsets` and
`pinned_D_subsets` cover every projection onto subsets of those pairs. These are
unconditional marginal distributions, without outcome-based selection.

`recipients_A_dichotomy` and `recipients_D_dichotomy` show that any other
recipient set excluding the sender contains both B and C. If the sender is
spatially between B and C and is no later than either, `segment_obstruction`
proves that every point receiving both records is inside the sender's light
cone. Combining these facts, `zero_accessible_A` and `zero_accessible_D` prove
**exactly zero TV for every collectible recipient set**. In particular this
covers the three-site layout with co-located early parties lying on segment BC.
Co-location alone is insufficient; the segment and time hypotheses are explicit.

## Positive layouts

| Layout | Events (ct,x) | Hidden speed | Collection |
|---|---|---|---|
| Minimal separated example | A=(0,−1), D=(11/20,1), B=(17/20,−1/10), C=(17/20,1/10) | 4 | BCD collected at (39/20,1) outside A's cone; ABC at (39/20,−1) outside D's cone |
| Four-site restoration | A=(0,−6000), D=(c·100ns,6000), B=(c·200ns,−5000), C=(c·200ns,5000) | 10000 | Opposite outboard collectors at time c·200ns+11000 |

`ForcedSignalingLayouts` verifies both LC4 geometries, the A-before-D order,
both full-complement collection claims, and the minimal example's margins
1/20 and 3/5. The restoration uses the exact SI value c=299792458 m/s.
Its early A→D threshold is
`12000/(299792458·10⁻⁷) = 60000000000/149896229 ≈ 400.27691423778`.
`restoration_threshold_rounding` verifies the interval 400.275 < threshold <
400.285, hence the paper's rounded 400.28. It is not asserted as an exact
rational equality. The supplied speed 10000 satisfies the actual cone tests.

## Complete accessible-signaling minimum

`ForcedSignalingAccessibleOptimum.proposition2_layout_minimum` proves the full
piecewise formula of Proposition 2 in the rational 1+1 setting: the minimum is
(√2−1)/4 when both full complements are collectible, and zero otherwise.
`stochastic_layout_minimum` covers the full finite stochastic conditional-local
class. Both branches include an actual attaining model, using the existing
balanced or one-sided pairwise-invisible certificates. This theorem does not
assume that the blind pair alone carries the forced signal.

`accessible` is the finite maximum over all 16 early-setting switches and all
seven nonempty recipient subsets, with zero contribution from an uncollectible
record. `recordParties_complete` checks exhaustive coverage;
`proper_encoding` and `full_encoding` prove that the statistic's labels encode
exactly the bits of those recipient sets. Singles use padded outcome labels,
which only add zero-probability entries. The maximization keeps every other
setting fixed for each switch and introduces no postselection or hidden-state
access. The separate `zero_accessible_A_of_blind_pair_not_collectible` and D
analogue prove the every-model zero branch whenever the blind pair is not
collectible; the segment condition is one sufficient reason, not a required
assumption of that stronger result.

## Physical payoff

`ForcedSignalingCollectibility.vcausal_forced_superluminal_signal` obtains an
actual maximizing context, identifies whether its sender is A or D, and proves
that the **full other-three-party record** is collectible with TV at least
(√2−1)/4. Both complements must be collectible: the quantitative theorem bounds
a maximum over directions and does not choose one in advance. A signal can also
be invisible to every proper recipient subset, so replacing the full record by
a pair would not justify this conclusion.

## Timing interventions and sharpness

`TimingLayout` contains the blind geometry and the two delayed events. Delay
choices occur at the original mutually blind late events. `TimingProtocol p`
uses the same seed law and the same early and undelayed responses as the blind
protocol p. Only the delayed outcome is replaced, using a kernel whose available
information is the seed, early settings, both late settings, and the retained
three-party record. The branch is an intervention, not conditioning on a
hidden-variable subensemble. Independence of intervention choices from the
seed is built into this shared-law semantics.

`delayC_preserves_ABD` and `delayB_preserves_ACD` prove marginal preservation for
all such kernels. `ConnectedMatches.blind_matches` transfers reproduction in
the connected branches to the blind branch of that **same mechanism**.
`timing_forced_superluminal_signal` then derives the collectible lower bound.
`minimalTiming` supplies concrete connected delays for the minimal layout.

For the converse, `FiniteKernel.complete_eq_target` disintegrates a normalized
finite target over already-produced records; its support theorem preserves
those records on every positive transition. `TimingProtocol.completeTarget`
samples only the delayed outcome from that conditional. `LC4FullDistribution`
checks positivity, normalization, and the retained marginals of the full Born
joint distribution with exact Q(√2) calculations. The theorems
`quantumTiming_runC`, `quantumTiming_runB`, and `attaining_timing_extension` show
that **every LC4-matching blind protocol**, including the exact minimizer,
extends to both connected branches with the complete quantum distribution.
This settles attainment for this finite menu of interventions. It does not
construct one theory reproducing quantum mechanics for every possible layout.

## Claim mapping and review boundaries

| Claim | Lean entry points |
|---|---|
| Pinned-pair lemma and all its recipient projections | `pinned_A_subsets`, `pinned_D_subsets`, recipient dichotomies |
| Zero accessible signaling under the segment hypothesis | `zero_accessible_A`, `zero_accessible_D` |
| Collection criterion | `collectible_criterion` |
| Minimal separated layout and exact margins | `minimal_lc4`, `minimal_A_collectible`, `minimal_D_collectible`, `minimal_margins` |
| Fixed-frame four-site restoration | `restoration_lc4`, `restoration_A_collectible`, `restoration_D_collectible` |
| Full piecewise accessible minimum, with attained branches | `proposition2_layout_minimum`, `stochastic_layout_minimum` |
| Forced usable signal | `vcausal_forced_superluminal_signal`, `timing_forced_superluminal_signal` |
| Sharpness with quantum connected timing branches | `attaining_timing_extension` |

These are the corresponding manuscript MANIFEST rows eligible for a Lean label
once the PRs are verified and merged. The paper repository is not changed here.
The [definitions audit](FORCED_SIGNALING_DEFINITIONS_AUDIT.md) remains essential:
classical screening-off is an assumption, not a consequence of cone geometry,
and conditional locality alone is different from no-signaling ∩ conditional
locality. The mathematical proofs do not decide which ontology nature uses.

## Headline, noise and the original no-go corollary

`ForcedSignaling.physical_main` bundles full-behavior soundness, LC4 realization,
the collectible lower bound on the restoration layout, and an attaining blind
protocol whose two delayed branches reproduce the full quantum distribution.
`restorationTiming` supplies both delayed events, rather than assuming that such
events exist.

`ForcedSignalingVCausal.conditional_local_nonsignaling_exclusion` reproduces the
NS ∩ conditional-local exclusion for the explicitly finite stochastic LC4 class.
It follows from the positive certified lower bound, not a new inequality.
`noisy_collectible_signal` transfers the entire certified curve
Σ(p)=max(0,(p(4+2√2)−6)/8) to a collectible full-recipient record.
`restoration_ninety_percent_signal` proves strictly more than 0.018 at p=0.9.
Below the positivity threshold the theorem still holds but does not force a
nonzero signal. This is white-noise visibility in `MatchesNoisyCluster`, not
an arbitrary experimental error model or a finite-sample confidence bound.

## Robustness and candidate frames

`ForcedSignalingGeometryRobustness.precedes_duration` gives the general cone-slack
condition for bounded nonnegative timing errors. In the minimal example every
outcome may independently occur between 0 and 1/100 time units after its choice:
`minimal_duration_lc4`, `minimal_duration_order`, and
`minimal_duration_cross_events` certify both outcome geometry and the stronger
choice-to-other-outcome exclusions. `minimal_duration_collectible` moves the
collectors later by 1/100 and preserves direct collection. These are geometric
robustness results for stationary sites. They do not construct arbitrary
continuous measurement dynamics; the stochastic protocol still has the stated
response-table semantics.

For |β|<1, `boost β (t,x)=(t−βx,x−βt)` omits the common positive Lorentz gamma
factor. Cone tests are homogeneous, so this scale does not change them.
`boost_lightFuture` and `boost_collectible` prove preservation of ordinary
causality and collection. `restoration_frame_iff` characterizes the **exact**
set of rational candidate frame velocities and rational hidden speeds in this
coordinate framework yielding a collectible LC4
layout by the explicit inequalities `restorationFrameTests`. The additional
A-before-D condition is `restoration_frame_order_iff`. These are tests of the
same laboratory events in a candidate preferred frame, not a Lorentz-invariance
claim for hidden propagation. For example, at v=10000 the blindness condition
is exactly v|β|≤1 (`restoration_blind_iff`), so requires |β|≤1/10000; an arbitrary boost does not preserve blindness.
A single protocol or delay menu covering every unknown preferred frame remains
unproved.

`scripts/check_vcausal_geometry.py` independently recomputes exact rational
cone tests, collection apexes, sender margins, cone boundaries, the restoration
threshold, duration corner cases, and frame examples. It is part of
`scripts/check.sh`. The finite test grid supplements the universal Lean proofs;
it does not replace them.

## Assumption-deletion audit

`ForcedSignalingLC4MinimalCore.minimalCore` packages a three-premise
`AdversarySearch.MinimalCore` for the **same exact LC4 marginal target with zero
A/D full-recipient TV** used by the forced-signaling exclusion. Every deletion
witness reports the full LC4 Born distribution; none substitutes a PR-box target.

| Deleted assumption | Witness | Retained assumptions |
|---|---|---|
| Setting independence | `dependent quantumLaw` draws its seed from the setting-dependent Born law | Deterministic local responses, no filtering |
| Local responses (the refined screening-off condition) | `jointResponse quantumLaw` uses a joint response kernel | One setting-independent seed law, no filtering |
| No postselection | `filtered quantumLaw` accepts a uniform outcome seed with probability equal to its Born probability; acceptance rate is exactly 1/16 | Setting-independent seed, deterministic local responses |

The generic `ForcedSignalingAssumptionCore.excludes` applies to every finite
hidden type. The deletion models each use 16 seeds. `deletion_witness` proves
that each model meets the target and retained assumptions and actually violates
the omitted law. The checked `quantum_zero_signal` result uses the full Born
law's A-to-BCD and D-to-ABC marginals.

This is premise-by-premise necessity **within the enlarged conditional-local
mechanism language**. It is not a complete physical-ontology minimality claim:
the language does not impose early causal order, spacetime geometry or a common
cross-timing mechanism. The joint-response witness, in particular, is a
countermodel in that language, not a proposed finite-speed physical theory.

`no_fourth_premise_core` proves that adding any fourth premise cannot produce a
minimal four-premise core for this same target while retaining the three laws.
The direct LC4 bound already excludes the target without timing consistency.
Timing is used to transfer marginals between interventions; proving its
necessity requires a separately specified intervention target and model language.

## General measurable hidden laws

`VCausal.MeasurableProtocol` and `ForcedSignalingMeasures` extend fixed-layout
soundness, the exact LC4 minimum, all-completions slope optimality, the noisy
lower bound and the collectible lower-bound component to arbitrary measurable
hidden probability spaces with measurable deterministic response tables.
Full-behavior pushforward equality and a finite-witness embedding justify both
sides of the exact minimum. See [the measure guide](FORCED_SIGNALING_MEASURES.md)
for the continuous example, rejection tests and remaining Markov-kernel scope.
