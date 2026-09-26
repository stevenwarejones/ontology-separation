# From forced signaling to collectible records

This development uses a **fixed preferred frame**, rational coordinates in 1+1
spacetime, c=1, finite classical randomness, and fixed settings during each
single-input switch. It does not treat an unknown preferred frame, boosts, a
delay cover, adaptive communication protocols, or finite-sample statistics.

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
are open; ordinary light cones are closed. All positive examples have strict
margins, so their conclusions do not hinge on boundary conventions.

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
| Forced usable signal | `vcausal_forced_superluminal_signal`, `timing_forced_superluminal_signal` |
| Sharpness with quantum connected timing branches | `attaining_timing_extension` |

These are the corresponding manuscript MANIFEST rows eligible for a Lean label
once the PRs are verified and merged. The paper repository is not changed here.
The [definitions audit](FORCED_SIGNALING_DEFINITIONS_AUDIT.md) remains essential:
classical screening-off is an assumption, not a consequence of cone geometry,
and conditional locality alone is different from no-signaling ∩ conditional
locality. The mathematical proofs do not decide which ontology nature uses.
