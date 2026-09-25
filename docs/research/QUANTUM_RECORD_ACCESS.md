# Explicit quantum record access: formalized reproductions

These finite-dimensional models reproduce standard decoherence and local
indistinguishability. They make no novelty claim and have not been reviewed by a
human domain expert. All theorem names below have the prefix
`OntologySeparation.`.

| Model | Checked statement | Source |
|---|---|---|
| Generic perfect binary record | `PerfectRecordTraceout.cross_branch_zero` and `same_branch_preserved`: tracing out a perfect copy removes cross-branch entries and preserves same-branch entries. | [PerfectRecordTraceout.lean](../../OntologySeparation/Experiments/PerfectRecordTraceout.lean) |
| Two redundant copies | `TwoRecordEnvironment.one_copy_missing_state` and `full_access_strictly_distinguishes`: one inaccessible copy hides coherence; joint access can distinguish it. | [TwoRecordEnvironment.lean](../../OntologySeparation/Experiments/TwoRecordEnvironment.lean) |
| Laboratory/environment access | `QuantumAccessMonogamy.disjoint_local_blind_joint_separates`: the specified coherent and collapsed states agree under local access and differ under joint access. | [QuantumAccessMonogamy.lean](../../OntologySeparation/Experiments/QuantumAccessMonogamy.lean) |
| Disjoint access policies | `QuantumTwoObserverMonogamy.disjoint_policies_cannot_both_separate`: the defined disjoint policies cannot both distinguish the selected states. | [QuantumTwoObserverMonogamy.lean](../../OntologySeparation/Experiments/QuantumTwoObserverMonogamy.lean) |
| Explicit four-qubit model | `FriendshipMonogamyQuantum.observerA_state`, `observerB_state`, and `two_copy_access_obstruction`: either missing perfect environment copy dephases the retained state, so every allowed finite quantum test agrees. | [FriendshipMonogamyQuantum.lean](../../OntologySeparation/Experiments/FriendshipMonogamyQuantum.lean) |
| Two imperfect records | `ImperfectTwoRecordAccess.distance_pair_exact` and `attainable_region_iff`: if the two record overlaps are `r₁,r₂`, the two one-copy observer trace distances are exactly `12 r₂/25` and `12 r₁/25`, and every pair in `[0,12/25]²` is physically attained. The perfect-copy obstruction is the `(0,0)` corner. | [ImperfectTwoRecordAccess.lean](../../OntologySeparation/Experiments/ImperfectTwoRecordAccess.lean) |

The four-qubit observers' views both include the laboratory. Those two views
are not disjoint physical regions; their environment copies are distinct. The
separate access-policy theorem states its own disjointness premise explicitly.
The imperfect-record theorem is a continuous, exact baseline for one explicit two-branch source family with two independently parameterized record overlaps. It shows that the perfect-copy obstruction is not, by itself, a robust cross-observer monogamy inequality: once both missing copies are imperfect, both observer views can simultaneously recover coherence, and the complete attainable region for this family is a square. It does **not** assert the same region for arbitrary record channels, correlated environment fragments, adaptive observers, or all quantum states.

The explicit four-qubit module supersedes the unused effective overlap-product
benchmark proposed in PR #72. The benchmark is omitted; no other module imports
it. The public theorems of the included modules are registered in
[Tests/Audit.lean](../../Tests/Audit.lean). Run `sh scripts/check.sh` to rebuild
the library, tests, reports, and [generated axiom audit](../AXIOM_AUDIT.txt).
