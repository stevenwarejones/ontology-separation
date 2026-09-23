# Research program: post-#73 frontier

Status: active research plan, refreshed 2026-09-23 from main at
`76338444ec1ef133806c861485526c5c51adc741` after merged PR #73.

A checked theorem establishes only the proposition and model class stated in its
Lean declaration. Reproductions remain reproductions; finite search is not a
class-wide impossibility theorem; and no novelty claim is made without a focused
prior-art audit and external scientific review.

## Goal

Use explicit operational assumptions to derive experimentally meaningful
separations, sharp tradeoffs, or impossibility results. The preferred unit of
progress is now a physical theorem with a proved scope boundary, not another
framework layer.

The scientific success criterion remains an independently reviewed result about
a physically motivated model class that was not already known. Formalized
reproductions and adversarial reductions are valuable foundations, but are
labeled as such.

## What main now contains

The earlier infrastructure program has largely been completed. The relevant
frontier is:

| Area | Checked state on main | Explicit remaining boundary |
|---|---|---|
| Local Friendliness | finite joint-event correspondence, genuine LF bound and quantum witness, relaxed readout-error bound, exact `sqrt 2` Local Agency result | no complete 3x3 LF-polytope enumeration; no apparatus-level premise certification |
| Forced signaling | physical LC4 target, exact 59-atom witness, marginal matching, universal fixed-completion lower bound, exact minimum `(sqrt 2 - 1)/4` | deterministic finite response-table class has not been proved equivalent to general finite stochastic conditional-local models; slope-8 optimality over every allowed completion is not in Lean |
| Quantum record access | perfect-record traceout, two-copy access, local/joint discrimination, two-observer access obstruction, explicit four-qubit friendship-monogamy reproduction | perfect-record results do not characterize imperfect records, arbitrary states, or arbitrary observer access families |
| Baumann-Brukner | Sec. 3 source, Bob measurements and unread Wigner pinching reconstructed in QIT; setting-dependent flip rates proved | no class-wide channel theorem; identifying the mathematical record change with awareness remains interpretive |
| Adversarial boundary map | passive nesting collapse, reduced timelike Bell collapse, unrestricted scalar-report adversary, locality-free contextual gluing benchmark | stronger active-intervention formulations remain open |
| Reporting / access framework | proof-bearing claims, access-relative equivalence and separators, finite model classes, named-register access, exact recipes and adopter checks | software generalization is no longer the highest-priority scientific work |
| Statistics | exact expectation-level statements and reports | no checked finite-sample rejection analysis for the current flagship physical theorems |

There are no open PRs or issues at this refresh point.

## Immediate sequence

The next increments are intentionally sequential. A later increment should not
start until the earlier theorem's code, tests, audit roots and documentation are
complete.

### F1 — close the finite hidden-influence representation gap

Define a general finite stochastic conditional-local response model with explicit
normalization and conditional response distributions. Prove that every such model
can be refined into the deterministic response-table representation already used
by `HiddenInfluence.Model`, while preserving the observable ABD/ACD marginals and
recipient signaling total variation. Also prove the converse embedding.

Exit criterion: an equality/equivalence theorem for the observable model classes,
not merely a one-way construction. Add negative tests that demonstrate why
normalization and conditional locality are required. Audit all public roots.

Scientific meaning: this removes a representation restriction from the existing
forced-signaling theorem. It does not by itself enlarge the physical assumptions
beyond finite conditional-local hidden-variable models.

### F2 — all-completions forced-signaling sharpness

Make the operational completion an explicit finite parameter rather than a fixed
constant. Reconstruct the admissible completion family and certify the full
completion spectrum needed to prove that the coefficient 8 cannot be improved
within that family.

Exit criterion: a Lean theorem quantifying over every stated completion, plus an
attaining completion/witness establishing sharpness. External enumeration may
propose a certificate; the kernel must verify the universal statement. The
completion family and its cardinality must be defined from semantics, not a
trusted label.

Scientific meaning: this closes the second scope caveat in
`docs/research/FORCED_SIGNALING_THEOREM2.md`.

### R1 — imperfect quantum record-access tradeoff

Move beyond perfect copied records. Introduce a physically explicit one-parameter
(or otherwise minimal) family of imperfect environment records using QIT states or
channels, and quantify what two specified observer access policies can
simultaneously distinguish.

Prefer standard operational quantities such as trace distance, fidelity, or
optimal binary discrimination probability. Do not introduce a custom scalar
unless it has a proved operational interpretation.

Exit criterion: a continuous upper bound over the stated family and an explicit
attaining construction, with the perfect-record theorem recovered as a boundary
case. If the result is a direct instance of a standard trace-distance/fidelity
identity, present it as a formalized baseline and use it to select the next harder
access model rather than claiming novelty.

### N1 — active nested-friend intervention

Only after F1/F2/R1 are settled, revisit the post-LF boundary map with a genuinely
new operation. Passive copies are already proved to add nothing. The next model
must include an incompatible outer choice such as read, coherent reversal, or
interference, with any meta-record semantics stated explicitly.

Exit criterion: either a checked reduction to a known Bell/contextuality class or
a new scoped operational constraint with an explicit quantum target and adversary
analysis. A failed search is not a no-go theorem.

### S1 — finite-sample flagship test

After one physical theorem is stable, add one end-to-end finite-statistics result
rather than a generic statistics framework. Forced signaling is the preferred
first target.

Specify the null class, setting distribution, filtration/memory assumptions,
event-selection rules, stopping rule and calibration nuisance parameters. Reuse
established Bell-test statistical methods where possible.

Exit criterion: a checked finite-sample type-I error bound for a named statistic
under the stated null, together with a reproducible prospective analysis example.
Observed estimators and exact expectation values remain distinct.

## Work that is deliberately not next

Do not prioritize a new generic `UniverseComparison` hierarchy, broad automatic
circuit synthesis, another ontology checkbox layer, or additional passive nested
observer examples. Those may improve ergonomics, but the repository now has
enough infrastructure to test substantive physical questions.

Likewise, do not pursue a common tradeoff abstraction merely because LF error,
forced signaling and record accessibility can all be written as inequalities.
A shared theorem is warranted only if a common physical hypothesis derives at
least two of them and predicts something new.

## Review and verification gates for every research increment

- State the model class, quantifier order, operations and observables in the PR.
- Reuse mathlib and Lean-QIT before introducing local linear-algebra foundations.
- Kernel-check every imported finite certificate; external scripts are proposal
  or transcription checks, never proof rules.
- Add public theorem roots to the transitive axiom audit.
- Run the full `sh scripts/check.sh` gate on the final head.
- Add a negative test for the theorem boundary where meaningful.
- Update the relevant research guide so its scope caveats match the theorem.
- Distinguish reproduction, known corollary, scoped extension and novelty claim.
- Do not start the next increment while CI, audit output, generated reports or
  documentation are inconsistent with the branch head.

## Longer-term directions

After the immediate sequence, reconsider:

- active Wigner-friend interventions beyond ordinary LF/contextuality;
- channel-class versions of the Baumann-Brukner memory alteration result;
- robust access/discrimination under unknown phase or correlated noise;
- complete finite LF-polytope results only if required by a physical theorem;
- finite statistics with realistic detection and selection assumptions;
- constrained exact experiment proposal with Lean verification.

The criterion for choosing among them is scientific leverage: prefer the smallest
additional physical structure that makes a theorem stronger or closes a real
scope gap.

## References and boundaries

See [Prior art and reuse decisions](PRIOR_ART.md),
[Adversarial boundary map](ADVERSARIAL_BOUNDARY_MAP.md),
[Forced-signaling theorem guide](FORCED_SIGNALING_THEOREM2.md),
[Quantum record access](QUANTUM_RECORD_ACCESS.md), and
[Baumann-Brukner guide](BAUMANN_BRUKNER_GUIDE.md).

The repository's Lean proofs certify mathematical implications inside stated
models. They do not certify apparatus calibration, consciousness, philosophical
interpretations, experimental data authenticity, or scientific priority.
