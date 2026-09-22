# Research program: from explicit assumptions to decisive experiments

Status: staged plan, started 2026-09-22. A milestone below is a research target,
not a claim that its theorem or software already exists.

## Goal and measure of success

Discover which operationally defined physical model classes can be distinguished
with specified experimental controls, prove when weaker controls cannot suffice,
and connect those results to statistically valid experiments. The scientific
success criterion is an independently reviewed result about distinguishability
that was not previously known. Verified reproductions are valuable foundations,
but are labeled as reproductions. No deadline or novel result is guaranteed.

The adopter's workflow is: choose physical assumptions, choose available systems
and operations, request comparison/search, inspect the scope and witness, then
export a reproducible report. Every milestone must improve that same workflow.

## Inventory: merged and open work

Repository state inspected on 2026-09-22; main refreshed to `a57ab06` after #22 and #24 merged. Open branches are implemented work under
review, not merged guarantees. Inspect their current heads before integration.

| Location | Already implemented | Boundary / how this program builds on it |
|---|---|---|
| main at `4ac299e` | Bell operational laws, an LF bound and quantum witness, FriendRecords-to-LF bridge, real-QM/QIT adapters, scoped claims and exact grids | LF is one finite 3×3 binary scenario and one genuine inequality, not a complete formalization of every LF facet or observer model |
| merged #21 | continuous leakage gap and real-channel bridge, exact boundary-law equality | effective attenuation model; no finite-shot inference |
| merged #22, main `d90ce67` | leakage public study, committed HTML pipeline, edited-parameter downstream test | reuse its publication/adoption pattern; do not recreate it |
| merged #24, main `a57ab06` | finite separator search, proof-linked search report/export, multi-candidate public example and downstream checks | finite enumeration is not an impossibility theorem for all physically allowed protocols |
| open #25, `68f9f52` | named register footprints, subset-based permissions, explicit record-access connections | a generic footprint function still requires a trusted physical interpretation |
| open #26, `6a25785` | typed local/joint two-register quantum protocols and equal-marginal local equivalence | only the left local factor or both factors; no arbitrary many-register reductions or general multi-round strategies |

The planned access/discovery work depends on #24–26 and will extend their APIs.
The first assumption-atlas increment is independent and branches from main.
No edits to those open branches are part of this increment. Their green CI and
merge state must be checked before using them as established dependencies.

## Seven ideas, three milestones

| Milestone | Ideas combined | Exit criterion |
|---|---|---|
| M1: assumptions and credibility | landmark LF formalization; assumption atlas; external review/upstreaming | paper-to-Lean premise map, exact operational encoding, audited implication and countermodel results, one independently reviewed baseline |
| M2: discovery and accessibility | experiment synthesis plus impossibility proofs; constrained AI autoformalization | one physical research question with a checked witness or class-wide obstruction; an adopter can change a supported premise/control without writing proof plumbing |
| M3: experiment and evidence | finite-statistics layer; complete design-to-data workflow | a formally justified test of a specified model class, reproducible trial-data analysis, provenance and selection assumptions visible |

External physics and Lean review runs through all milestones. Outreach requires
separate explicit authorization; preparing a review packet does not send it.
Upstream reusable definitions only after they have a stable purpose and external
maintainers agree that their library is the appropriate home.

## M1: understand precisely what the assumptions buy

**M1-A — This increment: close the LF encoding loop.** Construct an operational
FriendRecords model from every finite LF conditional-box mixture; check readable
records, conditional locality, independent preparation and equality of every
probability. Combine with the existing forward bridge to prove an iff. Exhibit
an LF model violating outcome independence, with all retained premises proved.
Export the iff, countermodel existence and quantum exclusion through normal
Claim auditing. Scope: the repository's finite encoding, not all mathematical
formulations of Bong et al. These are known-physics baseline results.

**M1-B — Paper-to-code contract and missing LF implications.** The initial
[review map](PAPER_CONTRACT.md) records the remaining obligations. Read the full
Bong et al. paper and supplement. Map AOE, locality, choice independence, observer
control, conditioning and zero-probability cases to definitions and derivations.
Distinguish primitive assumptions from parameterization choices. Prove each
claimed equivalence, or explicitly record an implication-only boundary. Do not
call four generic Boolean labels a complete ontology. Request a foundations
review of this map before claiming faithful full-theorem formalization.

**M1-C — Assumption atlas with constructive countermodels.** Within a fixed
ambient model type, prove implications and non-implications by actual witnesses.
For each allegedly necessary premise, attempt a model satisfying all remaining
premises that defeats the conclusion. Where no such model exists, look for a
weaker theorem. A missing proof is an open cell, not a false premise. A bound
below threshold alone is not class membership. Class nonemptiness is evidence,
not a renderer label. Extend to quantified relaxation parameters only after
their operational meaning and composition rules are clear.

**M1-D — Landmark scope expansion only when scientifically useful.** Select the
additional inequalities/facets or scenarios needed to test a candidate theorem.
If claiming a complete finite polytope description, certify completeness as well
as validity. Reproduce the quantum witness through explicit physical semantics.
No priority claim ('first') until a focused literature and repository audit.

### Early discovery question, begun alongside M1

Can record/environment control expose distinctions that remain invisible to
all protocols in a weaker operational class? Specify states or model classes,
allowed channels, accessible registers, ancillary systems, number of rounds,
classical communication, and noise before optimization. First check whether
standard equal-marginal or channel-discrimination results already answer it.
A restriction invented only to make the result nontrivial is not a breakthrough.

## M2: search, obstruction, and the physicist's front door

**M2-A — Reuse #24–26; separate finite search from physical completeness.** Add a
precise protocol class and a coverage theorem where a finite search claims
completeness. Search programs/optimizers are untrusted proposal engines; Lean
checks witnesses and bounds. A failed search reports its budget and domain.
It does not become a no-go theorem.

**M2-B — A paired witness/obstruction study.** For a stated resource budget,
produce a separating experiment and prove no weaker-access experiment can
separate the models, or prove an optimal gap bound attained by that experiment.
Include ancillas/adaptation only if covered by the theorem. Minimax separation
between model classes must quantify over nuisance parameters and establish
nonempty classes; separation of two selected states is a weaker result.

**M2-C — Parameterized physical leakage and recovery.** Extend typed access to
an explicit system/record/environment channel model, with justified reindexing
and partial traces. Distinguish inaccessible reversible leakage from an actual
irreversible channel. Optimize permitted recovery operations rather than simply
naming an attenuation multiplier 'recovery efficiency'. Check identifiable
parameters and whether competing classes overlap before promising separation.

**M2-D — Constrained AI authoring assistant.** Begin with assembly of checked
components from a documented grammar. Show the interpreted premises, model
class, access, quantifiers and target observable before certification. Separate
unsupported input, inconclusive search, proved proposition and counterexample.
A counterexample refutes a universal statement, not every claim about a model.
Do not silently introduce axioms or weaken a claim to obtain a proof. Display
source-to-formalization differences for human semantic review. Evaluate on
held-out tasks and deliberately ambiguous/incorrect claims, not only demos.

Exit requires an independent scientific comparison with prior art. If the first
candidate reduces to a known trace-distance result, publish it as a baseline and
move to an explicitly motivated harder model. Do not rebrand it as new physics.

## M3: valid conclusions from finite trials

**M3-A — Statistical contract.** Define the null class, setting distribution,
trial filtration, independence or memory assumptions, detection/event-selection
rules, stopping rule and nuisance bounds. Start from established Bell statistical
methods; prove the relevant test-factor or supermartingale conditions for the
chosen null. Exact probabilities, empirical frequencies and statistical bounds
must remain distinct types/records.

**M3-B — Checked analysis.** Certify a computable rejection bound with numerical
rounding controlled. Handle data-driven experiment/test selection through sample
splitting or a proved predictable adaptive procedure. Failure to reject is not
truth or membership. Guarantee concerns type-I error under the null, not the
posterior probability that an ontology is true. Ordered trials may be required;
aggregated counts alone do not justify arbitrary memory-sensitive analyses.

**M3-C — Public-data reproduction and prospective design.** Choose a dataset
with sufficient metadata and permissions, reproduce a published analysis, and
explain any discrepancy. Record source hashes and preprocessing. Then optimize
expected distinguishing power subject to physically motivated resource/noise
constraints, and issue a prospective analysis protocol for external review.
Lean cannot certify apparatus calibration or data authenticity from a CSV alone.

## Reuse infrastructure before extending it

Before adding linear algebra, finite quantum states, POVMs, channels, or tensor
operations, inspect the pinned mathlib and Lean-QIT sources and check relevant
upstream work, including Lean-Quantum. Record the searched declarations, version,
and any missing capability in the implementation PR. Prefer an existing theorem
or a thin adapter. A different upstream name or representation is not by itself
a reason to duplicate the mathematics.

New local infrastructure needs a concrete gap: for example, a computable exact
evaluator with a proved connection to upstream semantics. Keep such code small
and explain why adaptation is insufficient. Compare dependency compatibility,
proof assumptions, maintenance and migration cost before adding another library;
do not silently upgrade the pinned Lean/mathlib toolchain. Our focus is physical
assumptions, access-relative comparison, experiment search and scoped reporting.
This gate does not require rewriting already checked code without a benefit.

## Engineering and review gates for every increment

- One short adopter example using public imports and the normal audited exporter.
- Positive edited-input test; negative misleading-input test where relevant.
- Proof-carrying values, explicit quantification domain, orientation and existence.
- Full Lean gate and axiom whitelist; no sorry/admit/native_decide or silent axioms.
- Supported Python versions and committed report regeneration in CI.
- Record exact base/head and inspect every open dependency before starting a PR.
- Independent increments branch from main; dependent increments use a short stack.
  Merge predecessor changes forward, retain tests/docs, and require checks on new heads.

## References and novelty boundaries

- Bong et al., *A strong no-go theorem on the Wigner's friend paradox*,
  https://arxiv.org/abs/1907.05607v4 — scientific baseline, not a claim that this
  first increment formalizes the entire paper.
- Krenn et al., *Automated Search for new Quantum Experiments*,
  https://arxiv.org/abs/1509.02749 — automated experiment design already exists.
- Ren et al., *MerLean: An Agentic Framework for Autoformalization in Quantum
  Computation*, https://arxiv.org/abs/2602.16554 — agentic quantum autoformalization
  already exists; scientific semantic fidelity still requires review.
- Zhang, Glancy and Knill, *Asymptotically optimal data analysis for rejecting
  local realism*, https://arxiv.org/abs/1108.2468 — established memory-aware
  analysis to build on, with assumptions that must be re-established for LF.

See [Prior art and reuse decisions](PRIOR_ART.md) for the additional literature
assessment and the distinction between verified sources and unverified leads.
These references establish precedents, not an exhaustive novelty search.
