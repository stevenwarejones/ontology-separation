# Flagship: which environment fragment is enough?

The target is a necessary-and-sufficient experimental resource threshold, with
an implementable experiment, a converse for its entire allowed class, and a
finite-data decision under explicit uncertainty assumptions. A successful
textbook quantum-eraser calculation does not complete that target.

The [literature audit](../research/LF_READOUT_LITERATURE.md) rules out presenting
partial access or a half-environment transition alone as new physics. It also
prevents importing #29's LF mismatch budget as a coherence parameter.

## Reviewable sequence

| Stage | Deliverable | Required before calling it complete |
| --- | --- | --- |
| Physical partial-access benchmark (this change, stacked on #32) | One accessible and one inaccessible environment fragment; exact optimum and uniform probability-allowance threshold for a normalized two-branch family. | A real partial trace, continuous parameter theorem, explicit attaining POVM, full-test converse, nonempty worst-case family and boundary tests. |
| Restricted-control study | Shared preparation on `laboratory × accessible fragment × hidden remainder`; protocols with separate types for record-basis access, complementary measurements plus classical feedback, and coherent control. | The allowed-operation definition comes before the bound; no arbitrary global POVM silently admitted; no postselection without accounted failure outcomes. |
| Fragment selection under uncertainty | A specified correlated leakage family and fixed resource budget; choose which physical fragments can be accessed. Optimize the worst-case discrimination margin over that family. | An attaining protocol and matching converse; include two equal-size fragments with different information value. If a known erasure formula already solves it, say so and reassess the scientific target. |
| Finite-data decision | A prospective count-based test, calibration transfer model and separate calibration failure budget. | Explicit power/sample-size guarantees, trial-dependence scope, no optional stopping by default, no posterior-ontology claim. |

The LF stack #27–29 remains independent. #30–32 supply the full-access baseline,
Helstrom adapter and first conservative finite-shot rule; they do not already
solve the restricted-control or fragment-selection stages. Rebase stacks in
review order instead of duplicating their infrastructure.

## The non-textbook question to settle next

For two explicitly defined dynamical model classes, what is the smallest allowed
fragment/control resource for which **one fixed protocol** gives a positive
worst-case margin after the stated calibration allowances? Which resource below
that boundary has a physical worst-case model defeating every allowed protocol?

Use the quantifier order `∃ protocol, ∀ model in class`, not the weaker
`∀ model, ∃ protocol`. The latter can require knowing the answer before choosing
the experiment. Fragment number, Hilbert-space dimension, inaccessible-record
overlap and control cost are different resources; do not collapse them into a
single “percent access” slider.

The exact first correlated leakage/control family is a research choice still to
be made against the precedents. Do not label an unsolved optimization as a
verified result. A useful initial candidate is unequal, correlated environmental
records with a bounded measurement/feedback menu and a calibrated phase interval;
its challenge is to prove a converse without assuming the nominal phase is known.

## Adopter experience

1. Select two physical dynamical models and name the registers.
2. Choose the accessible fragment and supported control class.
3. Enter a physically justified parameter range and probability allowances.
4. Ask for a separating protocol or a scoped impossibility result.
5. Read a report showing both model probabilities, exact margin, quantifiers,
   access footprint and what calibration assumptions still need evidence.

Lean must derive report values and scope from the proof-bearing construction.
The user must never hand-copy the optimum into a report. A wrong normalization,
illegal register access, excessive tolerance or stale numerical claim must fail
before replacing the last checked artifact.

Reuse the pinned Lean-QIT state, partial-trace, channel, POVM, Helstrom and
trace-norm infrastructure. New code belongs in the physical model, allowed
protocols, optimization bridge and reports; avoid another quantum algebra backend.
