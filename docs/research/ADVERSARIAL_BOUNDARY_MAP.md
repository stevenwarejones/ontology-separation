# Adversarial boundary map beyond Local Friendliness

Status: scoping notes and calibration results. None of the reductions in this document is presented as a new foundational no-go theorem.

The purpose of this file is to record which deliberately simplified formulations are already too weak to support a Bell -> Local-Friendliness-sized next step, and what a stronger formulation must include before further optimization is scientifically meaningful.

## Summary

| Formulation tested | Checked outcome | Interpretation | Not yet ruled out |
|---|---|---|---|
| Operational-Friendliness score benchmark | two-premise reduced core is deletion-minimal | calibration of the structured-adversary API against a known theorem shape | a paper-faithful Operational/Noncontextual Friendliness circuit-and-equivalence bridge |
| P06 scalar causal-order statistics | one scalar is fixed-order mimicked; a second setting defeats that comparator; unrestricted setting-dependent reporting then mimics every scalar table | scalar settings are vacuous unless the implementation is calibrated across settings | a definite-order hull built from a shared finite instrument/process family |
| Reduced timelike 2222 factorization | three operational consequence laws give CHSH <= 2 and embed into ordinary Bell screening-off | the reduced model has discarded the distinctive time-symmetric/pseudo-event structure | a model retaining the paper's asymmetric temporal and pseudo-event semantics |
| Passive nested observers | every finite passive copy depth has exactly the ordinary finite LF behavior class | copying an existing record adds no new experimental constraint | active outer read/reverse/interference or meta-record operations |
| Locality-free shared facts | shared context-independent facts plus faithful perfect-anticorrelation contexts reduce to the ordinary triangle marginal-gluing obstruction | this benchmark is contextuality, not a distinct friend-specific theorem | locality-free scenarios with explicit friend read/reverse, persistence, or intervention semantics |

"Not yet ruled out" means only that the corresponding stronger model has not been excluded by the checked adversary in this repository. It is not an assessment of promise or novelty.

## 1. Calibration: reduced Operational Friendliness

`OperationalFriendlinessBenchmark.lean` is a deliberately reduced calibration example. It represents an absolute-event premise by Bell/Fine-compatible latent behavior and the operational-agency hinge by equality of the latent and visible tables. The exact singlet target is excluded, and deleting either premise has an explicit target-realizing adversary.

This is not a formalization of the full theorem of Walleghem and Catani. Their Operational Friendliness theorem uses Absoluteness of Observed Events together with Operational Agency in an extended Wigner-friend construction:

- Laurens Walleghem and Lorenzo Catani, *An extended Wigner's friend no-go theorem inspired by generalized contextuality*, arXiv:2502.02461, https://arxiv.org/abs/2502.02461

Role here: **method calibration**, not a new result.

## 2. P06: scalar causal-order tests need calibrated instruments

The checked sequence is intentionally adversarial.

1. `CausalOrderAdversary.lean` proves the original X/Z minus-port statistic is reproduced exactly by a fixed X-then-Z order for every input.
2. `CausalOrderTwoSetting.lean` adds an X/X setting and thereby distinguishes the coherent construction from that one fixed comparator.
3. `CausalOrderUnrestricted.lean` then allows an arbitrary setting-dependent scalar report map and proves universal mimicry: every proposed scalar table is represented exactly.

The last step is deliberately broad. It formalizes why an admissible causal witness class has to be fixed before optimizing a statistic. Standard causal-nonseparability work likewise defines a restricted process/witness class rather than allowing arbitrary setting-dependent reports:

- M. Araújo, C. Branciard, F. Costa, A. Feix, C. Giarmatzi, and Č. Brukner, *Witnessing causal nonseparability*, New J. Phys. 17, 102001 (2015), https://arxiv.org/abs/1506.03776
- C. Branciard, *Witnesses of causal nonseparability: an introduction and a few case studies*, Sci. Rep. 6, 26018 (2016), https://doi.org/10.1038/srep26018

Required next formulation: one shared, calibrated finite instrument/process family across settings, with the definite-order convex hull fixed before facet search.

## 3. Timelike 2222: the reduced operational core is Bell screening-off

`TimelikeFriendliness.lean` reproduces the CHSH <= 2 consequence of a factorized pseudo-event model. `TimelikeOperationalCore.lean` separates that reduced consequence into stable pseudo-event weights, Alice screening, and Bob screening. The three laws are deletion-minimal inside the stated finite model class. `TimelikeBellCollapse.lean` then builds an ordinary Bell screening-off model from every model satisfying those three laws and preserves the CHSH score.

This is a scope result about the repository's **reduced abstraction**, not a claim that the full timelike theorem is merely Bell locality. Mukherjee and Hance's Causal Time-Symmetric Friendliness theorem is formulated using AOE, Axiological Time Symmetry, No Retrocausality, and Screening via Pseudo Events:

- S. Mukherjee and J. R. Hance, *Limits of absoluteness of observed events in timelike scenarios: A no-go theorem*, Phys. Rev. Research 8, 023066 (2026), https://doi.org/10.1103/1c6t-45g8

Required next formulation: preserve enough of the asymmetric pseudo-event and time-symmetry structure that the model no longer reduces to setting-independent Bell screening-off responses.

## 4. Passive nesting: observer depth alone adds nothing

`NestedFriendliness.lean` equips an ordinary operational LF model with an arbitrary finite number of outer records that simply copy the existing friend records. Lean proves, for every finite depth, that the nested theory equals OperationalLF and the finite LF theory.

This is expected from the definition: no new incompatible operation has been added. It should not be read as a general theorem that nested Wigner-friend scenarios are trivial.

Related work already shows that broad sequential friend scenarios can collapse back to Bell/LF structure, so nesting or repeated interaction by itself is not a novel resource:

- A. Utreras-Alarcón, E. G. Cavalcanti, and H. M. Wiseman, *Allowing Wigner's friend to sequentially measure incompatible observables*, arXiv:2305.09102, https://arxiv.org/abs/2305.09102
- L. Walleghem, Y. Yīng, R. Wagner, and D. Schmid, *Connecting extended Wigner's friend arguments and noncontextuality*, Quantum 9, 1819 (2025), https://doi.org/10.22331/q-2025-07-31-1819

Required next formulation: an active outer intervention such as read versus coherent reversal/interference, or a meta-record about alteration of the inner observer.

## 5. Locality-free benchmark: ordinary contextual gluing

`LocalityFreeFriendliness.lean` allows separate joint fact distributions for the AB, BC, and AC contexts and tests two laws: one shared context-independent joint fact distribution, and faithful reproduction of the perfectly anticorrelated context tables. Their conjunction is impossible, and the two-law core is deletion-minimal. This is the familiar triangle marginal-gluing obstruction in friend language. No spatial locality assumption is used.

This is intentionally a contextuality calibration. Existing work already gives much more systematic connections between extended Wigner-friend arguments and Kochen-Specker contextuality, including translations of possibilistic contextuality arguments and explicit compatible-measurement friend protocols:

- L. Walleghem, Y. Yīng, R. Wagner, and D. Schmid, *Connecting extended Wigner's friend arguments and noncontextuality*, Quantum 9, 1819 (2025), https://doi.org/10.22331/q-2025-07-31-1819
- L. Walleghem, R. Wagner, Y. Yīng, and D. Schmid, *Extended Wigner's friend paradoxes do not require nonlocal correlations*, Phys. Rev. A 112, 022212 (2025), https://doi.org/10.1103/n4hv-rlgj

Required next formulation: retain friend-specific operational structure absent from an ordinary marginal scenario, such as explicit read/reverse access, persistence under selected interventions, or alteration-awareness records.

## What these notes do and do not establish

They establish exact statements inside the model classes named in the Lean files. They do not establish philosophical necessity, experimental realizability of every adversary, or novelty of the underlying textbook/known reductions.

The structured-adversary lesson is methodological: before optimizing a proposed post-LF witness, first ask whether a stronger admissible adversary can reproduce it or whether the abstraction has collapsed to a known Bell/contextuality class.

The active research program should therefore focus on the extra structure listed in the final column of the summary table, not on strengthening these scoped-out benchmarks.
