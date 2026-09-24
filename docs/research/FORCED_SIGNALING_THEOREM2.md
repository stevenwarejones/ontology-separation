# Forced-signaling Theorem 2: the LC4 proof chain

The target is the four-qubit linear cluster state
`CZ_AB CZ_BC CZ_CD |+⟩⁴`, with Li et al.'s two binary measurement settings at
each site. The admissible models reproduce its ABD and ACD no-blind-pair
marginals. Within the finite response-table class below, the minimum recipient
signaling is exactly `(√2 − 1)/4`.

This formalization accompanies the
[forced-signaling paper and exact certificates](https://github.com/stevenwarejones/forced-signaling).
It makes no novelty claim and has not been reviewed by a human domain expert.

## Physical and proof scope

- `HiddenInfluence.Model` uses finite deterministic response tables internally.
  `HiddenInfluence.StochasticModel` now starts instead from an arbitrary finite
  hidden state, stochastic A/D outputs, and conditionally independent local B/C
  response kernels. `selected_probability` proves that sampling both potential
  B/C responses and refining to deterministic strategies preserves every selected
  factorized probability. `behavior_prob_eq_factorized` then connects those
  probabilities to the exact packed `Behavior` used by the forced-signaling
  theorem. Recipient TV, signaling budgets and maximum signaling are preserved
  by determinization. The converse stochastic embedding preserves response-table
  weights, observable probabilities and signaling. This closes the **finite**
  stochastic-vs-deterministic representation gap for the theorem's observables.
  The Lean construction is stated for finite hidden spaces. For this finite
  setting/outcome scenario, standard convex-hull reasoning (Fine/Carathéodory-
  type determinization) implies that allowing arbitrary hidden spaces does not
  enlarge the observable finite behavior class; that standard extension is not
  formalized here. The result does not weaken the stated conditional-local
  factorization.
- Theorem 1 and this lower-bound argument use **one fixed operational
  completion** of the S4 witness, described in the
  [signaling guide](../SIGNALING_GUIDE.md). The paper's assertion that slope 8
  is optimal over **all completions** (Corollary 1 / the 512-completion
  spectrum) is **not in Lean**.
- Whether this response-table class is the appropriate formalization of
  finite-speed hidden influence is an interpretive question for experts.
- No human domain expert has reviewed the physical assumptions or results.

## Checked chain

1. [ForcedSignalingLC4.lean](../../OntologySeparation/Experiments/ForcedSignalingLC4.lean)
   defines the amplitudes and projectors in exact `ℚ × ℚ` arithmetic for
   `a + b√2`. It computes Born probabilities and marginal families directly.
   `ForcedSignalingLC4.cluster_normalized` checks the state normalization;
   `ForcedSignalingLC4.score_exact_real` gives the fixed-completion value
   `4 + 2√2`.
2. [ForcedSignalingLC4Witness.lean](../../OntologySeparation/Experiments/ForcedSignalingLC4Witness.lean)
   imports only the 59 nonzero response-atom indices and weights from the
   paper certificate. `model_abd_matches` and `model_acd_matches` check the
   marginals, while `tv_exact` and `signaling_exact` recompute recipient total
   variations. External LP slack variables are not assumed.
3. [HiddenInfluenceStochastic.lean](../../OntologySeparation/Operational/HiddenInfluenceStochastic.lean)
   proves finite stochastic conditional-local response kernels admit deterministic
   refinement without changing selected joint probabilities, and that every packed
   response model has a stochastic representative with the same observable behavior.
4. [ForcedSignalingTheorem2.lean](../../OntologySeparation/Experiments/ForcedSignalingTheorem2.lean)
   proves that those marginal constraints determine the completed score.
   `matches_score` and `lower_bound` connect the target to the physical
   [Theorem 1 tradeoff](../../OntologySeparation/Experiments/SignalingTradeoff.lean).
   `StochasticMatchesCluster`, `stochastic_lower_bound` and
   `exact_forced_signaling_stochastic_value` lift the result to arbitrary finite
   stochastic conditional-local hidden states: every LC4-matching stochastic
   model has signaling at least `(sqrt 2 - 1)/4`, and the explicitly constructed
   `stochasticWitness` attains equality.
   `exact_forced_signaling` states the universal lower bound and existence of
   an attaining model; `targetDelta_value` identifies the value with
   `(√2 − 1)/4`.

The existing `SharpOptimum` interface encodes a maximum. Accordingly, `optimum`
maximizes **negative signaling**, which expresses the required minimum without
reversing the theorem's inequality. The public theorem states the minimum
explicitly.

Every theorem name above is in the `OntologySeparation` namespace (the witness
and final-theorem module names give their respective subnamespaces).

## Verification

Run `lake exe cache get`, then `sh scripts/check.sh`. The latter builds the
library and tests, regenerates the axiom snapshot, and checks the report layer.
The [audit registry](../../Tests/Audit.lean) includes the public proof-chain
roots; [its generated output](../AXIOM_AUDIT.txt) records their transitive
axioms. No external numerical evaluation is used as a proof rule.
