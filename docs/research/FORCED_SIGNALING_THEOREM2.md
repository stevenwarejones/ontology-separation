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
- The measured-signaling tradeoff is implemented for the certified K=8
  completion, and the full completion family is now formalized explicitly.
  Lean proves there are 512 raw completions, that only three of the nine
  completion bits can affect a conditionally-local model's score, that the LC4
  target has value `4 + 2√2` under every completion, and that **no valid
  completion-specific tradeoff can have slope below 8**. Thus the paper's
  Corollary 1 optimality statement is kernel-checked. The finer per-completion
  slope spectrum `{8,10,12,14,16}` with its multiplicities remains a numerical
  result from the source reproduction scripts, not a Lean theorem.
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
4. [ForcedSignalingCompletions.lean](../../OntologySeparation/Experiments/ForcedSignalingCompletions.lean)
   formalizes all 512 raw completions, proves the six blind-setting choices drop
   out for conditionally-local models, proves completion-independent LC4 target
   value, and establishes global slope optimality `K ≥ 8` with the certified
   K=8 completion attaining the minimum. `stochastic_completion_globally_sharp`
   then lifts the same all-completions statement to the finite stochastic
   conditional-local class proved equivalent in `HiddenInfluenceStochastic`.
5. [ForcedSignalingTheorem2.lean](../../OntologySeparation/Experiments/ForcedSignalingTheorem2.lean)
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

## Directional and pairwise-invisible refinements

Propositions 1 and 2 are formalized separately in
[FORCED_SIGNALING_PROPOSITIONS.md](FORCED_SIGNALING_PROPOSITIONS.md).
That extension kernel-checks the directional tradeoff
`S4^op <= 6 + 4 deltaA + 4 deltaD`, exact one-sided directional attainment,
and three LC4-matching models whose every one- and two-party recipient marginal
is non-signaling while the surviving full-record change is a pure parity shift.
The finite stochastic directional bound is also lifted through the existing
determinization theorem.

Fixed-layout spacetime geometry and the finite causal bridge are formalized
below. Lemma 2 and collectibility belong to the separate timing/collection
extension. Finite-sample statistical claims remain outside this bridge.

## Verification

Run `lake exe cache get`, then `sh scripts/check.sh`. The latter builds the
library and tests, regenerates the axiom snapshot, and checks the report layer.
The [audit registry](../../Tests/Audit.lean) includes the public proof-chain
roots; [its generated output](../AXIOM_AUDIT.txt) records their transitive
axioms. No external numerical evaluation is used as a proof rule.

## White-noise robustness

The exact cluster-point theorem now has a separate
[white-noise robustness guide](NOISY_LC4_FORCED_SIGNALING.md). For visibility
`p`, Lean proves the exact minimum
`max 0 ((p * (4 + 2√2) - 6) / 8)`, including explicit attaining models and
checked values at 90% and 95% visibility.

## Preferred-frame physical bridge

See [the definitions audit](FORCED_SIGNALING_DEFINITIONS_AUDIT.md) for the
physical scope and the distinction between conditional locality and NS ∩ CL.
`VCausal.Protocol.full_behavior` preserves every four-party probability.
`VCausal.realizable_iff_early` identifies the exact remaining finite early-law
realizability obligation. `ForcedSignalingVCausal.lc4_AD_uniform` supplies the
LC4 early law, and `vcausal_exact_forced_signaling` gives an attaining finite
classical protocol on any qualifying fixed layout, for all three early orders.
These are fixed-layout statements. Cross-timing consistency and accessibility
require their separate protocol and geometric hypotheses. No infinite-hidden-
variable or general field-dynamics equivalence is claimed.

`vcausal_optimal_completion_globally_sharp` also transfers the all-512-completion
slope optimum using a **realized** LC4 witness. This sharpness conclusion is
proved separately from the lower-bound transfer. The white-noise result in this
bridge is a lower-bound corollary; a physical exact noisy curve is not asserted.

The finite NS ∩ conditional-local exclusion is explicitly stated as
`ForcedSignalingVCausal.conditional_local_nonsignaling_exclusion`.
`VCausal.SupportedProtocol.full_behavior` also covers finite-support laws
on arbitrary ambient hidden types without requiring a global `Fintype`.
