# General measurable hidden laws

`VCausalMeasure.lean` removes the finite-support restriction for **measurable
deterministic response-table protocols** on the fixed LC4 causal graph.
`ForcedSignalingMeasures.lean` transfers the quantitative and collectibility
results to that class.

A `MeasurableProtocol order Ω` contains an arbitrary measurable space Ω, a
probability measure μ, a measurable map from Ω to `Early → Strategy`, and an
almost-everywhere early causal-order constraint. There is one μ for all setting
choices. B and C read only their own late setting from the selected table.
Neither a score inequality nor agreement with quantum data is a structure field.

The finite type of complete response tables provides an exact quotient of the
hidden space. `tableLaw` is the pushforward of μ; each finite atom receives its
fiber's probability. Positive atoms obey the causal law because the bad-table
set has measure zero. `full_behavior` proves equality with the original event
measure for every early setting, late setting and full four-party outcome.
`observationallyEquivalent` states the same equality at the behavior interface.
Null hidden states are allowed to have arbitrary tables.

The reverse embedding takes a finite protocol to a probability measure.
`Protocol.toMeasurable_toModel` proves that embedding and recompression preserve
the entire packed strategy model. Consequently the previously certified finite
witness attains the minimum in the general-measure class too; sharpness is not
inferred merely from a one-way inclusion.

| Result | Public theorem in `ForcedSignalingMeasures` |
|---|---|
| Slope-8 tradeoff | `tradeoff` |
| LC4 lower bound | `lower_bound` |
| Exact minimum with an explicit attainer | `exact_minimum` |
| Optimal slope across every completion | `coefficient_lower_bound_all_completions`, `optimal_completion_globally_sharp` |
| Noisy LC4 lower bound | `noise_lower_bound` |
| Collectible signal with `BothCollectible` | `collectible_signal`, `noisy_collectible_signal` |
| Restoration-layout headline lower bound | `physical_main_lower_bound` |

The theorem statements use the compressed model for matching, scores and TV.
This is an exact change of representation, justified by full-behavior equality,
not an approximation or a restriction to finitely supported μ.

The tests use Lebesgue measure restricted to [0,1], split into two response
tables at 1/2, and compute both weights as exactly 1/2. Negative tests rule out a
backwards early table on a set of positive measure. The new public theorem roots
are registered in `Tests/Audit.lean` for the transitive axiom audit.

## Scope

This closes the arbitrary-probability-space question for measurable deterministic
response tables with the stated shared-law, local-response and early-order
assumptions. It does not derive screening-off from a finite propagation speed.
Nonmeasurable response maps are excluded. Spacetime results retain their rational
1+1-dimensional, fixed-preferred-frame hypotheses.

A general measurable Markov-kernel formulation and its randomization theorem
remain open in this port. In particular, the theorem does not silently supply a
measurable shared-randomness dilation for arbitrary local stochastic kernels.
The existing finite stochastic determinization results remain available. The
common timing-intervention mechanism is still proved for the finite class;
only its fixed-layout headline's lower-bound component is extended here.
