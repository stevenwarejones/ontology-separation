# P06 structured adversary: the current fringe is insufficient

P06 currently contains an X/Z order-interference calibration. Before searching
for a Causal-Order Friendliness theorem, the structured-adversary workflow asks
whether a definite-order model can reproduce the proposed witness.

It can.

The checked adversary applies X then Z in an ordinary fixed order. Both gates
preserve the input norm, while the existing coherent-order minus-port statistic
is exactly the same norm. Therefore the two scalar probabilities agree for
**every input vector**.

This is stronger than saying a particular test point is ambiguous: there is no
input choice within the current scalar statistic that separates these two
implementations.

## Consequence for the research program

Do **not** optimize the existing fringe and call a larger value evidence for
indefinite causal order. The next P06 increment must enlarge the observable
interface or the admissible-process definition.

The next search should:

1. define the finite definite-order process class, including allowed ancillas,
   control access, adaptation and classical communication;
2. expose a multi-setting/multi-outcome table rather than one scalar fringe;
3. enumerate/propose facets of the definite-order hull;
4. verify every candidate facet in Lean;
5. construct the quantum/friend witness;
6. run premise-deletion adversaries for causal definiteness, record absoluteness,
   agency, and any screening/no-fine-tuning assumption;
7. only then perform a novelty audit against quantum-switch and causal-inequality
   literature.

This PR is a negative result, but it is exactly the kind of adversary rejection
the discovery workflow is intended to produce.
