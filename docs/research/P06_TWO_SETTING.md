# P06: two-setting calibration after the fixed-order adversary

The previous adversary result showed that the original P06 X/Z minus-port
probability is exactly reproduced by a fixed-order X-then-Z circuit for every
input vector. Optimizing that one number therefore cannot establish indefinite
causal order.

This increment asks the next adversarial question: can a slightly richer
observable table reject that same countermodel?

## Added setting

- setting 0: X/Z, where the two orders anticommute and the coherent minus port
  has weight equal to the input norm;
- setting 1: X/X, where the two branches are identical and the coherent minus
  port is exactly dark.

For a normalized input, the restricted fixed-sequence adversary reports norm 1
for both settings, while the coherent-control circuit reports X/Z -> 1 and
X/X -> 0.

Lean proves the original setting is still exactly mimicked, but the added X/X
setting separates the two implementations by an exact unit gap.

## Boundary

This is **not** yet a witness of indefinite causal order. It rejects one explicit
fixed-sequence adversary, not the full class of causally ordered processes.
A general definite-order model could have setting-dependent instruments or
classical post-processing and may reproduce this two-setting table.

The next step remains the important one: define that full finite adversary class,
enumerate its behavior hull, and search for a facet that the coherent friend
protocol violates.
