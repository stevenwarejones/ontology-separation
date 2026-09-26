# When is “the photon takes every path” testable?

A claim about paths becomes experimentally distinguishable when it changes an
observable prediction under a specified measurement procedure. Different
descriptions of the same amplitudes do not supply such a difference.

For finite propagation matrices K₁,…,Kₘ, matrix multiplication gives

\[
(K_m\cdots K_1)_{x_m x_0}
=\sum_{x_1,\ldots,x_{m-1}}
K_m(x_m,x_{m-1})\cdots K_1(x_1,x_0).
\]

The right side is a finite path sum; the left side is transfer evolution.
Identical final amplitudes give identical predictions under any common detector
rule applied to those amplitudes. This identity alone cannot decide whether the
summed paths are literally occupied. It presumes the same state space, propagation
and boundaries in both descriptions.

## What is checked in Lean

The [module](../OntologySeparation/Experiments/PathInterference.lean) treats an ideal
balanced interferometer with two routes, two phase settings (0 and π), and both
detector outcomes. Its five results are:

1. **Normalized probabilities:** coherent addition produces a deterministic bright
   output at each setting; either separately populated route gives probability
   1/2 at each detector.
2. **Equivalent descriptions:** the two-route path sum equals the elementary
   transfer formula at every setting/outcome. Their predictions agree under both
   modeled access protocols.
3. **A specified class is excluded:** every preparation mixture of the separately
   populated route behaviors has score 1/2; the coherent target has score 1. The
   excluded class is nonempty.
4. **An enlarged class contains the target:** an explicitly setting-dependent
   deterministic response table reproduces the coherent probabilities exactly.
5. **Access matters:** dephased access makes the coherent and dephased descriptions
   agree; retaining interference yields an exact probability gap of 1/2.

The general matrix identity above explains the setting; the module certifies the
specific two-route formulas, not a general continuum path integral. The
[checked report](../examples/path-interference.html) exposes the theorem statements.
Nine roots are registered in the repository's axiom audit.

## Scope and a route to stronger tests

There is no apparatus model or experimental-data certificate here. Excluding the
defined incoherent class does not exclude all definite-trajectory theories. The
context-dependent response is a lookup table, not a physical theory; “context” here
means the selected setting, not a demonstrated violation of a noncontextuality
inequality.

A real separation requires alternatives with different observable predictions
and explicit assumptions connecting them to an experiment. Contextuality tests
in the style of [Pusey (2014)](https://doi.org/10.1103/PhysRevLett.113.200401) and
[Kunjwal–Lostaglio–Pusey (2019)](https://doi.org/10.1103/PhysRevA.100.042116) offer
one direction. Their operational-equivalence and disturbance requirements must
be established; an unusual weak value or interference fringe alone is not enough.
No faster-than-light or backward-time propagation is established by this example.

Empirical studies of path-reality claims live in [path-reality-tests](https://github.com/stevenwarejones/path-reality-tests).
