# From the LF paper to a checked experimental conclusion

Start with `import OntologySeparation.Assumptions` and the runnable
[`LFPaperStudy.lean`](../../examples/LFPaperStudy.lean). Export it with:

```sh
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/LFPaperStudy.lean -o examples/lf-paper.html
```

## What the input means

`LFJoint.Table` is a nonnegative joint probability table at each selected pair of
settings. `prob (x,y) (c,d) (a,b)` assigns probabilities to Wigner outcomes `a,b`
and actual friend records `c,d`. Summing all outcomes and records gives one.
Summing just the records gives the observable `Table.behavior`.

The table is a mathematical extension postulated by the model class. Its existence
is not inferred from having a CSV of Wigner outcomes. In particular, records erased
by a reverse operation need not remain available for simultaneous readout.

## What to require

| Physical condition | Public definition | Meaning |
|---|---|---|
| Consistent friend readout | `LFJoint.Readable` | At setting zero, all probability for each record lies on the outcome agreeing with that record. |
| Independent prior records | `LFJoint.IndependentRecords` | The distribution of `c,d` does not change with either setting. |
| Conditional locality, with independent records | `LFJoint.Local` | Joint single-party marginals at fixed records do not change with the remote setting. |

`LFJoint.Admissible` requires all three. Settings `0,1,2` correspond to paper
settings `1,2,3`. Boolean `false` has sign +1 and `true` has sign -1.

## Why the definitions match

`conditional_probability` proves that on every possible record pair the normalized
response is the usual joint probability divided by the record probability.
`local_iff_conditional` proves that our division-free locality law is equivalent
to locality of these responses when records are independent. Nonnegativity and
normalization make the readable-outcome marginal condition equivalent to a delta
response: no probability remains for the opposite Boolean outcome.

On impossible record pairs, every joint entry is proved zero. We choose a normalized,
local, readable response there. `conditional_reconstruct` proves that multiplying
by the record probability recovers the original joint entry in both cases.
We never assume every record occurs or silently divide by zero.

`fromOperational` combines latent states sharing the same pair of records, and
preserves observable probabilities. `toOperational` reconstructs an operational
model with exactly four latent labels: the record pairs themselves. The theorem
`joint_iff_lf` proves both inclusions between this joint-table class and the existing
finite LF class. Extra latent labels therefore do not enlarge the observable class.

## Use the conclusion

```lean
example (j : OntologySeparation.LFJoint.Table)
    (h : OntologySeparation.LFJoint.Admissible j) :
    OntologySeparation.RealQuantum.genuineLF j.behavior ≤ 6 :=
  OntologySeparation.LFJoint.bound j h
```

`quantum_excluded` says the existing quantum witness cannot have such an admissible
extension. A violation excludes the conjunction; it does not select which law fails.
The exported report preserves these quantified theorem statements.

## Scope and review

This implements the finite three-setting, binary-outcome specialization of the
joint-event assumptions in [Bong et al.](https://arxiv.org/html/1907.05607v4),
section “Formalization of the Local Friendliness assumptions.” It reuses the
existing LF inequality and quantum witness. It does not enumerate all facets,
formalize arbitrary observers, certify finite-shot data, or settle scientific
priority. Lean checks the equations; expert review must still assess the translation
from physical concepts to those equations.

No new quantum infrastructure is introduced. The implementation reuses `Behavior`,
`FiniteDistribution`, `FriendRecords`, and the existing LF theorem, plus mathlib's
finite sums and real arithmetic. No dependency or toolchain upgrade is needed.
