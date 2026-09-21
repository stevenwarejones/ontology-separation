# Check a whole model class

A single inequality is a useful exclusion test. Passing it does **not** prove
compatibility. This API makes the two conclusions require different evidence.

[Browse checked examples](../examples/model-classes.html), or run:

```sh
lake build
PYTHONPATH=python python -m ontology_separation.proof_report \
  examples/ModelClassStudy.lean -o examples/model-classes.html
```

## A membership witness

`generators : G → Behavior E` lists the behaviors generating the class.
`FiniteModels.Compatible generators target` means the target is a convex
combination of those behaviors. The distribution is independent of the selected
setting: it is a preparation mixture, not a setting-dependent choice of model.

A `Membership generators target` contains:

- `weights`: nonnegative weights summing to one.
- `reproduces`: a proof that the mixture reproduces **every setting/outcome entry**.

Open `examples/ModelClassStudy.lean`. It defines its own target and a 1/3–2/3
preparation independently, then checks the entire table. Change the weights but
leave the target unchanged: the proof must fail. Matching one reported score is
insufficient. Exporting `certificate.compatible` uses the existing audited report
boundary; the Python side cannot attach a membership label without that proof.

## An exclusion witness

An `Exclusion generators target` contains coefficients for a linear probability
statistic, a ceiling, a proof that **every generator** obeys the ceiling, and a
strict violation by the target. The library proves that all convex mixtures obey
the same bound and hence the target is outside the class. Equality at the ceiling
cannot produce an exclusion. Empty generator families cannot produce membership.

The shipped counterexample uses two settings and two outcomes. Each generator
reports a fixed bit regardless of setting. Their mixtures have identical outcome
probabilities under both settings. A device reporting its setting satisfies one
side of that equality but violates the other. Lean proves both the passed bound
and exclusion, making the “below the bound means compatible” mistake concrete.

## From one quantum model to a quantum model class

The record-access example compared a coherent state with one dephased state.
The new `recordClassExclusion` bounds the recovery success probability of **every
mixture of |00⟩ and |11⟩** by 16/25. The coherent input succeeds with probability 1,
so the same intervention excludes the entire specified correlated, fully dephased
preparation class. The reported bound includes an explicit member of that class,
so it is certified nonempty. The Born probabilities are calculated from the quantum adapter.

This does not exclude all collapse theories, every diagonal four-dimensional
state, or all LF models. The generator list is part of the mathematical statement.
To claim a particular ontology is exactly this convex hull, supply a separate
proof connecting its operational definition to these generators.

## What a search tool may do

A numerical optimizer can suggest weights or coefficients. Feed exact candidates
into the Lean constructors and prove their obligations. This stack provides the
verification boundary, not an LP solver or a proof that a searched list exhausts
an ontology. A failed search stays unknown. Neither a missing certificate nor
failure to violate one tested inequality yields a displayed compatibility claim.

See [experiment access](EXPERIMENT_ACCESS.md), [the record example](RECORD_ACCESS_GUIDE.md),
and [the implementation plan](design/UNIVERSE_SEPARATION.md).
