# Recover information by gaining access to a record

> **Two layers.** This advanced guide uses the general complex-quantum research layer.
> To run or compare supported experiments, start with the [recipe guides](RECIPE_GUIDE.md).
> Recipes have exact rational evaluators; the general complex-quantum semantics are noncomputable.
> Both layers use normalized behaviors and audited reports, but no checked recipe-to-quantum equivalence bridge exists yet.
> Custom research models require Lean proofs; see the [documentation index](README.md) for the beginner path.

**Question:** two models give the same statistics for every local experiment.
What new control lets us tell them apart?

[Browse the checked claims](../examples/record-access.html), or recheck them:

```sh
lake build
PYTHONPATH=python python -m ontology_separation.proof_report \
  examples/RecordAccessStudy.lean -o examples/record-access.html
```

## The physical example

Prepare a system and a record in the pure state
`(3|00⟩ + 4|11⟩)/5`. This is the result of coherently copying the computational
basis value of `(3|0⟩ + 4|1⟩)/5` into an initially blank record.

Compare two explicitly specified models:

- **Coherent:** preserve the joint state.
- **Dephased:** apply the computational-basis measurement channel and discard its
  classical outcome, represented by the resulting diagonal density matrix.

This models a specified loss of phase coherence. It is not a claim that every
objective-collapse theory has this dynamics, or that every environment is accessible.

| Available intervention | Coherent model | Dephased model | Proved conclusion |
|---|---|---|---|
| Any channel and finite measurement on the system alone | Same reduced state | Same reduced state | All local tests agree |
| Joint recovery, outcome `00` | 1 | 337/625 | Gap 288/625 |

The recovery first reverses the copy and then rotates the source back to `|0⟩`.
Every measurement outcome is retained; the success probability is not conditioned
on discarding failures. The rational amplitudes are exact.

## Follow the code

In `OntologySeparation/Experiments/RecordAccess.lean`:

1. `source` specifies amplitudes and proves normalization; `coherent` is its density state.
2. `dephased` applies a genuine Lean-QIT channel. `dephased_entry` derives its matrix entries.
3. `same_local_state` computes the partial trace and proves the two marginals equal.
4. `all_local_tests` applies the general adapter theorem, covering arbitrary local
   channels and finite POVMs. It does not merely check a hand-picked list.
5. `recovery` specifies the reversal matrix; `recovery_isometry` proves it is physical.
6. `recoveryReadout` uses the library isometry constructor to obtain a complete POVM.
7. `coherent_recovery` and `dephased_recovery` prove the two probabilities from the Born rule.
8. `Protocol.localTest` and `.jointTest` carry different input register types.
   `Protocol.localOnly` accepts only the first, preventing mislabeled joint access.
9. `locally_equivalent` quantifies over the allowed protocol family. `separator`
   supplies the new protocol, outcome and positive gap; `joint_not_equivalent` follows.

## Adapt the question

Change the prepared states, access boundary, or joint measurement. The proofs of
normalization, local equality and separation must then be supplied or reused.
Simply changing a text label does not change the law. For a first adaptation,
choose a different rational normalized pair of amplitudes and derive its gap.

For a genuinely new law, define its state evolution as a checked quantum channel,
or use the theory-independent `ExperimentAccess.Predictions` interface if its
operational rules are not quantum. The latter still requires normalized behaviors.
The same experiment must be passed to both interpretations.

This example is a fully checked *minimal record-access separation*. It is not yet
a parameterized LF leakage experiment, a universal collapse test, a new laboratory
result, or an automated search for optimal experiments. The general quantum
adapter and access certificates are reusable foundations for those next questions.


## Proof-bearing comparison view

The same result is also packaged through the common comparison layer. See
[scoped comparison results](COMPARISON_RESULTS.md). `localComparison` binds the
local-only agreement proof to this model pair and prediction semantics;
`jointComparison` binds the recovery separator to the full-access predicate.
