# How much hidden which-branch information can this study tolerate?

This is the checked partial-access benchmark for the
[flagship program](design/PARTIAL_ACCESS_FLAGSHIP.md). It is a known two-branch
quantum-erasure family, with a sharp discrimination theorem and a safe editing
workflow. It is not yet the proposed correlated-fragment, restricted-control result.

## Run and edit

Open [the example](../examples/PartialEnvironmentStudy.lean) and change:

```lean
def study := PartialEnvironment.design (3/5) (1/20) (1/25)
```

The three numbers are the **minimum hidden-record overlap**, a downward
probability allowance for the coherent model, and an upward probability
allowance for the collapsed model. They are not percentages of environment
qubits and are not estimated confidence intervals.

```sh
PYTHONPATH=python python3 -m ontology_separation.proof_report \
  examples/PartialEnvironmentStudy.lean -o examples/partial-environment.html
```

The [checked HTML report](../examples/partial-environment.html) gives:

| Quantity at the physical worst-case endpoint | Exact value |
| --- | --- |
| Coherent probability | 197/250 |
| Collapsed probability | 1/2 |
| Best accessible binary-event gap | 36/125 |
| Gap after both allowances | 99/500 |

Changing the overlap floor to `4/5` changes the optimal gap to `48/125` and
margin to `147/500`. Changing it to `1/10` fails the required margin proof.
Negative allowances and overlaps outside [0,1] also fail. The exporter checks
the source and its dependencies before replacing the previous HTML.

## Physical preparation and access

Register order is `((L,A),H)`: laboratory logical branch, accessible environment
fragment, inaccessible environment fragment. The normalized source is

```
3/5 |0,0,0> + 4/5 |1,1> (r |0> + w |1>),   r² + w² = 1, r ≥ 0.
```

`Leakage.ofOverlap` constructs `w = sqrt(1-r²)` with a proof of normalization.
Lean traces out H to obtain the coherent accessible state. The alternative
applies a specified unread coordinate measurement to the accessible state.
This is a comparison of dynamics, not a declaration that an interpretation
of quantum mechanics predicts objective collapse.

L is a logical branch register; this benchmark does not separately model a
conscious observer or the system and friend memory. H is a real tensor factor,
not a display-only label. The type of an allowed test contains L and A but
cannot consume H. Losing A as well makes the states identical for every local
test, including arbitrary finite channels and readouts.

## What is sharp?

The readout accepts the projector onto `(|00>+|11>)/sqrt(2)` and keeps its
complement as the other outcome. No outcome is discarded. Lean proves

```
p(coherent) = 1/2 + 12r/25
p(collapsed) = 1/2
D(coherent, collapsed) = 12r/25
minimum equal-prior single-copy error = 1/2 - 6r/25.
```

The trace distance uses Lean-QIT's normalized convention. The converse includes
every finite CPTP preprocessing and complete binary POVM on L,A. Thus the
explicit measurement attains the upper bound; this is not a scan of a menu.
The theorem does not assert that implementing this projector is cheap or
requires entangling control. Environment measurement and classical feedback
are important competitors in the next restricted-control study.

For all normalized hidden records with `r ≥ r_min`, the **same** readout clears
the supplied probability allowances exactly when

```
loss + slack < 12 r_min / 25.
```

At equality there is no strict certified margin. Below that resource threshold,
an explicit physical endpoint model defeats the margin criterion for every
allowed test. The quantifier is one test working throughout the whole class.

## Keep the conclusion in scope

`Resolves` compares the two conservative probability endpoints. Failure says
those allowances do not certify a strictly separated binary-event margin.
It is not a proof that all noisy implementations are indistinguishable, that a
multi-experiment inference is impossible, or that the null model is true.
The allowances are independently supplied event-probability bounds; this change
does not derive them from a common physical error channel or calibration data.

The full-control benchmark optimizes within a partial tensor factor. It does
not optimize the number of fragments, access cost, recovery gate count or a
restricted feedback protocol. The [literature audit](research/LF_READOUT_LITERATURE.md)
explains why this benchmark alone is not a new scientific result.

For finite shots, the previous [statistical layer](FINITE_SHOT_GUIDE.md) can
consume a justified per-history null bound and power bound. This example does
not infer those trial-history premises from a single-copy Born probability.
