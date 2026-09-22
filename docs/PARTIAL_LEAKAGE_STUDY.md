# End-to-end partial leakage study

This public study combines the finite exact checker, structured physical report,
and symbolic robustness theorem without conflating their scopes.

At the exact point

- visibility = 1/2;
- recovery efficiency = 3/4;

the study automatically checks the supplied calibration and recovery protocol
families. Calibration agrees. The recovery probe separates the effective laws
with exact gap 3/16.

Those statements are **pointwise checked results**.

The same file separately exports the symbolic theorem

`∀ v r ≥ 0, Δ(v,r) > 0 ↔ v > 0 ∧ r > 0`.

For the physical channel model, `v,r ∈ [0,1]`, so the separating region is
`(0,1] × (0,1]`; the upper edges are included.

That is a **region theorem**, not evidence obtained by enumerating finitely many
parameter values. The report keeps the ordinary theorem proposition alongside
the finite comparison cards.

The independent downstream adoption gate copies this public file into a separate
Lake project and requires both the exact 3/16 point result and the symbolic
theorem export to survive outside the repository source tree.

## Scientific status

This remains a certified-derivation showcase for the explicitly documented
effective attenuation model. The product law is realized by sequential
dephasing channels; it is not claimed to model every imperfect reversal. It is not presented as a new experimental
falsification result, a finite-shot statistical threshold, or a theorem about
all Wigner/friend models.


## Browse the committed report

The normal repository gate regenerates
[`examples/partial-leakage.html`](../examples/partial-leakage.html). That
committed snapshot is linked from the examples index and is therefore published
with the other GitHub Pages examples. Re-running the gate rechecks the Lean
source before replacing the snapshot.
