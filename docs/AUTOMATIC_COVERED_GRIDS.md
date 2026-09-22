# Automatic covered finite families

For a finite/discrete operational interface, adopters should not have to handwrite
the routine `Grid.covers` proof.

`ExactFinite.ProtocolFamily` is a nonempty supplied list of protocols.
When settings and outcomes have Mathlib `FinEnum` instances,
`ProtocolFamily.grid` enumerates the complete

`protocol × setting × outcome`

grid and derives the coverage proof from that enumeration.

`certifyFamily backend family a b` then runs the existing exact checker and
returns its ordinary proof-bearing `CheckedResult`.

`FinEnum` provides an explicit finite enumeration together with a proof that it
covers the type. This is stronger data than an unordered `Fintype`: the list
must also reduce inside Lean so the audited exporter can inspect the checked
result. `Finset.toList` is noncomputable, and a compiled-only enumeration is
not sufficient for this exporter.

Protocols are visited in supplied list order; settings and outcomes follow
their `FinEnum` order. This makes the first reported separator deterministic
for those enumerations. Enumeration order does not change agreement over the
complete supplied family and is not a physical assumption.

Mathlib supplies instances for `Unit`, `Fin n`, products and sums. This module
supplies Boolean enumeration `[false, true]`. No decidable equality instance
is required for the protocol type.

For a new finite setting or outcome type, supply the enumeration once:

```lean
inductive Setting where | first | second
  deriving DecidableEq

instance : FinEnum Setting :=
  FinEnum.ofList [.first, .second] (by intro s; cases s <;> simp)
```

Lean checks that every constructor is included. The framework still derives
the entire protocol × setting × outcome coverage proof; adopters do not write
`Grid.covers`. Use concrete, kernel-reducible enumeration data rather than
classical choice when the result will be automatically exported.

## Scope discipline

The represented access predicate is **exactly membership in the supplied protocol
list**. An agreement result therefore means agreement across that supplied,
fully-enumerated family. It does not mean agreement for protocols absent from the
list or for a broader physical access class.

The constructor never accepts a free-form predicate plus an assumed coverage
proof. If a family cannot be reduced to the supplied finite protocol list and
finite setting/outcome types, this automatic-grid route does not apply.

## Discrete checker versus symbolic thresholds

This API is intentionally a **finite/discrete engine**. It must not be used to
claim a continuum has been scanned.

A statement such as "separation holds for every leakage parameter p below p*" is
a different proof problem. Continuous or parameterized robustness regions belong
on the symbolic theorem path: define the physical channel, derive its probability
formula, and prove the threshold inequality for the whole parameter range.

Keeping these engines separate prevents a finite enumeration result from being
misreported as a continuous robustness theorem.

## Adopter workflow

`examples/AutomaticComparisonStudy.lean` now supplies two models and one-element
protocol families, calls `certifyFamily`, and exports the resulting audited claims.
There is no handwritten `Grid.covers` proof in the adopter file. The downstream
Lake-project gate copies and executes that public example.
