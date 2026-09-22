# Automatic covered finite families

For a finite/discrete operational interface, adopters should not have to handwrite
the routine `Grid.covers` proof.

`ExactFinite.ProtocolFamily` is a nonempty supplied list of protocols.
When settings and outcomes have `Fintype` and decidable-equality instances,
`ProtocolFamily.grid` enumerates the complete

`protocol × setting × outcome`

grid and derives the coverage proof from that enumeration.

`certifyFamily backend family a b` then runs the existing exact checker and
returns its ordinary proof-bearing `CheckedResult`.

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
