# One evidence contract

Every numerical cell and theorem result uses `Core.Claim`. The constructors tie
exact values, ceilings, membership and exclusion to their proofs. `Claim.sound`
proves the proposition derived by `Claim.statement` for every constructor.
`Claim.kind` and `Claim.quantity` are projections of that same proof-bearing value.

`Reporting.Claim` reduces rational data and prints the actual proposition.
`#export_claim`, `#export_theorem`, `#export_scenario` and `#export_catalog` audit
their dependencies and use this shared claim exporter. The Python `evidence` module
validates and formats the same claim record in each view. Scope (native versus
additional laws) is separate from evidence kind, so a witness under extra laws
cannot visually become an unconditional prediction of a column.

The catalog uses live claims instead of theorem IDs plus result strings. Every
concrete noisy-singlet cell carries the instantiated parameter proof and the
identity for its actual score. Memory rates have one source used by both model
labels and interpretation dispatch. Every native bound in the shipped matrix has
a satisfying model for its actual class; existence is not inferred from a ceiling.

The numeric memory cells report exact rational matrix-interpreter outputs. They
remain restricted two-qubit model calculations. The common claim type does not
upgrade those dynamics into arbitrary Hilbert-space, observer or gravity models.
General symbolic theorems display their actual proposition, with assumptions intact.

The catalog JSON schema is 3 and the scenario envelope is v2. Earlier schemas are
rejected: there is no second renderer, compatibility fallback or unaudited executable
report generator. Offline snapshots remain useful; they are generated exclusively
through checked exports and are not authenticated proof certificates.

## Model review boundary

No formal system can determine whether an author's definitions capture the intended
physics. Type-level guarantees bind claims to supplied definitions; vocabulary
meanings, applicability to an experimental setup and explanatory descriptions still
need scientific review. This is the same boundary for introductory and general APIs.
