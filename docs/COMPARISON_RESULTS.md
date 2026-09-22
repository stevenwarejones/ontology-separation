# Scoped comparison results

The comparison layer reports exactly one of two proof-bearing conclusions for a
fixed pair of models, prediction semantics, and access predicate:

- **Agreement over the stated access domain** — a proof of
  `ExperimentAccess.Equivalent predict allowed a b`.
- **Verified separating experiment** — an `ExperimentAccess.Separator` whose
  protocol is proved allowed and whose positive probability gap is checked.

The underlying notions remain in `ExperimentAccess`; `Comparison.Result` only
packages them so reports cannot detach a verdict from the models, semantics, or
access scope that its proof actually concerns.

## Supplied experiment families

A finite or otherwise supplied family is represented separately by
`Comparison.FamilyAgreement`. The certificate includes one member of the family,
so an empty family cannot be presented as a substantive checked family.

Agreement on a supplied family is **not** automatically agreement over a broader
allowed domain. Promotion requires a `Comparison.Coverage family allowed` proof
showing that every allowed protocol is represented by the family.

This matters even when the family was exhaustively enumerated by external code:
the coverage theorem is what connects that enumeration to the domain named by the
result.

## Record-access example

`RecordAccess.localComparison` packages the existing theorem that the coherent
and dephased record states agree for every protocol satisfying
`Protocol.localOnly`.

`RecordAccess.jointComparison` packages the existing recovery separator under
full access. Both compare the same `RecordAccess.Law` values through the same
`RecordAccess.predict` semantics; only the access predicate changes.

The resulting claims export with distinct evidence kinds:

- `agreement`
- `separation`

The renderer derives these labels from the proof-bearing claim constructors. A
human-readable label cannot turn a theorem about one model pair or access policy
into a claim about another.

## What this does not do

This layer does not automatically search for a separator, decide arbitrary
real-valued quantum predictions, prove that a finite family exhausts an access
domain, or identify either state with an entire interpretation of quantum
mechanics. Those require separate evidence.
