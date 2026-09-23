# Consensus records: access accounting

This increment makes the consensus program explicitly access-relative.

An `AccessModel` separates record fragments into:

- **accessible** fragments under the superobserver's coherent control;
- **inaccessible** fragments that remain outside that control;
- a recovery efficiency for the laboratory operation.

Only the inaccessible fragments enter the residual branch-overlap product.

## Exact access law

If one hidden record has overlap r and is moved into the accessible set, then

[
  V_{\rm before}=r\,V_{\rm after},
  \qquad
  \Delta_{\rm before}=r\,\Delta_{\rm after}.
]

So access to a fragment is not represented by an arbitrary "recovery bonus";
it removes exactly the decoherence factor associated with that fragment.

## Perfect-record limit

A perfectly distinguishing inaccessible record has overlap zero. Therefore:

- one such hidden record forces the fringe to zero;
- recovering the final such record with perfect laboratory recovery restores
  the ideal 1/2 fringe;
- if every remaining inaccessible fragment is a perfect record, a positive
  fringe implies the inaccessible list is empty.

This is the ideal all-or-nothing version of the later redundancy threshold:
for perfect durable copies, Wigner must coherently control **every** surviving
copy to restore interference.

## Scope and novelty

This is still an effective independent-record model, not yet an N-register
Hilbert-space theorem. It should be treated as access-accounting infrastructure,
not a new Quantum Darwinism result.

The recent Maity--Onggadinata--Koh QEC/Quantum-Darwinism tradeoff means generic
"redundancy versus recovery" is already occupied prior art. The foundations
target here is narrower: friend records, explicit read/reverse controls, and
subset access. The next increment should replace these overlap lists by a typed
system + friend + finite environment state and prove that tracing inaccessible
fragments produces the same access law.
