# Consensus records: first adversary pass

## Question

When a friend-like record is copied redundantly into inaccessible fragments, what
is the weakest record condition that already makes a later laboratory-only
interference recovery impossible in the repository's checked dephasing model?

## Result in this increment

A list of independent record fragments is assigned overlap parameters in [0,1].
The residual visibility is their product. This is connected directly to the
existing `PartialLeakage` channel semantics, so the recovery fringe is

[
  \Delta = \frac{r_1 r_2 \cdots r_n\,\eta}{2}.
]

Consequently, **one perfectly distinguishing inaccessible record** (one overlap
equal to zero) forces the exact recovery gap to zero, no matter how many other
fragments exist or how good the laboratory recovery is.

The structured-adversary certificate then deletes that premise. With no hidden
copies and perfect recovery, the same checked physical backend gives gap 1/2.
Thus the premise is deletion-minimal inside this fixed laboratory-only mechanism
class.

## What this is not

This is not yet a new no-go theorem about Quantum Darwinism or observer-independent
facts. Multiplicative decoherence from independent records is standard physics.
The research value is that it gives the consensus program a checked base case and
a precise adversary target.

The next nontrivial step is **access-sensitive redundancy**: allow a superobserver
to recover selected fragments and search for the minimum inaccessible redundancy
that defeats every allowed recovery protocol. That requires a many-register
channel/access theorem, not just multiplying effective visibilities.

## Novelty gate

This PR is classified as a reproduction/baseline until a focused literature audit
shows that a later access-sensitive bound or minimal assumption core is not already
known. Quantum Darwinism already identifies redundant environment records with
operational consensus, and standard decoherence already relates distinguishable
environment states to loss of interference.


## 2026 novelty collision

A focused follow-up sweep found Maity, Onggadinata and Koh,
*Exact Tradeoff Between Quantum Error Correction and Quantum Darwinism:
An Information-Theoretic No-Go Theorem* (arXiv:2608.03944, August 2026).
They report an exact redundancy--post-recovery-fidelity tradeoff in a solvable
model and a model-independent information-theoretic no-go theorem.

Accordingly, a later result here must **not** claim novelty merely for showing
that redundant environmental records trade off against generic recoverability.
The distinct target is narrower and more foundations-specific: explicit friend
records, read-versus-reverse controls, typed subset access, and a
premise-deletion theorem connecting consensus facts to Wigner-style reversible
interventions.  The prior-art comparison must be repeated once that theorem is
mathematically fixed.
