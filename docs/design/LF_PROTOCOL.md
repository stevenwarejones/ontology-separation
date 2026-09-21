# Local Friendliness protocol and proof boundary

This extends PR #4 with a specific extended Wigner's-friend experiment, not an
arbitrary four-qubit circuit simulator. Two system qubits and two initially blank
record qubits are explicit. Each friend coherently copies its system's Z value
into its record by CNOT. A laboratory either reads that record (setting 0), or
undoes its own CNOT and measures its system in one of two real bases (settings
1 and 2). The unreported registers are summed out; there is no postselection.

## Exact representation

The reachable premeasurement subspace has amplitudes
`F(a,b,c,d) = v(a,b)` when `c=a` and `d=b`, and zero otherwise. Prove this encoding
preserves norm, copies perfectly readable records, and is reversed by the two
CNOT permutations. Define those permutations and the measurement maps on full
four-register amplitudes, then prove all observable probabilities agree with
the compressed two-qubit representation. Compression is a proved isometry,
not an omitted record or an assumed probability table.

Local record dephasing between friend and Wigner is the convex random-Z channel.
A record Z on this subspace equals a system Z before encoding; prove that identity.
Thus the compact mixture representation faithfully handles both coherent records
and irreversible record dephasing. A Wigner can reverse the copy but cannot erase
the ensemble's lost phase information.

## Scientific result

Choose rational source amplitudes and relative readout bases that reproduce all
36 probabilities of the existing three-setting LF witness. Connect the resulting
score to the genuine bound G≤6 and the operational FriendRecords profile bridge.
A read outcome is accessible in its actual branch; this does not supply a common
classical record variable for every incompatible branch. Above 6 excludes the
conjunction of readable absolute records, conditional locality and independent
preparation, not one chosen assumption in isolation.

Friends here are coherent qubit records, not conscious agents. The result is a
finite mathematical model and a formal bridge, not a new laboratory violation.
Reference: Bong et al., https://arxiv.org/abs/1907.05607 (LF experiment and inequality).

## Acceptance

Prove record copying, reversal, normalization, readout reduction, no signaling,
reference-probability agreement, and LF/profile exclusion. Check coherent/noisy/
fully dephased examples and mixed read/reverse branches. Add a proof-free starter,
shared checked report, negative-input checks, and the normal full verification gate.
