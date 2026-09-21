# Local Friendliness: read or reverse the friends

This example completes the path from **explicit friend records** to a checked
Local Friendliness (LF) score and an operational assumption-class exclusion.
It uses coherent qubit memories as friends, not conscious observers.

After the [one-time setup](START_HERE.md#1-set-up-once):

```sh
ontology-separation new-scenario FriendStudy --backend local-friendliness -o examples/FriendStudy.lean
ontology-separation scenario-report examples/FriendStudy.lean -o examples/friends.html
```

Open `examples/friends.html`. The [checked-in view](../examples/local-friendliness-protocol.html)
contains the same eight predictions and expandable statements of the LF exclusion
and the fully dephased model's positive realization proof.

## What physically happens

There are four registers: Alice's system A, Bob's system B, Charlie's record C,
and Debbie's record D. C and D start at zero.

1. Prepare an entangled state of A and B.
2. Charlie copies A's Z value into C with CNOT(A→C); Debbie copies B into D.
   This is a coherent premeasurement. The records agree perfectly with the
   corresponding Z values; no collapse is assumed at this step.
3. Apply the selected noise to C and D, after recording and before Wigner's choice.
4. Independently choose a setting in each laboratory. **0 reads the record.**
   **1 or 2 reverses that laboratory's CNOT**, then measures its system in the
   corresponding alternative basis.
5. Sum over every unreported register. There is no postselection or discarding
   outcomes. Combine the resulting probabilities into the genuine LF statistic G.

Noise strength p implements (1-p/2)ρ+(p/2)ZρZ on the **record**. At p=1 the phase
information has been lost. Reversing the CNOT then does not restore interference.

## Read the source

`reference` supplies the source and local alternative bases. The source has
relative amplitudes **(-3, 4, -4, -3)** in order 00, 01, 10, 11. It is a singlet
rotated into the friends' local measurement frames; Lean proves that preparation
identity and agreement with all 36 probabilities of the existing LF witness.

The friends measure Z in these frames. Alice's alternatives are `(3,-4)` and Z;
Bob's are `(4,3)` and `(84,13)`. As in the Bell backend, a pair `(c,s)` specifies
normalized orthogonal columns `(c,s)` and `(-s,c)`. False is the first outcome
(+1), true the second (-1). These are basis coordinates, not angles in degrees.

```lean
open OntologySeparation.LocalFriendlinessRecipe

def changed : Recipe :=
  { reference with
    bob := { first := .x, second := .of 84 13 } }
```

To change the preparation, use `source := .of 1 0 0 0` for |00>, or another
nonzero rational amplitude vector. To change noise, use
`Law.recordDephasing charlieNumerator debbieNumerator denominator`.
The denominator is positive, each rate lies in [0,1], and invalid inputs fail.
The source and settings cannot inspect which law is selected. Setting 0 is
fixed by the protocol; it cannot quietly become another Wigner measurement.

## What the table establishes

| Charlie p | Debbie p | Reference G | What follows |
|---|---|---:|---|
| 0 | 0 | 1214656/180625 ≈ 6.724 | Excludes the LF conjunction for this modeled behavior |
| 1/4 | 0 | 1095424/180625 ≈ 6.064 | Still violates G≤6 |
| 1/2 | 0 | 976192/180625 ≈ 5.405 | This statistic no longer excludes LF |
| 1 | 1 | 2684416/4515625 ≈ 0.594 | Explicit classical-record model realizes the LF profile |

With Debbie coherent, the exact violation threshold is
**Charlie p < 65453/238464**. The completely dephased row has a separate positive
proof: a setting-independent mixture over four record pairs reproduces all its
probabilities and satisfies the profile. That conclusion is not inferred from
merely observing a score below 6.

The excluded finite-model profile requires **readable absolute records, conditional locality,
and independent preparation**. Outcome independence is left unspecified. The
result excludes the conjunction; it does not identify which assumption fails.
Being able to read a record in the actual read branch does not establish a
single classical record variable shared by all incompatible branches.

## How the proof is connected

`FriendProtocol` defines the full four-register copy, inverse, basis operations,
and partial readout. It proves record agreement, norm preservation and reversal.
`pure_probability_bridge` identifies every read/read, read/reverse,
reverse/read and reverse/reverse branch with an exact compact evaluator.
The record-Z identity makes the noise compression explicit. Normalization,
no signaling and the score bridge hold for every supported recipe and law.

`matches_reference` connects all 36 ideal probabilities to the existing LF
witness. `coherent_excludes_profile` uses the existing operational FriendRecords
bridge. `fully_dephased_realizes_profile` supplies an actual satisfying model
for the dephased row. All exported claims use the shared transitive axiom audit.

This is a verified finite real-amplitude protocol, not a general four-qubit
simulator or evidence about human observers. Other friend interactions, complex
amplitudes, imperfect reversal, inaccessible environments and conscious-agent
claims require additional models and proofs. No new laboratory result is claimed.

[Protocol design](design/LF_PROTOCOL.md) · [Bong et al.'s LF theorem](https://arxiv.org/abs/1907.05607)
