# Literature audit: LF readout and partial environment recovery

Checked 22 September 2026 against PR #29, `cdf577c0a53b64ac83bb22321873de635fdf66bb`.
This is a targeted primary-source sweep, not a claim of exhaustive priority clearance.

## Verdict on 65453/361250

The number is a target-specific corollary of a known relaxed-LF inequality.
It should not be advertised as a new universal physical tolerance.

Our joint-table theorem is `S ≤ 6 + 4(δA + δB)`. The checked target has
`S = 1214656/180625 ≈ 6.724739`. Consequently any admissible extension requires

```
δA + δB ≥ (S - 6)/4 = 65453/361250 ≈ 0.1811848.
```

If each mismatch is bounded by the same ε, this score excludes the class for
`ε < 65453/722500 ≈ 0.0905924`. The inequalities are strict at exclusion.
Above the threshold, this argument becomes inconclusive; it does not construct
an extension for the whole quantum table. The sharp total-budget construction
attains the score with other, potentially nonquantum, tables.

**Direct precedent:** Moreno, Nery, Duarte and Chaves,
[Events in quantum mechanics are maximally non-absolute](https://quantum-journal.org/papers/q-2022-08-24-785/pdf/),
Quantum 6, 785 (2022), Eq. (8) and Sec. 3, give relaxed agreement and
`Ω₁(ε)=6+8ε`. Their printed `I₁` matches our `genuineLF` under the setting
permutation `(paper 2,1,0) → (code 0,1,2)`. The read setting maps to zero.
Their non-absoluteness coefficient minimizes `2ε` with a common per-side
ceiling. Our actual total mismatch is not that minimization. PR #29 supplies
a Lean derivation in our semantics, total-budget sharpness and exact arithmetic.
It does not establish scientific novelty of the relaxed bound.

## Three different experimental questions

1. **Does the read setting actually read the friend's memory?**
   [Proietti et al. (2019)](https://arxiv.org/html/1902.05080v2), Discussion and
   the supplementary loophole section, explicitly identify the additional
   requirement that the read observable operate on the memory rather than an
   unintended joint system-memory observable. This is a Bell-Wigner predecessor,
   not the genuine-LF theorem. A small electronics bit-flip estimate alone does
   not establish this measurement identification.
2. **Does calibration bound the same disagreement used in the theorem?**
   [Extended Wigner's Friend Scenarios with Agent-like Observers on Quantum
   Computers (2026 preprint)](https://arxiv.org/html/2609.12527v1), Sec. VII.3
   and Appendix C, estimate disagreement using a modified preparation circuit
   and expressly do not claim a strict upper or lower bound. Its one-friend
   inequality has a different normalization. Transfer assumptions and finite
   statistics remain necessary before using any calibrated bound in #29.
3. **Does a reversible record qualify as an observed event?**
   [Bong et al. (2020)](https://arxiv.org/html/1907.05607v4) distinguish their
   theory-independent LF conclusion from an objective-collapse interference
   test. [Towards violations of Local Friendliness with quantum computers](https://arxiv.org/abs/2409.15302)
   explores increasing branch complexity. Neither register size nor a verified
   readout probability automatically resolves that interpretive question.

The `0.1811848` total budget is not a detector efficiency, a white-noise
fraction, a confidence level, or an inaccessible-environment fraction. The
roughly 18.3% white-noise tolerance discussed for a different optimized strategy
in Bong et al.'s supplement is a different quantity despite the similar number.

## Recovery literature changes the flagship contract

| Primary source | Existing result relevant here | Consequence for this project |
| --- | --- | --- |
| [Gregoratti & Werner, Quantum Lost and Found (2003)](https://arxiv.org/abs/quant-ph/0209025) | Environment measurements and classical correction can reverse suitable noise. | Do not equate recovery with coherent joint access. |
| [Buscemi, Chiribella & D'Ariano, Quantum erasure of decoherence](https://arxiv.org/abs/quant-ph/0611070) | Environment-assisted erasure gives strong recovery results for low-dimensional decoherence. | Include environment measurement plus classical feedback as an allowed-control competitor. |
| [Buscemi, Channel correction via quantum erasure](https://arxiv.org/abs/quant-ph/0611111) | Relates imperfect erasure to corrected entanglement fidelity. | Keep recovery fidelity, event-probability gap and LF disagreement as separate quantities. |
| [Miatto et al., The optimal bound of quantum erasure with limited means (2014 preprint)](https://arxiv.org/pdf/1410.2313) | Optimizes recoverable coherence under partial access, without postselection; treats low-dimensional accessible fragments. | Partial access plus an optimal bound is already established territory. |
| [Miatto et al., Recovering full coherence in a qubit by measuring half of its environment (2015 preprint)](https://arxiv.org/abs/1502.07030) | Studies typical recovery versus accessible/inaccessible dimensions in random pure states. | A “half the environment” transition is not a universal threshold or a new target by itself. |

Our proposed contribution must specify a different operational question, such
as a uniform discrimination guarantee over uncertain models under a physically
restricted control class, with attainment, converse and finite-data inference.
The current two-branch benchmark is a verification baseline for that program,
not evidence of a new post-LF theorem. We found no reason to identify the
readout budget with a recovery parameter without a new bridge theorem.

## Implementation implications

- Retain #29's explicit prior-art attribution and conditional experimental wording.
- Require a shared physical preparation and an actual discarded tensor factor
  for partial access; a variable called “accessible fraction” is insufficient.
- State whether the result covers all tests, a constrained family, or one witness.
- Separate probability allowances from inferred calibration intervals and their
  failure probabilities. Keep statistical significance out of ideal score claims.
- Compare proposed novelty against both optimal erasure and quantum hypothesis
  testing, not only against LF papers. Independent physics review remains valuable;
  no researcher has been contacted as part of this audit.

See [the flagship contract](../design/PARTIAL_ACCESS_FLAGSHIP.md).
