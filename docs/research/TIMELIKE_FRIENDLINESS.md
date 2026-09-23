# Timelike Friendliness: factorization benchmark

Mukherjee and Hance's 2026 Causal Time-Symmetric Friendliness theorem derives a
CHSH-form inequality from four named assumptions:

- Absoluteness of Observed Events (AOE),
- Axiological Time Symmetry (ATS),
- No Retrocausality (NRC),
- Screening via Pseudo Events (SPE).

The paper shows that these assumptions yield a pseudo-event-conditioned
factorization and hence |CHSH| <= 2; quantum theory reaches 2 sqrt(2).

This increment formalizes **the factorized consequence**, not the four semantic
assumptions themselves.  For each finite pseudo-event state lambda, Alice and Bob
have screened binary response means in [-1,1].  The public correlators are their
finite convex mixture.  Lean proves:

1. every conditional response obeys CHSH <= 2;
2. every finite pseudo-event mixture obeys CHSH <= 2;
3. the class is nonempty and the ceiling is attained;
4. the repository's existing exact rational singlet behavior violates the bound.

That gives us a checked reproduction target for the next adversary pass.

## Next pass: assumption decomposition

The next PR must encode AOE, ATS, NRC and SPE separately and prove their bridge to
this factorized class.  Only after that bridge exists do we run premise deletion:

- remove AOE while retaining the operational pseudo-event construction;
- remove ATS;
- remove NRC;
- remove SPE;
- search explicit finite countermodels for each deletion.

The paper itself already shows that full AOE can be weakened and that removing
absoluteness of the individual pseudo-events can allow the algebraic CHSH maximum.
So the objective is not to force an artificial four-premise minimal core; it is
to discover the smallest faithful core supported by explicit countermodels.
