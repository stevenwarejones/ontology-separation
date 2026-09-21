# Matrix completion, ontology slices, and experimental evidence

## What changed

The 14×7 matrix now contains 24 results under native model definitions and 74
conditional results under explicitly added laws. The 24 native entries are five
bounds, seven witnesses and twelve toy predictions. No bundled cell is left as
an unexplained placeholder. **This is not 98 unconditional predictions from seven
complete universes.** Reusing the same conditional theorem across several columns
does not establish that those columns entail its premises.

All seven previously empty research directions now have checked restricted
subproblems. They retain their original IDs and broader research ambitions. This
revision does not claim to have solved seven fundamental open physics problems.

## New mathematical results in this implementation

- LF-compatible components can be restricted to a normalized two-setting Bell
  interface. The conditional PR component has inner CHSH score 4.
- Three-setting deterministic local mixtures embed in the LF component model and
  satisfy G≤6. This expands the setting domain explicitly.
- Real singlet measurements have proved setting-independent marginal probabilities.
- The three-setting no-signaling maximum of the genuine LF score is 10. A finite
  positivity certificate proves the upper bound and a normalized extremal behavior
  attains it. The exploratory linear program is not part of the trusted proof.
- LF contamination by an arbitrary normalized behavior gives G≤6+8ε. If the
  contaminating behavior is also no-signaling, G≤6+4ε. The latter is attained for
  every ε∈[0,1] by mixing explicit LF and no-signaling witnesses. These are mixture
  fraction bounds, NOT communication or causal-influence measures.
- Under an explicitly added partially Z-dephased singlet preparation,
  S(p)=(1502−1152p)/625 and G(p)=(1214656−476928p)/180625 for the selected bases.
  The exact violation thresholds are p<7/32 and p<65453/238464 respectively.
  These are thresholds for these witnesses, not optimized thresholds over bases.
- Joint binary records obey a triangle bound of 2. Three fair anticorrelated
  pairwise contexts attain 3 and cannot be jointly glued.
- One classical share of two fair parity-encoded bits gives success 1/2 for every
  randomized response; joint access gives 1. A passive invertible relabeling
  changes no event. This is not a quantum decoder theorem.
- X/Z order interference has minus-port probability 1−p/2 when the order control
  is dephased with strength p. It is gate-specific calibration, not certification
  of causal nonseparability. A known-gate ordinary circuit can mimic its statistic.
- CZ|++> is normalized and admits no complex product amplitudes. This pure-state
  obstruction is not a mixed-state witness or a gravity-mediator model.
- Public joint records obey P(A≠C)≤P(A≠B)+P(B≠C).

Every reportable declaration is registered in `Catalog.Evidence.resolve`; that
resolver and selected additional results are included in the transitive axiom audit.
Model authors can inspect the actual theorem statements, rather than trusting labels.
The display text is still prose, not a formal proof term.

## Why conditional extensions are necessary

The original columns mix correlation constraints and dynamics: Bell locality is
not a time-evolution law for memories; a two-qubit memory channel is not a law of
gravity. The added-law hypotheses are visible in every conditional cell and in
the extension cards. No model receives a new law merely because its name sounds
classical or quantum.

`Core.Extensions` provides setting restriction, a lightweight finite-distribution
wrapper, and independent-sector extensions. `free_binary_extension` constructs
an extension with any binary probability while retaining the exact base behavior.
This is a theorem about the specified independent-extension class, not a blanket
claim that every physical coupling leaves the new result free.

## Sixteen ontology profiles per experiment

`examples/index.html` links fourteen self-contained experiment pages. Every page
contains all sixteen require/reject combinations and interactive two-axis slices.
For any selected axes, four 2×2 panels cover all choices of the remaining two.
The static full table works without JavaScript.

The displayed axes are vocabulary slots. Their physical definitions must be supplied
by the model author. The checkbox for an operational bridge previews a conditional
reading of a theorem; it is **not** an implemented proof of a physical vocabulary
mapping. In particular:

- The Bell preview requires a bridge from the chosen realism/locality/measurement-
  independence predicates to membership in the implemented Bell-local class.
- The LF preview requires a bridge from the chosen global-truth/locality/measurement-
  independence predicates to the finite conditional friend model. LF's locality
  notion must not silently be replaced by Bell factorization.
- The P01/P10 preview requires global truth to supply the particular joint public
  record distribution used by those theorems.
- Realism→global truth is separately selectable, not imposed universally. With that
  extra implication a realism-required/global-truth-rejected profile is inconsistent,
  independently of the other two axes. Lean proves this conditional statement.

The generic `ProfileBridge.excludes` theorem transfers exclusions once `.sound` is
proved. No such physical bridge for the broad four English labels is manufactured
by the HTML. The UI therefore defaults to no profile exclusion. Negating a premise
removes that theorem's route; it does not establish compatibility or existence.

## Experimental evidence

The ledger distinguishes mathematical witnesses from literature measurements.
For B01 it records Hensen et al.'s 245-trial result S=2.42±0.20 and reported null-test
p=0.039. The probability is a null-test tail probability, not the probability an
ontology is true. It is not promoted to an absolute logical contradiction. The
reported uncertainty is not treated as a Lean-certified confidence interval.

For B02 it records Bong et al.'s proof-of-principle photonic observer-proxy result.
It does not generalize that result to controllable cognitive observers. No raw
experimental dataset or statistical reanalysis is bundled or verified here.

`Bound.excluded_by_lower` requires a justified lower bound on the true statistic.
The estimator from a finite sample is not sufficient by itself. A surviving model
is compatible with the evidence; an ontology is not proved true by surviving a test.

## References and novelty limits

- Bong et al., *A strong no-go theorem on the Wigner's friend paradox*, Nature
  Physics 16 (2020): https://arxiv.org/abs/1907.05607v4. Source of the LF inequality
  and the scope of the reported observer-proxy experiment.
- Hensen et al., *Experimental loophole-free violation of a Bell inequality using
  entangled electron spins separated by 1.3 km* (2015):
  https://arxiv.org/abs/1508.05949. Source of the reported measurement and p-value.
- Abramsky and Brandenburger, *The Sheaf-Theoretic Structure Of Non-Locality and
  Contextuality* (2011): https://arxiv.org/abs/1102.0264. Context for gluing and global
  section obstructions; this implementation is only a finite three-record example.
- Chiribella et al., *Quantum computations without definite causal structure*:
  https://arxiv.org/abs/0912.0195. Context for order control. Our two known gates and
  single statistic do not establish its general black-box-order result.
- Bose et al., *A Spin Entanglement Witness for Quantum Gravity*:
  https://arxiv.org/abs/1707.06050. Motivation only; our CZ subproblem does not
  implement its proposed gravitational apparatus or mediator assumptions.
- Beals et al., *Quantum Lower Bounds by Polynomials*:
  https://arxiv.org/abs/quant-ph/9802049. Explains why quantum-query claims require
  a different algorithm class from our classical one-query parity example.

These sources were consulted for scope and prior context. No comprehensive novelty
claim is made for the new formalizations or for elementary convex tradeoffs.

## Adoption and schema migration

Report schema 3 derives quantities and evidence kinds from `Core.Claim`.
Additional-law scope is independent of claim kind. All native bound cells have
satisfying models. Earlier report schemas are rejected; regenerate from Lean.
