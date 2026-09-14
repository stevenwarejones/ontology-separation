# Experiments and their research status

The framework includes four reference experiments and all ten original proposals.
An executable toy is not a solution to its motivating research problem.

| ID | Experiment | Initial implementation |
|---|---|---|
| B01 | Bell CHSH | Local-class bound, PR/no-signaling separation, quantum reference |
| B02 | Genuine LF, Bong Eq. 13 | Conditional no-signaling LF model, bound 6, exact singlet witness |
| B03 | Bell violation compatible with LF | Inner PR box has CHSH 4 but belongs to an LF component |
| B04 | Memory echo | Exact two-qubit density-matrix evaluation with parametric dephasing |
| P01 | Relative facts fail to compose | Protocol specification; composition semantics open |
| P02 | Conservation/public records versus reversal | Exact inaccessible-leakage toy; conservation-law theorem open |
| P03 | Hidden causal cost of absolute facts | Protocol specification; influence metric and tradeoff open |
| P04 | Coherent experimenter choices | Exact phase-control echo toy; full choice theorem open |
| P05 | Observer identity/subsystem boundaries | Protocol specification; physical access-map comparison open |
| P06 | Observations with indefinite causal order | Protocol specification; process interpreter required |
| P07 | Gravitating records | Protocol specification; explicit competing mediator models required |
| P08 | Computationally limited objectivity | Protocol specification; resource-bounded decoder class required |
| P09 | Observer versus reversible machine | Exact reversible-memory toy; no cognition model |
| P10 | Rules of shared reality | Protocol specification; operational composition rules required |

The original literature reevaluation favored P07 and P04, retained P06 and P09
conditionally, treated P10 as a design target, downgraded P01/P05, treated P02/P03
as supporting machinery, and set P08 aside as a breakthrough claim. Inclusion
here preserves the research question; it does not reverse that assessment.

## Bell conventions

Binary outcomes false/true mean +1/-1. CHSH is E00+E01+E10-E11. Locality is
membership in finite convex mixtures of deterministic local response tables,
not an assumed CHSH bound. No-signaling refers to marginal independence.

## LF conventions and physical meaning

The three settings use zero-based indices: 0 asks the friend; 1 and 2 are
alternative superobserver interventions. The friend outcome is fixed within a
conditional component. Its remaining 2x2 box is allowed to be any no-signaling
box; it is NOT forced to factorize or to have joint counterfactual outcomes.
Setting-independent mixing weights implement the common prior over components.
This follows the conditional formulation of Bong et al., Eqs. 3–6. The real
moment coordinates reconstruct nonnegative normalized probabilities; marginal
independence and certainty when asking the friend are separately proved.
The full philosophical-to-operational derivation is a modeling argument, not a
Lean proof about human observers. A finite mixture is the implemented scope.

The genuine inequality is:

G = -A0-A1-B0-B1-E00-2E01-2E10+2E11-E12-E21-E22 <= 6.

The explicit singlet measurement bases are real and rational. The probability
of a pair of outcomes is the squared determinant of their unit measurement
vectors divided by two, with a proved Born-amplitude identity and normalization.
This gives an explicit quantum submodel; it does not assert all quantum behaviors
have been characterized. The selected settings are a simple exact witness, not
a reconstruction of the 2020 experimental apparatus or measured data.

## Memory experiments

`Memory.Model` supplies a dephasing strength p in [0,1]. Preparing |+0>, copying
with CNOT, applying (1-p) identity + p dephasing to the recorded state, reversing
CNOT and reading X yields 1-p/2. With inaccessible leakage before reversal the
result is 1/2 for every p. Inserting a phase flip yields p/2. These are actual
matrix calculations. Reversal never undoes an irreversible channel.

Physical models p=0, p=1 and p=1/2 are explicitly named toy universes. They make
no claim to distinguish every interpretation of quantum mechanics or establish
collapse in nature. A function's name cannot supply missing physics.
