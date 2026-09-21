# Operational onboarding architecture

Goal: let a physicist specify assumptions, compose experiments, and trace results
to checked mathematics without editing a central registry.

The new API has four layers:

1. **Physical model:** normalized conditional response tables or validated quantum
   states. Arbitrary setting-dependent preparation and conditional signaling are
   permitted in the ambient Bell and friend-record model spaces.
2. **Operational laws:** explicit equations for outcome independence, conditional
   parameter independence, independent preparation, and readable fixed records.
   Named vocabularies state which meaning each profile slot has.
3. **Experiment composition:** finite classical channels compose with normalization
   proofs. State-map procedures compose separately, avoiding a classical hidden-state
   interpretation of quantum state vectors or density operators. Preparation and
   public readout remain explicit.
4. **Result:** a question, predictor, profile bridge, and bound/value are attached
   to their proofs. A theorem exporter renders actual Lean types, rather than
   treating handwritten descriptions as formal conclusions.

Bell bounds are derived from conditional probability factorization, local marginals,
and independent preparation. LF bounds use a probability-preserving reconstruction
from arbitrary readable, conditionally local tables into the existing LF model.
The fixed records do not assign every alternative Wigner outcome.

The old report remains compatible and curated; its 98 descriptions are not silently
upgraded to formal statements by this revision. The new operational view is separate.

Acceptance: library and tests compile; changed values/protocols cannot reuse the
wrong proof; invalid exports are rejected; a separate Lake package consumes the
public API; offline pages and documentation identify assumptions and evidence limits.

Design references: [Lean structures](https://lean-lang.org/theorem_proving_in_lean4/Structures-and-Records/),
[Bong et al. published version](https://arxiv.org/abs/1907.05607v4).
