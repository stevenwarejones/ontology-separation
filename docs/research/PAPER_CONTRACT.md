# LF paper-to-code contract

Source: [Bong et al., formal assumptions and properties](https://arxiv.org/html/1907.05607v4).
Status: finite correspondence implemented; external semantic review remains open.

| Paper ingredient | Checked representation | Scope or remaining obligation |
|---|---|---|
| Joint observed events with consistent friend readout | `LFJoint.Table` and `Readable`; `joint_iff_lf` | Three settings and binary outcomes; no counterfactual Wigner assignments |
| Setting-independent record distribution | `IndependentRecords`; `fromOperational_independent` | Latent states are explicitly combined by observed record pair |
| Conditional remote-setting independence | `local_iff_conditional`, `conditional_probability` | Division-free equalities under independent records; positive-mass conditionals are ordinary ratios |
| Impossible record pairs | `prob_eq_zero_of_mass_zero`, `conditional_reconstruct` | Normalized fallback responses provably contribute zero to observations |
| Friend-read setting numbered 1 | `Fin 3` index 0 | Keep relabeling explicit in examples |
| Quantum control of observer and environment | Existing finite record protocol | Does not establish macroscopic controllability or consciousness |
| Complete 3×3 binary LF polytope | Existing genuine inequality and finite conditional-box model | Completeness of all facets is not proved here |

`LFJoint.joint_iff_lf` proves both inclusions for the observable behavior class.
See [the adopter walkthrough](LF_PAPER_GUIDE.md) for the constructions and the
resulting inequality. The internal equivalence introduced in #27 remains a
separate theorem used in this proof.

Next scientific target: quantify relaxation of record readability in these joint
tables, with an exact bound, explicit attaining models and precise experimental
scope. Do not call that new physics without comparing the relaxed-LF literature.
