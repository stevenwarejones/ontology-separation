# From the reported apparatus to a testable model

Work package 3; 2026-09-26. This is an analytical correspondence audit, not a reconstruction from unavailable workbooks. Read alongside the main report and question register.

## Correspondence and missing obligations

| Reported object | Mathematical object / inference | Evidence needed for the bridge | Current status |
|---|---|---|---|
| Polarization camera images in four bases | Differences of calibrated intensities estimate two pointer components | Pixel response, background, exposure, gain, herald counts, repeated frames and covariance | Method described; full acquisition records unavailable |
| Complex propagator estimate | Pointer bilinears divided by a reference factor and phase convention | Nonzero reference amplitude, reference phase profile, normalization and instrument calibration | Conditional reconstruction, not a per-photon trajectory observation |
| Position labels | Finite spatial modes or quadrature nodes | Actual center coordinates, bin widths, mode overlap and preparation profile | 5.73 μm reported; edge/center convention unresolved |
| Intermediate path labels | Products of shared propagator estimates | Consistent phase gauges and integration weights across slices | Algebra valid; empirical tensor unavailable |
| Finite intermediate sums | Products with intermediate projection operators, if labels represent an orthonormal retained subspace | Actual apertures or a bound on discarded amplitudes; quadrature error if coordinates are nodes instead | Neither bridge established from published description alone |
| Direct endpoint image Pe | Output measurement on the prepared input under the endpoint protocol | Same preparation and optics as prediction, calibrated outcome effects, retained losses and common normalization | Independent observation in principle; comparison not yet reproduced |
| Eq.12 projected polarization branch | A trace-nonincreasing instrument branch | All complementary outcomes or calibrated failure probability | Projection need not invalidate the instrument; deterministic-unitary interpretation would be unjustified |
| Incoherent Pc | Delete cross terms for a declared history decomposition | Physical dephasing map, or explicit assumption about trajectory response under interventions | Restricted null model; not every definite-history ontology |
| Formal two-route example | Exact normalized finite probability tables | Experimental reduction to those amplitudes and access assumptions | Lean certifies the tables and exclusions only |

## Finite-window error: what can be bounded

Let the input be normalized, the propagation steps Uj unitary, and Pj orthogonal projections at intermediate planes. Define

\[
A=U_M\cdots U_1,\qquad B=U_M P_{M-1}U_{M-1}\cdots P_1U_1.
\]

The truncated construction B describes successful passage through all those projections. It is generally different from A. For ideal, unfiltered states ψj=Uj⋯U1ψ, set ℓj=‖(I−Pj)ψj‖². A telescoping expansion, with contractions after each omitted component, gives

\[
\|(A-B)\psi\|\leq\sum_{j=1}^{M-1}\sqrt{\ell_j}=\varepsilon.
\]

For any fixed detection effect 0≤E≤I, write u=Aψ and v=Bψ. Expanding ⟨u,Eu⟩−⟨v,Ev⟩ and using ‖u‖,‖v‖≤1 gives

\[
|p_A(E)-p_B(E)|\leq\min(1,2\varepsilon).
\]

These are unconditioned probabilities. Renormalizing B by its success probability changes the comparison; the same bound cannot simply be carried over. The bound may be loose, but it states exactly which missing measurements would make a truncation claim defensible. It also requires genuine projections and controlled propagation; a 17-node quadrature approximation needs its own discretization bound.

A two-mode counterexample is enough to expose the issue. Let U1=U2=H (the Hadamard matrix), ψ=|0⟩ and P1=|0⟩⟨0|. Unrestricted propagation returns |0⟩ with probability 1. With the intermediate projection, the final |0⟩ probability is 1/4, total survival is 1/2, and the conditional |0⟩ probability is 1/2. Even zero population outside the final output window does not establish that intermediate omissions were harmless: amplitudes can leave and return. This calculation is checked in `intervention_checks.py`; it is not an assertion about Wen's apparatus.

## What acquisition can resolve

For each intermediate plane, measure or bound population outside the selected window using the same initial preparation and unrestricted earlier propagation. Record sufficient spatial range and detector calibration to bound the missing tails. Separately document real apertures, mode profiles and integration weights. Recompute both projected and unrestricted predictions, preserving absolute survival as well as conditional shape. A numerical window scan without tail/calibration control is a sensitivity analysis, not proof of convergence.

This remains ontology checking: the central question is which observation protocols discriminate which model classes. Standalone instrument-control software or a broadly reusable optical calibration package could justify a separate repository later. The present audit and model distinctions belong in `ontology-separation`.
