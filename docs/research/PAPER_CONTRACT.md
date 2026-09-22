# LF paper-to-code contract: initial review map

Source: [Bong et al., formal assumptions and properties](https://arxiv.org/html/1907.05607v4).
Status: initial mapping, not an external semantic sign-off.

| Paper ingredient | Repository representation | Remaining obligation |
|---|---|---|
| Joint observed events, with consistent friend readout | `FriendRecords.Model` plus `ReadableRecords` | Explicit joint-table construction indexed by observed record pairs |
| Setting-independent record distribution | `IndependentPreparation` | Relate arbitrary latent refinement to conditioning on the record pair itself |
| Conditional remote-setting independence | `ConditionalLocality` | Handle zero-weight record pairs in the direct joint-table correspondence |
| Friend-read setting numbered 1 | `Fin 3` index 0 | Keep relabeling explicit in exported examples |
| Quantum control of observer and environment | Existing finite record protocol | Does not establish macroscopic controllability or consciousness |
| Complete 3×3 binary LF polytope | One genuine inequality and finite conditional-box model | Completeness of all facets is not proved here |

This PR proves the two repository representations equivalent. It does not
substitute that internal theorem for the outstanding paper-to-code obligations.

Next proof target: construct the record-indexed joint table, prove its observable
marginal and conditional laws, and reconstruct a finite model without dividing
by zero-probability conditioning events.
