# Validation record

Date: 2026-09-26 UTC. Repository base: `c10474e9b45cca2ea260eec2d9f348a12cf62677`.

## Completed checks

- `lake build OntologySeparation.Experiments.PathInterference Tests.PathInterference`: passed. All new definitions, normalization proofs, finite-class exclusion/membership and access counterexamples compile with the pinned Lean 4.30.0 toolchain.
- `lake env lean research/path_integral_audit/Audit.lean`: passed; all nine registered new roots report only the permitted logical axioms (`propext`, `Classical.choice`, `Quot.sound`). Output is `path-axioms.txt`.
- Standard proof reporter: exported seven checked claims to `examples/path-interference.html`, including its transitive dependency audit.
- `synthetic_checks.py`: passed. Route enumeration versus matrix multiplication; complete 17⁵ finite-grid enumeration; eight declared noise seeds with shared kernel factors; two coordinate conventions; common-mode calibration counterexample; analytical Gaussian overlap checked independently by 64-node Gaussian quadrature.
- Python syntax compilation: passed for downloader, extractor and synthetic script.
- Figure inspection: synthetic plot has readable axes/legend and explicitly identifies simulated data; source supplement page 4 visually checked.
- `fetch_data.py --verify-only`: reports all 19 expected files unavailable and exits 2. This is the correct missing-input result, not a successful download.
- Original workbook extraction and observed-data reproduction: **not run; originals inaccessible**. No claims of passing workbook-content validation.

## Full repository gate and CI evidence

Local full/isolated/single-thread builds exhausted the shared 8 GiB environment in the existing `ForcedSignalingLC4Witness`. A proof-decomposition experiment was attempted and then discarded once CI supplied full verification; no changes to that existing proof are included.

On PR #84 commit `7ef21978018473de694d9441a3a58ae0f3b94b2c`, [CI run 36211257318](https://github.com/stevenwarejones/ontology-separation/actions/runs/36211257318), verify job `108318095178`, completed `sh scripts/check.sh` successfully at 2026-09-26 02:30:07 UTC. This includes the whole-repository audit, generated exports, 65 Python tests and downstream adopter checks. Python 3.10/3.11/3.12 jobs all passed.

The subsequent snapshot-consistency step failed solely because `docs/AXIOM_AUDIT.txt` lacked the nine new roots. The exact generated diff was recovered from that job's log and applied; its appended bytes also match the independently generated local `results/path-axioms.txt`. No generated predictions were hand-edited. The next CI run must confirm snapshot consistency. This distinguishes a successful proof/test gate from the overall first run's failed status.

## Follow-up analytical checks

`intervention_checks.py` passes 48 reproducibly seeded mixed-state/effect cases against independent direct density-matrix evaluation (maximum error 2.23e-16), including the imaginary contrast sign. It verifies complete lossy outcome normalization, a coherent state with zero detectable contrast, the intermediate-window counterexample and 32 numerical checks of the telescoping bound. Precision figures are recorded in `intervention.json`. These calculations validate the implementation of the stated model, not physical calibration, experimental novelty or statistical power. The generalized physical/statistical derivations are not Lean-certified.

## Environment

Python 3.12.14; NumPy 2.3.5; openpyxl 3.1.5; Matplotlib 3.10.8; Pillow 12.3.0. Runtime environment packages were used without installing dependencies. Raw source files and transient build logs are ignored.

The local Lean launch uses an existing workspace portability adapter redirecting only the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`. This repairs executable-location discovery in this environment; it changes no proof terms, compiler options or allowed axioms. The repository toolchain/dependency pins are unchanged.
