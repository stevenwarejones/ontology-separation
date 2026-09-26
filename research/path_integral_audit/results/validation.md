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

## Full repository gate

`sh scripts/check.sh` stopped in the build stage: existing `ForcedSignalingLC4Witness` compiler process exited 137 during a broad concurrent rebuild. An isolated rebuild and a further `LEAN_NUM_THREADS=1` rebuild both also exited 137. During the last attempt, the environment's 8 GiB cgroup was full and its OOM-kill counter increased from 7 to 8. No Lean proof diagnostic was emitted for these failures. The file is unchanged from the base commit.

The full gate, whole-repository axiom snapshot regeneration and downstream checks are therefore **not completed locally**. The new module/tests and standard report passed separately. This is a draft checkpoint, not a claim that the full repository gate is green. Next action: run the unchanged gate with sufficient memory/CI; if it fails with a proof diagnostic, investigate that diagnostic before considering the PR ready. Do not weaken proof checking or silently reuse stale compiled artifacts.

## Environment

Python 3.12.14; NumPy 2.3.5; openpyxl 3.1.5; Matplotlib 3.10.8; Pillow 12.3.0. Runtime environment packages were used without installing dependencies. Raw source files and transient build logs are ignored.

The local Lean launch uses an existing workspace portability adapter redirecting only the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`. This repairs executable-location discovery in this environment; it changes no proof terms, compiler options or allowed axioms. The repository toolchain/dependency pins are unchanged.
