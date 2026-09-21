# Operational onboarding verification

Verified with the pinned Lean 4.30.0 toolchain and repository dependency manifest.
The complete `sh scripts/check.sh` gate exited successfully.

| Check | Result |
|---|---|
| Default library and executable build | Passed |
| Lean test library, including operational tests | Passed |
| Existing custom-universe example and new physicist workflow | Passed |
| Theorem report generation | 24 actual theorem statements; 16 operational profiles |
| Proof policy and transitive dependency audit | 78 declarations; only `propext`, `Classical.choice`, `Quot.sound` permitted |
| Exporter integration tests | Valid proof accepted; definition, invented axiom, and unfinished proof rejected |
| Python tests | 34 passed, including failed-check report preservation and CLI routing |
| Existing report regeneration | 98 cells across 14 experiments |
| Existing HTML interaction checks | 14 pages and 168 axis selections passed |
| Separate Lake package | Built Study and exported two new predictions without registry edits |

New operational and historical HTML pages were rendered and visually inspected.
This was static layout inspection; no full browser layout test was run. The
JavaScript interaction tests above check widget logic separately.

The downstream example has its own package manifest and compiled Study module.
Within this checkout it shares pinned dependency downloads using `packagesDir`;
its README explains removal of that setting for a standalone repository.

The new negative Lean examples check that a prediction cannot be reassigned to a
wrong value or experiment. Physical counterexamples include conditional signaling,
setting-dependent preparation, failed outcome independence, and failed record
readability. The LF reconstruction preserves every public probability.

This verifies mathematical statements and software behavior. It does not validate
all physical interpretations, establish that every profile is inhabited, or
reproduce experimental statistical analyses. The real-qubit backend is restricted;
the existing research-scenario matrix retains its documented legacy scope.

The subsequent complete scenario workflow is verified in
[SCENARIO_VERIFICATION.md](SCENARIO_VERIFICATION.md).
