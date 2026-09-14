# Checked matrix-completion snapshot

Date: 2026-09-14. Project: Ontology Separation.
Base: origin/main at 84aef8c78c61c96cd4481b2ebdcf74b4a03825b4.

## Verification

- Default Lean library and report executable build successfully.
- Lean mathematical, catalog, documentation and research tests pass.
- The standalone `examples/CustomUniverse.lean` adoption example compiles.
- 47 selected declarations (including the exhaustive claim resolver) pass the
  transitive axiom audit. Only propext, Classical.choice and Quot.sound occur.
- All 17 Python tests pass, including matrix coverage, conditional-label contracts,
  exact noise endpoints, all ontology axis slices, HTML escaping and path portability.
- Generated widget JavaScript passes execution tests against a minimal DOM test
  double for all 14 pages and all 168 ordered axis selections. Default evidence
  states, empirical coloring, conditional contradictions and axis collision handling
  are checked. This is interaction-logic testing, NOT a real-browser layout test.
- Real Chromium rendering was attempted but its browser binary could not be
  downloaded in this environment. Visual/browser-engine QA remains outstanding.
- Every JSON/Markdown/HTML report is regenerated from the built Lean executable.

## Contents and limitations

The 98 cells contain 24 native results (five bounds, seven witnesses, twelve toy
predictions) and 74 explicitly conditional additional-law results. There are no
unexplained placeholders, but this is NOT 98 unconditional predictions of seven
complete physical theories. Seven new restricted research subproblems are proved;
the radical beyond-LF research ambitions remain open.

All sixteen binary ontology profiles are shown on each experiment page. Their
physical realizability is not asserted. The optional UI bridge previews are
conditional explanations; the physical vocabulary bridges are not supplied by
checkboxes. Literature measurements are not our calculated witnesses or a formal
raw-data/statistical reanalysis.

## Build environment

The official pinned Lean 4.30.0 binary and unchanged dependency proof sources were
used. This hosted environment requires a host-only executable-path compatibility
shim from the numeric /proc PID spelling to /proc/self/exe. It does not change
Lean's kernel or proof checking and is not needed on normal Macs or GitHub Actions.
Dependency revisions remain pinned in lake-manifest.json.

The portable test fix separates `Tests/` and `python_tests/`; the runner rejects
zero tests and checks case-insensitive path collisions. Node.js is used only for
the widget-logic development test, not by the Python package or offline examples.

This bundle is prepared for a follow-up PR. It has not been pushed or merged.
