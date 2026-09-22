# Offline examples

Open `index.html` in a browser. No server or installed Python/Lean is needed to
browse the committed snapshots. For proof assurance, run `sh scripts/check.sh`.

- `matrix.html`: all 14 experiments × seven model classes.
- `B01.html` through `B04.html`, `P01.html` through `P10.html`: each experiment,
  its model results, sixteen ontology profiles, and every two-axis slice.
- `evidence.html`: published measurements and their scope, separate from calculations.
- `CustomUniverse.lean`: a short, build-checked example of reusing parameterized proofs.

Amber conditional results use explicitly ADDED laws; they are not native predictions
of the model column. The optional ontology-bridge checkbox previews a conditional
mapping and does not supply a Lean proof or establish physical realizability.
Realism → global truth is an optional extra premise, not a universally imposed rule.
Published statistical evidence is not absolute logical falsification. Compatibility
with a result never proves an ontology true.

Regenerate HTML from the built executable with `python scripts/export.py`. The
committed pages are deterministic, self-contained and work offline. A static
16-profile table remains available when JavaScript is disabled.

- `partial-leakage.html`: checked exact-point comparison plus the symbolic partial-leakage robustness theorem.

- `SeparatorSearchStudy.lean`: public multi-candidate search example; the first candidate agrees and a later candidate supplies the checked separator.
