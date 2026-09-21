# Scenario workflow verification

The pinned Lean 4.30.0 build and full `sh scripts/check.sh` gate passed. The added
parameter-change regression was then run successfully through the comparison
exporter test script.

| Check | Result |
|---|---|
| Scenario API and comparison exporter | Compiled with Lean |
| Separate adopter package | Compiled Study, Coherence, and negative assignment checks |
| Coherence comparison | 3 models × 4 procedures; all 12 rational predictions proved and exported |
| Supporting results | Universal prediction formula, direct separation, protected-statistic equality proved |
| Invalid exports | Non-comparison objects, unfinished proofs, and invented premises rejected |
| Signed rational export | A proved -3/2 observable retained exactly |
| Adoption exercise | Changing p=1/2 to p=1/4 compiled, including the 25/32 repeated-exposure prediction |
| Core proof policy and transitive audit | 78 declarations passed; only standard permitted logical axioms |
| Python suite | 34 tests passed |
| Existing matrix and widgets | 98 cells regenerated; 14 pages and 168 axis selections passed |
| HTML layout | New comparison rendered and visually inspected; no full browser test |

The comparison exporter checks the actual `Scenario.Comparison` and audits its
transitive proof dependencies. Its cell data are projected by Lean reduction from
the checked declaration. It does not execute a real-valued interpretation or use
floating-point approximations. An HTML file remains an editable presentation;
rechecking the trusted Lean source is the authority.

This is an adoption workflow for explicit models, not automatic interpretation of
arbitrary ontology labels. Its example supplies effective dephasing laws in the
real-qubit backend. It does not claim a novel no-go theorem or a statistical test of
measured data. Equal displayed statistics do not prove whole-model equivalence.
