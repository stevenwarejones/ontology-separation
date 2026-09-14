# Checked release snapshot

Date: 2026-09-14. Version: 0.1.0. Project: Ontology Separation.

## Completed verification

- Default Lean library and lightweight report executable build successfully.
- `lake build Tests` checks mathematical, catalog and documentation examples.
- All 22 selected declarations pass the transitive axiom audit. Only propext,
  Classical.choice and Quot.sound occur; no unfinished-proof dependency appears.
- All 10 Python API/report tests pass.
- An editable Python installation in an isolated virtual environment succeeds;
  the installed CLI's help and a filtered LF/memory comparison were exercised.
- The report is regenerated from the Lean executable, not authored as a table.

## Contents and limitations

There are 14 scenario descriptions and seven model/theory choices, giving 98
cells. Of these, two are verified bounds, four are verified witnesses and twelve
are verified toy predictions. Forty-nine cells are unresolved, and 31 are outside
the selected adapter's scope. Reuse of a theorem across cells is not a new theorem.

All sixteen binary assumption profiles are expressible. No claim is made that
all sixteen are physically realizable. Seven advanced proposals remain protocol
specifications, while three have limited executable toy reductions. The radical
beyond-LF ambitions remain research questions.

Bell and genuine LF have a common-interface bound/witness separation. The LF
quantum realization is an ideal real-projective singlet model with a coherent
friend-implementation assumption, not published laboratory data. The optional
bridge from this restricted model into Lean-QIT's general IsQuantum predicate
has not been proved and is not assumed by any result.

## Build environment

The official pinned Lean 4.30.0 binary was used. This hosted environment exposes
its own executable path through /proc/self/exe but denies the numeric-pid spelling
used by Lean. A host-only path compatibility shim mapped only that own-process
lookup to /proc/self/exe. It did not alter Lean's kernel or proof checking and is
not required in normal local or CI installations. No dependency proof source was
changed to obtain the build. The dependencies and revisions are in lake-manifest.json.

The source is prepared for a new repository; no GitHub repository or package
registry publication has been performed.
