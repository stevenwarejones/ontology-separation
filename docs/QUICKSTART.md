# Quickstart

## Browse the supplied result snapshot

With Python 3.10 or later, from the repository root:

```sh
python -m pip install -e .
ontology-separation list
ontology-separation compare B01 B02
ontology-separation compare B04 P02 --models unitary_memory dephased_memory partial_memory
ontology-separation profiles
ontology-separation html matrix.html
```

A bundled snapshot is convenient for browsing. Loading its JSON validates the
report format; it does **not** independently check its mathematical proofs.
Expand a cell in the HTML report to see assumptions, limitations and its Lean
declaration. Gray cells mean outside the selected adapter's scope, never zero.

## Recheck the mathematics

Install Lean using the official instructions at https://lean-lang.org/install/.
The repository's `lean-toolchain` selects the pinned version automatically.

```sh
lake update
lake exe cache get
lake build
lake build Tests
python scripts/audit.py
python scripts/export.py
python -m unittest discover -s python_tests -v
```

The initial mathlib cache download can be substantial. Later builds reuse it.
Do not upgrade a dependency independently of the Lean toolchain. Commit changes
to both `lakefile.toml` and `lake-manifest.json` when intentionally updating.

For a fresh report from the current local build:

```sh
ontology-separation verify .
```

## Use the Lean API

```lean
import OntologySeparation

open OntologySeparation

example : ¬ LF.theory RealQuantum.lfBehavior :=
  LF.quantumSeparation.excludes

example (m : Memory.Model) :
    Memory.probability m Memory.echo = 1 - m.strength / 2 :=
  Memory.echo_probability m
```

These are ordinary Lean statements. The report is a view of the mathematics,
not another inference engine.

## Use the Python API

```python
from ontology_separation import load_report

report = load_report()
for cell in report.compare(["B02"], ["local_friendliness", "real_singlet"]):
    print(cell["status"], cell["result"], cell["declaration"])
```

The full development gate also uses Node.js (18+) for the dependency-free HTML widget logic test. The Python client and offline HTML do not require Node.
