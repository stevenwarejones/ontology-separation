"""Create a working checked experiment; never overwrite an adopter's existing file."""
from pathlib import Path
import re


def create_scenario(name: str, output: Path, backend: str = "qubit") -> Path:
    if backend not in {"qubit", "two-qubit"}:
        raise ValueError("Choose backend qubit or two-qubit")
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', name) or name in {'Type', 'Sort', 'Prop'}:
        raise ValueError('Choose a Lean study name starting with a capital letter, e.g. MyStudy')
    if output.suffix != '.lean':
        raise ValueError('The scenario source must have a .lean extension')
    parents = (output.resolve().parent, *output.resolve().parent.parents)
    if not any((p/'lakefile.toml').is_file() or (p/'lakefile.lean').is_file() for p in parents):
        raise ValueError('Create the scenario inside an existing Lake project; see docs/START_HERE.md')
    source = f'''import OntologySeparation.Recipes

namespace {name}
open OntologySeparation.Recipes

-- Change the laws or recipes. The framework derives exact predictions and proofs.
-- Law.dephasing takes numerator and denominator, both checked for physical validity.
def comparison := compare "{name}"
  [Law.dephasing 0 1, Law.dephasing 1 2, Law.dephasing 1 1]
  [ {{ prepare := .plus, steps := [.expose], measure := .x }},
    {{ prepare := .plus, steps := [.phaseFlip, .expose], measure := .x }},
    {{ prepare := .plus, steps := [.hadamard, .expose, .hadamard], measure := .x }},
    {{ prepare := .plus, steps := [.expose, .expose], measure := .x }} ]
end {name}

#export_scenario {name}.comparison
'''
    if backend == "two-qubit":
        source = _two_qubit_source(name)
    output.parent.mkdir(parents=True, exist_ok=True)
    try:
        with output.open('x', encoding='utf-8') as f:
            f.write(source)
    except FileExistsError as exc:
        raise ValueError(f'Refusing to overwrite existing source: {output}') from exc
    return output


def _two_qubit_source(name: str) -> str:
    return f'''import OntologySeparation.Recipes

namespace {name}
open OntologySeparation.TwoQubit

-- Alice and Bob have two local projective settings each.
-- These rational directions give CHSH = 1502/625 for an ideal singlet.
-- Only exposure uses the selected row's law. All gates precede setting choices.
def direct : Recipe := {{ singletRecipe with steps := [.expose .alice] }}

-- Build the same singlet from |00>: H(A), CNOT(A->B), X(B), Z(A).
def circuit : Recipe :=
  {{ direct with
    prepare := .product false false
    steps := [.h .alice, .cnot .alice, .x .bob, .z .alice, .expose .alice] }}

-- Change preparation while keeping the same measurements and exposure.
def product : Recipe := {{ direct with prepare := .product false true }}

-- Law.dephasing takes Alice numerator, Bob numerator, common denominator.
-- p=1 is full Z dephasing; p=0 is ideal. Rates are checked before export.
def comparison := compare "{name}: two-qubit Bell experiment"
  [Law.ideal, Law.dephasing 1 0 8, Law.dephasing 1 0 4, Law.dephasing 1 0 1]
  [direct, circuit, product]
end {name}

#export_scenario {name}.comparison
'''
