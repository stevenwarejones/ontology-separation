"""Create a working checked experiment; never overwrite an adopter's existing file."""
from pathlib import Path
import re


def create_scenario(name: str, output: Path) -> Path:
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
    output.parent.mkdir(parents=True, exist_ok=True)
    try:
        with output.open('x', encoding='utf-8') as f:
            f.write(source)
    except FileExistsError as exc:
        raise ValueError(f'Refusing to overwrite existing source: {output}') from exc
    return output
