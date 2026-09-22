"""Create a working checked experiment; never overwrite an adopter's existing file."""
from pathlib import Path
import re


def create_scenario(name: str, output: Path, backend: str = "qubit") -> Path:
    if backend not in {"qubit", "two-qubit", "local-friendliness", "separation"}:
        raise ValueError("Choose backend qubit, two-qubit, local-friendliness or separation")
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
    if backend == "local-friendliness":
        source = _lf_source(name)
    if backend == "separation":
        source = _separation_source(name)
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


def _lf_source(name: str) -> str:
    return f'''import OntologySeparation.LocalFriendliness

namespace {name}
open OntologySeparation.LocalFriendlinessRecipe

-- Four physical registers: Alice, Bob, Charlie's record, Debbie's record.
-- Setting 0 reads a record. Settings 1 and 2 undo that copy, then measure the system.
-- The reference source and relative bases reproduce the established LF witness.
def product : Recipe := {{ reference with source := .of 1 0 0 0 }}

-- Charlie numerator, Debbie numerator, common denominator.
-- Noise acts on the records AFTER the friends copy and BEFORE Wigner chooses.
def comparison := compare "{name}: read or reverse the friends"
  [Law.coherent, Law.recordDephasing 1 0 4,
   Law.recordDephasing 1 0 2, Law.recordDephasing 1 1 1]
  [reference, product]
end {name}

#export_scenario {name}.comparison
#export_theorem OntologySeparation.LocalFriendlinessRecipe.coherent_excludes_LF
#export_theorem OntologySeparation.LocalFriendlinessRecipe.coherent_excludes_profile
#export_theorem OntologySeparation.LocalFriendlinessRecipe.fully_dephased_realizes_profile
'''


def _separation_source(name: str) -> str:
    return f'''import OntologySeparation.Study

namespace {name}
open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation
open OntologySeparation.Comparison

noncomputable section

-- The calibration probe prepares |0>, exposes once, and reads Z. Every supported
-- exposure-dephasing law agrees on its full Boolean outcome distribution.
-- The coherence probe prepares |+>, exposes once, and reads X.
def reference : Law := Law.dephasing 0 1
def noisy : Law := Law.dephasing 1 2

theorem exposure_order : reference.exposure.value < noisy.exposure.value := by
  norm_num [reference, noisy, Law.dephasing, Rate.fraction]

def restricted :
    Result predict calibrationOnly reference noisy :=
  .agreement ⟨restricted_equivalent reference noisy⟩

def expanded :
    Result predict calibrationAndCoherence reference noisy :=
  .separation (expandedSeparator reference noisy exposure_order)

def restrictedClaim : Claim := restricted.claim
def expandedClaim : Claim := expanded.claim

-- These exact checked quantities make the physical edit visible in the report.
def noisyExposureClaim : Claim :=
  .exact (noisy.exposure.value : ℝ) noisy.exposure.value (by norm_num)

def separatorGapClaim : Claim :=
  .exact expandedSeparator.gap
    ((noisy.exposure.value - reference.exposure.value) / 2)
    (by rfl)

def noisyCoherenceClaim : Claim := coherenceClaim noisy
end
end {name}

#export_claim {name}.restrictedClaim
#export_claim {name}.expandedClaim
#export_claim {name}.noisyExposureClaim
#export_claim {name}.separatorGapClaim
#export_claim {name}.noisyCoherenceClaim
'''
