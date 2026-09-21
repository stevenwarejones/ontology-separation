"""Read-only installation diagnostics. Never builds or downloads a toolchain."""
from __future__ import annotations
from pathlib import Path
import shutil
import sys


def diagnose(directory: Path) -> str:
    lines = [f'Python: {sys.version.split()[0]} (requires 3.10+)',
             'Browse bundled results: available without Lean']
    project = next((p for p in (directory.resolve(), *directory.resolve().parents)
                    if any((p/n).is_file() for n in ('lakefile.toml', 'lakefile.lean'))), None)
    if project is None:
        return '\n'.join(lines + ['Lake project: not found',
            'Next: run doctor inside your checkout to check proof-tool availability.'])
    lines.append(f'Lake project: {project}')
    pin = project/'lean-toolchain'
    lines.append('Pinned toolchain: '+(pin.read_text().strip() if pin.exists() else 'not specified'))
    lake = shutil.which('lake')
    if lake is None:
        lines += ['Lake: not on PATH',
                  'Next: install Lean with Elan (https://lean-lang.org/install/), then reopen your terminal.',
                  'If already installed, add $HOME/.elan/bin to PATH.']
    else:
        # Do not execute an Elan shim: even a version probe may install a toolchain.
        lines += [f'Lake executable: {lake} (not executed)',
                  'Pinned toolchain availability: not verified; run lake --version to check it.']
    # A sentinel is evidence of cached files, never a claim that every import is warm.
    sentinel = project/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean'
    if sentinel.is_file():
        lines.append('Mathlib cache: sample compiled module found; completeness not checked')
        lines.append('Once the toolchain is available: run scenario-report to build imports and check predictions.')
    else:
        lines += ['Mathlib cache: sample compiled module not found in this project',
                  'After Lean is available: lake exe cache get']
    lines.append('Doctor does not verify proofs or tell whether another build is making progress.')
    return '\n'.join(lines)
