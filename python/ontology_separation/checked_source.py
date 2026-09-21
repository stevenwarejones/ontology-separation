"""Build current imports before reporting; never publish stale compiled dependencies."""
from __future__ import annotations
import os
from pathlib import Path
import subprocess
import tempfile


def project_for(source: Path) -> Path:
    source = source.resolve()
    if not source.is_file() or source.suffix != '.lean':
        raise ValueError(f'Expected an existing Lean source file: {source}')
    for directory in source.parents:
        if any((directory/name).is_file() for name in ('lakefile.toml', 'lakefile.lean')):
            return directory
    raise ValueError(f'No Lake project found above {source}; put the source in your Lean project')


def validate_output(source: Path, output: Path) -> None:
    if source.resolve() == output.resolve() or (
            source.exists() and output.exists() and os.path.samefile(source, output)):
        raise ValueError('A report cannot overwrite its Lean source')
    if output.suffix.lower() not in ('.html', '.htm'):
        raise ValueError('Choose an .html output file; reports cannot overwrite Lean or project files')


def run_lean(source: Path) -> str:
    project = project_for(source)
    # Unlike `lake env lean`, `lake lean` builds imported modules from current source.
    try:
        result = subprocess.run(['lake', 'lean', str(source.resolve()), '--', '-DautoImplicit=false'], cwd=project,
                                capture_output=True, text=True)
    except FileNotFoundError as exc:
        raise ValueError('lake was not found. Install Lean with Elan and add $HOME/.elan/bin to PATH') from exc
    if result.returncode:
        raise ValueError('Lean checking failed. No report was updated; an existing report may be stale.\n'
                         + result.stdout + result.stderr)
    return result.stdout


def atomic_write_html(output: Path, document: str) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=output.parent,
                                         prefix='.'+output.name+'.', suffix='.tmp', delete=False) as f:
            temporary = Path(f.name)
            f.write(document)
        os.replace(temporary, output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
