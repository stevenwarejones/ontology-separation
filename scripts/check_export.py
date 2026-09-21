#!/usr/bin/env python3
"""Integration-test rejection of misleading or unfinished theorem exports."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
CASES = [
 ('theorem actual : True := by trivial\n#export_theorem actual\n', True, 'ONTOLOGY_THEOREM '),
 ('def misleading : Nat := 99\n#export_theorem misleading\n', False, 'Expected a proved theorem'),
 ('axiom invented : False\ntheorem fabricated : False := invented\n#export_theorem fabricated\n', False, 'unsupported proof dependency'),
 ('theorem unfinished : False := by sorry\n#export_theorem unfinished\n', False, 'unsupported proof dependency'),
]
with tempfile.TemporaryDirectory(prefix='ontology-export-') as directory:
    source = Path(directory)/'Check.lean'
    for body, success, expected in CASES:
        source.write_text('import OntologySeparation.Reporting.Export\n'+body)
        r = subprocess.run(['lake','env','lean',str(source)], cwd=ROOT, capture_output=True, text=True)
        out = r.stdout+r.stderr
        if (r.returncode == 0) != success or expected not in out:
            raise SystemExit('Unexpected exporter behavior:\n'+out)
        if not success and 'ONTOLOGY_THEOREM ' in out:
            raise SystemExit('Rejected theorem exported')
print('Exporter: valid proof accepted; definition, invented premise and unfinished proof rejected')
