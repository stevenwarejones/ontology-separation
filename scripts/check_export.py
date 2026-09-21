#!/usr/bin/env python3
"""Integration-test rejection of misleading or unfinished theorem exports."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
CASES = [
 ('def fake : OntologySeparation.Claim := .realizedBound (M := Unit) (fun _ => False) (fun _ => 0) 0 (by intro _ h; exact h.elim) () (by trivial)\n#export_claim fake\n', False, 'error'),
 ('def fake : OntologySeparation.Claim := .witness (M := Unit) (fun _ => False) (fun _ => 0) () (by trivial) 0 (by norm_num)\n#export_claim fake\n', False, 'error'),
 ('def fake : OntologySeparation.Claim := .exclusion (M := Unit) (fun _ => True) () (by simp)\n#export_claim fake\n', False, 'error'),
 ('def actual : OntologySeparation.Claim := .exact (1 : ℝ) 1 (by norm_num)\n#export_claim actual\n', True, '"kind":"exact"'),
 ('def wrong : OntologySeparation.Claim := .exact (1 : ℝ) 2 (by norm_num)\n#export_claim wrong\n', False, 'error'),
 ('def emptyBound : OntologySeparation.Claim := .bound (M := Empty) (fun _ => True) (fun _ => 0) 0 (fun m => nomatch m)\n#export_claim emptyBound\n', True, '"kind":"bound"'),
 ('axiom invented : False\ndef fake : OntologySeparation.Claim := .exact (1 : ℝ) 2 (False.elim invented)\n#export_claim fake\n', False, 'unsupported proof dependency'),
 ('def fake : OntologySeparation.Claim := .exact (1 : ℝ) 2 (by sorry)\n#export_claim fake\n', False, 'unsupported proof dependency'),
 ('theorem actual : True := by trivial\n#export_theorem actual\n', True, 'ONTOLOGY_CLAIM '),
 ('def misleading : Nat := 99\n#export_theorem misleading\n', False, 'Expected a proved theorem'),
 ('axiom invented : False\ntheorem fabricated : False := invented\n#export_theorem fabricated\n', False, 'unsupported proof dependency'),
 ('theorem unfinished : False := by sorry\n#export_theorem unfinished\n', False, 'unsupported proof dependency'),
]
with tempfile.TemporaryDirectory(prefix='ontology-export-') as directory:
    source = Path(directory)/'Check.lean'
    for body, success, expected in CASES:
        source.write_text('import OntologySeparation.Reporting.Claim\nnoncomputable section\n'+body)
        r = subprocess.run(['lake','env','lean',str(source)], cwd=ROOT, capture_output=True, text=True)
        out = r.stdout+r.stderr
        if (r.returncode == 0) != success or expected not in out:
            raise SystemExit('Unexpected exporter behavior:\n'+out)
        if not success and 'ONTOLOGY_CLAIM ' in out:
            raise SystemExit('Rejected theorem exported')
print('Shared exporter: theorem/exact/bound accepted; wrong values, fake proofs and unsupported dependencies rejected')
