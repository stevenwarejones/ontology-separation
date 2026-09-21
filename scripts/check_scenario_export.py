#!/usr/bin/env python3
"""Exercise the checked comparison exporter in an adopter's separate package."""
from pathlib import Path
import subprocess
import json
import tempfile
ROOT = Path(__file__).resolve().parents[1] / 'examples/downstream'
HEADER = 'import OntologySeparation.Recipes\nimport OntologySeparation.Reporting.Scenario\nopen OntologySeparation OntologySeparation.Recipes\n def comparison := compare "Test" [Law.dephasing 1 2] [⟨.plus, [.expose], .x⟩]\n'
CASES = [
    ('#export_scenario comparison\n', True),
    ('#export_scenario probability\n', False),
    ('def bad : Scenario.Comparison scenario := { comparison with predictions := ⟨fun _ _ => 0, by sorry⟩ }\n#export_scenario bad\n', False),
    ('axiom invented : False\ndef bad : Scenario.Comparison scenario := { comparison with predictions := ⟨fun _ _ => 0, fun _ _ => False.elim invented⟩ }\n#export_scenario bad\n', False),
]
with tempfile.TemporaryDirectory(prefix='scenario-export-') as directory:
    source = Path(directory)/'Fixture.lean'
    for body, accepted in CASES:
        source.write_text(HEADER+body)
        r = subprocess.run(['lake','env','lean',str(source)], cwd=ROOT, capture_output=True, text=True)
        out = r.stdout+r.stderr
        if (r.returncode == 0) != accepted or ('ONTOLOGY_SCENARIO ' in out) != accepted:
            raise SystemExit('Unexpected comparison exporter behavior:\n'+out)
    negative = """
noncomputable def negativeScenario : Scenario Law Recipe :=
  ⟨⟨scenario.question.interface, fun _ => -(3/2 : ℝ)⟩, scenario.interpret⟩
def negativeTable : Scenario.Comparison negativeScenario where
  title := "Negative observable"
  description := "Checks signed rational export."
  models := [("Coherent", Law.dephasing 0 1)]
  protocols := [("Direct", ⟨.plus, [.expose], .x⟩)]
  models_nonempty := by simp
  protocols_nonempty := by simp
  predictions := ⟨fun _ _ => -(3/2), by intro m p; change -(3/2 : ℝ) = ((-(3/2) : ℚ) : ℝ); norm_num⟩
#export_scenario negativeTable
"""
    source.write_text(HEADER+negative)
    r = subprocess.run(['lake','env','lean',str(source)], cwd=ROOT, capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(r.stdout+r.stderr)
    records = [json.loads(line.removeprefix('ONTOLOGY_SCENARIO ')) for line in r.stdout.splitlines()
               if line.startswith('ONTOLOGY_SCENARIO ')]
    if len(records) != 1 or records[0]['comparison']['values'][0][0]['quantity'] != {'numerator':'-3','denominator':'2'}:
        raise SystemExit('Signed rational export changed the proved value')
print('Comparison exporter: checked cells and signed rationals accepted; invalid proofs rejected')
