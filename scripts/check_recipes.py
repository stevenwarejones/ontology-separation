#!/usr/bin/env python3
"""Exercise adoption, stale-import protection, and rejected mistakes in a real Lake project."""
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'python'))
from ontology_separation.scaffold import create_scenario
from ontology_separation.scenario_report import write_report

with tempfile.TemporaryDirectory(prefix='recipe-adoption-', dir=ROOT/'.lake') as directory:
    project = Path(directory)
    (project/'lean-toolchain').write_text((ROOT/'lean-toolchain').read_text())
    (project/'lakefile.toml').write_text(
        'name = "recipeAdoption"\n'
        + 'packagesDir = '+json.dumps(str(ROOT/'.lake/packages'))+'\n'
        + '[[require]]\nname = "ontologySeparation"\npath = '+json.dumps(str(ROOT))+'\n'
        + '[[lean_lib]]\nname = "FixtureModel"\nmoreLeanArgs = ["-DautoImplicit=false"]\n')
    env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE='1')
    updated = subprocess.run(['lake','update'],cwd=project,env=env,capture_output=True,text=True)
    if updated.returncode:
        raise SystemExit(updated.stdout+updated.stderr)
    starter = create_scenario('Starter',project/'Starter.lean')
    output = project/'report.html'
    assert write_report(starter,output) == 12
    assert '<td>5/8</td>' in output.read_text()
    print('Generated starter: all 12 cells checked', flush=True)

    model = project/'FixtureModel.lean'
    reporter = project/'Publish.lean'
    reporter.write_text('import FixtureModel\n#export_scenario current\n')
    def source(n, d):
        return ('import OntologySeparation.Recipes\nopen OntologySeparation.Recipes\n'
                f'def current := compare "Imported model" [Law.dephasing {n} {d}]\n'
                '  [{ prepare := .plus, steps := [.expose], measure := .x }]\n')
    model.write_text(source(0,1))
    assert write_report(reporter,output) == 1
    assert '<td>1</td>' in output.read_text()
    # Do not call lake build here: the public report command must rebuild this import itself.
    model.write_text(source(1,2))
    assert write_report(reporter,output) == 1
    assert '<td>3/4</td>' in output.read_text()
    assert 'Exposure dephasing p=1/2' in output.read_text()
    previous = output.read_bytes()
    model.write_text(source(2,1))
    try:
        write_report(reporter,output)
    except ValueError as exc:
        assert 'may be stale' in str(exc)
    else:
        raise AssertionError('Invalid edited import reused the old compiled module')
    assert output.read_bytes() == previous
    print('Edited import: rebuilt prediction and label; invalid edit rejected without overwriting output',flush=True)

    header='import OntologySeparation.Recipes\nopen OntologySeparation OntologySeparation.Recipes\n'
    recipe='{ prepare := .plus, steps := [.expose], measure := .x }'
    cases = [
        ('zero denominator','def bad := Law.dephasing 0 0\n','positive'),
        ('rate above one','def bad := Law.dephasing 3 2\n','bounded'),
        ('negative rate','def bad := Rate.of (-1)\n','nonneg'),
        ('empty model list',f'def bad := compare "Empty" [] [{recipe}]\n','hm'),
        ('empty recipe list','def bad := compare "Empty" [Law.dephasing 0 1] []\n','hp'),
        ('unknown operation','def bad : Recipe := { prepare := .plus, steps := [.teleport], measure := .x }\n','teleport'),
        ('model-dependent procedure','def bad : Recipe := { prepare := .plus, steps := fun (_ : Law) => [.expose], measure := .x }\n','error'),
        ('duplicate laws',f'def bad := compare "Duplicate" [Law.dephasing 1 2, Law.dephasing 2 4] [{recipe}]\n#export_scenario bad\n','Duplicate'),
        ('duplicate recipes',f'def bad := compare "Duplicate" [Law.dephasing 0 1] [{recipe}, {recipe}]\n#export_scenario bad\n','Duplicate'),
        ('unfinished proof',f'def fake : Law := ⟨⟨2, by norm_num, by sorry⟩⟩\ndef bad := compare "Fake" [fake] [{recipe}]\n#export_scenario bad\n','sorryAx'),
        ('invented premise',f'axiom invented : False\ndef fake : Law := ⟨⟨2, by norm_num, False.elim invented⟩⟩\ndef bad := compare "Fake" [fake] [{recipe}]\n#export_scenario bad\n','unsupported proof dependency'),
    ]
    fixture=project/'Mistake.lean'
    for label, body, expected in cases:
        fixture.write_text(header+body)
        try:
            write_report(fixture,output)
        except ValueError as exc:
            assert expected in str(exc), (label,str(exc))
        else:
            raise AssertionError('Accepted mistake: '+label)
        assert output.read_bytes() == previous, label
    print(f'Adoption guardrails: {len(cases)} invalid recipes, laws and exports rejected',flush=True)
