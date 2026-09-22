#!/usr/bin/env python3
"""Exercise adoption, stale-import protection, and rejected mistakes in a real Lake project."""
from pathlib import Path
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'python'))
from ontology_separation.scaffold import create_scenario
from ontology_separation.scenario_report import write_report
from ontology_separation.proof_report import write_report as write_claim_report, parse_exports
from ontology_separation.checked_source import run_lean

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

    bell = create_scenario('BellStarter', project/'BellStarter.lean', backend='two-qubit')
    bell_output = project/'bell.html'
    assert write_report(bell, bell_output) == 12
    values = re.findall(r'<td>([^<]+)</td>', bell_output.read_text())
    expected = [cell for value in ['1502/625', '1358/625', '1214/625', '14/25']
                for cell in [value, value, '14/25']]
    assert values == expected, values
    print('Two-qubit starter: 12 cells checked in an independent adopter project', flush=True)

    friend = create_scenario('FriendStarter', project/'FriendStarter.lean', backend='local-friendliness')
    friend_output = project/'friends.html'
    assert write_report(friend, friend_output) == 8
    values = re.findall(r'<td>([^<]+)</td>', friend_output.read_text())
    expected = [cell for value in ['1214656/180625', '1095424/180625', '976192/180625', '2684416/4515625']
                for cell in [value, '-744738/180625']]
    assert values == expected, values
    assert 'fully_dephased_realizes_profile' in friend_output.read_text()
    print('LF starter: eight cells and profile proof provenance checked in an adopter project', flush=True)

    separation = create_scenario('SeparationStarter', project/'SeparationStarter.lean',
                                 backend='separation')
    separation_output = project/'separation.html'
    assert write_claim_report(separation, separation_output) == 5
    records = parse_exports(run_lean(separation))
    exact = next(r['claim'] for r in records if r['declaration'].endswith('noisyCoherenceClaim'))
    assert exact['kind'] == 'exact'
    assert exact['quantity'] == {'numerator': '3', 'denominator': '4'}, exact
    page = separation_output.read_text()
    assert 'Agreement over stated access domain' in page
    assert 'Verified separating experiment' in page
    assert '>1/2<' in page, page
    assert '>1/4<' in page, page
    assert '>3/4<' in page, page

    separation.write_text(separation.read_text().replace('Law.dephasing 1 2', 'Law.dephasing 1 4', 1))
    assert write_claim_report(separation, separation_output) == 5
    records = parse_exports(run_lean(separation))
    exact = next(r['claim'] for r in records if r['declaration'].endswith('noisyCoherenceClaim'))
    assert exact['quantity'] == {'numerator': '7', 'denominator': '8'}, exact
    page = separation_output.read_text()
    assert '>1/4<' in page, page
    assert '>1/8<' in page, page
    assert '>7/8<' in page, page
    assert '>3/4<' not in page, page
    previous_separation = separation_output.read_bytes()

    separation.write_text(separation.read_text().replace('Law.dephasing 1 4', 'Law.dephasing 0 1', 1))
    try:
        write_claim_report(separation, separation_output)
    except ValueError as error:
        assert 'exposure_order' in str(error) or 'unsolved goals' in str(error), str(error)
    else:
        raise AssertionError('Zero-gap separation edit was accepted')
    assert separation_output.read_bytes() == previous_separation
    print('Separation starter: scoped claims, editable exact value, and stale-output guard checked',
          flush=True)

    # Copy public examples into an independent Lake project: no repository-local imports.
    for filename, count in [('RecordAccessStudy.lean', 8), ('ModelClassStudy.lean', 6)]:
        study = project / filename
        study.write_text((ROOT / 'examples' / filename).read_text())
        assert write_claim_report(study, project / (filename + '.html')) == count
    study = project / 'ModelClassStudy.lean'
    checked_output = project / 'ModelClassStudy.lean.html'
    before = checked_output.read_bytes()
    study.write_text(study.read_text().replace(
        'if bit then 1/3 else 2/3', 'if bit then 1/2 else 1/2', 1))
    try:
        write_claim_report(study, checked_output)
    except ValueError as error:
        assert 'reproduces' in str(error) or 'unsolved goals' in str(error), str(error)
    else:
        raise AssertionError('Incorrect whole-table membership was accepted')
    assert checked_output.read_bytes() == before
    print('Access and model-class adopters checked; mismatched weights rejected without overwriting output', flush=True)

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

    header='import OntologySeparation.Recipes\nimport OntologySeparation.LocalFriendliness\nopen OntologySeparation OntologySeparation.Recipes\n'
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
    cases += [
        ('zero state', 'def bad := TwoQubit.Pure.of 0 0 0 0\n', 'valid'),
        ('zero measurement direction', 'def bad := TwoQubit.Basis.of 0 0\n', 'valid'),
        ('invalid two-qubit rate', 'def bad := TwoQubit.Law.dephasing 0 2 1\n', 'bobBound'),
        ('zero two-qubit denominator', 'def bad := TwoQubit.Law.dephasing 0 0 0\n', 'positive'),
        ('nonexistent wire', 'def bad : TwoQubit.Operation := .h .charlie\n', 'charlie'),
        ('same CNOT control/target', 'def bad : TwoQubit.Operation := .cnot .alice .alice\n', 'error'),
        ('model-dependent two-qubit recipe',
         'def bad : TwoQubit.Recipe := { TwoQubit.singletRecipe with steps := fun (_ : TwoQubit.Law) => [] }\n', 'error'),
        ('duplicate two-qubit laws',
         'def bad := TwoQubit.compare "Bad" [TwoQubit.Law.ideal, TwoQubit.Law.dephasing 0 0 2] [TwoQubit.singletRecipe]\n#export_scenario bad\n', 'Duplicate'),
        ('two-qubit unfinished state proof',
         'def fake := TwoQubit.Pure.of 0 0 0 0 (by sorry)\n'
         'def bad := TwoQubit.compare "Bad" [TwoQubit.Law.ideal] [{ TwoQubit.singletRecipe with prepare := .custom fake }]\n'
         '#export_scenario bad\n', 'sorryAx'),
    ]
    cases += [
        ('LF invalid record rate', 'def bad := LocalFriendlinessRecipe.Law.recordDephasing 0 2 1\n', 'debbieBound'),
        ('LF zero direction', 'def bad : LocalFriendlinessRecipe.Alternatives := ⟨TwoQubit.Basis.of 0 0, .z⟩\n', 'valid'),
        ('LF read index cannot be reassigned', 'def bad : LocalFriendlinessRecipe.Alternatives := { first := .z, second := .z, readIndex := 1 }\n', 'readIndex'),
        ('LF source cannot depend on law', 'def bad : LocalFriendlinessRecipe.Recipe := { LocalFriendlinessRecipe.reference with source := fun (_ : LocalFriendlinessRecipe.Law) => TwoQubit.Pure.of 1 0 0 0 }\n', 'error'),
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
