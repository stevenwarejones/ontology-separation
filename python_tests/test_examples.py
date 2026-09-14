"""Meaningful contract checks for assumption/evidence views and portable sources."""
from pathlib import Path
from tempfile import TemporaryDirectory
from copy import deepcopy
import json
import subprocess
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from ontology_separation import load_report, Report
from ontology_separation.ontology import AXES, profiles, profile_rule, experiment_html, write_examples

class ExamplesTests(unittest.TestCase):
    def test_profiles_have_all_combinations_in_every_axis_slice(self):
        values=profiles()
        self.assertEqual(len({tuple(p[a] for a in AXES) for p in values}),16)
        for x in AXES:
            for y in AXES:
                if x == y: continue
                remaining=[a for a in AXES if a not in (x,y)]
                for a in (True,False):
                    for b in (True,False):
                        selected=[p for p in values if p[remaining[0]]==a and p[remaining[1]]==b]
                        self.assertEqual({(p[x],p[y]) for p in selected},{(True,True),(True,False),(False,True),(False,False)})

    def test_bell_rule_requires_conjunction_and_bridge(self):
        for p in profiles():
            rule=profile_rule('B01',p)
            applies=p['realism'] and p['locality'] and p['measurementIndependent']
            self.assertEqual('S ≤ 2' in rule,applies)
            if applies: self.assertIn('bridge required',rule)
        self.assertTrue(all('No prediction' in profile_rule('P07',p) for p in profiles()))

    def test_conditional_predictions_are_labeled_and_complete(self):
        report=load_report()
        self.assertEqual(len(report.compare()),98)
        self.assertNotIn('requiresExtension',{c['status'] for c in report.compare()})
        for c in report.compare():
            if c['status']=='verifiedConditional':
                self.assertTrue(c['declaration'])
                self.assertTrue(c['assumptions'])
                self.assertTrue(any('ADDED' in x or 'ADDITIONAL' in x for x in c['assumptions']))

    def test_explicit_noise_extension_endpoints(self):
        from fractions import Fraction
        r=load_report()
        values={c['model']:Fraction(c['result'].split(' = ')[-1]) for c in r.compare(['B01'],['unitary_memory','dephased_memory','partial_memory'])}
        self.assertEqual(values['unitary_memory'],Fraction(1502,625))
        self.assertEqual(values['dephased_memory'],Fraction(14,25))
        self.assertEqual(values['partial_memory'],(values['unitary_memory']+values['dephased_memory'])/2)

    def test_extensions_require_scope_and_law(self):
        data=deepcopy(load_report().data)
        data['extensions'][0]['requiredLaw']=''
        with self.assertRaisesRegex(ValueError,'Extension needs'):Report(data)

    def test_all_examples_written_with_static_profiles_and_safe_json(self):
        report=load_report()
        with TemporaryDirectory() as d:
            write_examples(report,d)
            files=list(Path(d).glob('*.html'))
            self.assertEqual(len(files),17)
            for s in report.data['scenarios']:
                content=(Path(d)/(s['id']+'.html')).read_text()
                self.assertIn('all-profiles',content)
                self.assertIn('ProfileBridge',content)
                self.assertIn('type="application/json"',content)
                self.assertIn('not a prediction entailed', (Path(d)/'matrix.html').read_text())
        bad=deepcopy(report.data['scenarios'][0]);bad['title']='</script><script>alert(1)</script>'
        self.assertNotIn(bad['title'],experiment_html(report,bad))

    def test_no_case_colliding_repository_paths(self):
        result=subprocess.run(['git','ls-files','--cached','--others','--exclude-standard'],cwd=ROOT,text=True,capture_output=True,check=True)
        seen={}
        for path in result.stdout.splitlines():
            parts=Path(path).parts
            for i in range(1,len(parts)+1):
                prefix='/'.join(parts[:i]);key=prefix.casefold()
                self.assertTrue(key not in seen or seen[key]==prefix, f'Case collision: {prefix} / {seen.get(key)}')
                seen[key]=prefix

if __name__=='__main__':unittest.main()
