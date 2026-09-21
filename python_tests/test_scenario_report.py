from pathlib import Path
from types import SimpleNamespace
import json
import tempfile
import unittest
from unittest.mock import patch
from ontology_separation.scenario_report import parse_comparison, render, write_report
from ontology_separation.cli import main


def exact(n, d):
    return {'kind':'exact','quantity':{'numerator':n,'denominator':d},'statement':'experiment.score = value'}

def record():
    return {'declaration':'Example.table','type':'Scenario.Comparison Example.scenario',
            'comparison':{'schema':'ontology-scenario-v2','title':'<sample>', 'description':'<script>x</script>',
                          'models':['A','B'],'protocols':['P','Q'],
                          'values':[[exact('1','1'),exact('0','1')],
                                    [exact('3','4'),exact('5','8')]]}}
def output(r):
    return 'ONTOLOGY_SCENARIO '+json.dumps(r)+'\n'

class ScenarioTests(unittest.TestCase):
    def test_exact_values_and_escaped_metadata(self):
        r=parse_comparison(output(record()))
        h=render(r,'Example.lean',[])
        self.assertIn('<td>5/8</td>',h)
        self.assertIn('&lt;script&gt;',h)
        self.assertNotIn('<script>',h)
    def test_missing_duplicate_and_malformed_exports(self):
        for s in ('',output(record())*2,'ONTOLOGY_SCENARIO {}'):
            with self.assertRaises(ValueError): parse_comparison(s)
    def test_reject_incomplete_or_ambiguous_grids(self):
        for key,value in [('models',[]),('models',['A','A']),('models',['A',' A ']),('models',['A B','A  B']),('protocols',['']),('values',[]),
                          ('values',[[exact('1','1')]])]:
            r=record();r['comparison'][key]=value
            with self.assertRaises(ValueError): parse_comparison(output(r))
    def test_reject_invalid_rationals(self):
        for n,d in [('1','0'),('1','-2'),('1.5','2'),(1,'2'),('x','2')]:
            r=record();r['comparison']['values'][0][0]=exact(n,d)
            with self.assertRaises(ValueError): parse_comparison(output(r))
    def test_large_rationals_do_not_round(self):
        r=record();r['comparison']['values'][0][0]=exact('9007199254740993','2')
        self.assertIn('9007199254740993/2',render(parse_comparison(output(r)),'X',[]))
    def test_failed_lean_or_parse_preserves_previous_report(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'report.html';p.write_text('previous')
            source=Path(d)/'X.lean';source.write_text('')
            (Path(d)/'lakefile.toml').write_text('')
            for response in [SimpleNamespace(returncode=1,stdout='',stderr='proof failed'),
                             SimpleNamespace(returncode=0,stdout='bad output',stderr='')]:
                with patch('ontology_separation.checked_source.subprocess.run',return_value=response):
                    with self.assertRaises(ValueError): write_report(source,p)
                self.assertEqual(p.read_text(),'previous')
    def test_successful_report(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'out.html'
            source=Path(d)/'X.lean';source.write_text('')
            (Path(d)/'lakefile.toml').write_text('')
            with patch('ontology_separation.checked_source.subprocess.run',
                       return_value=SimpleNamespace(returncode=0,stdout=output(record()),stderr='')):
                self.assertEqual(write_report(source,p),4)
            self.assertIn('Example.table',p.read_text())
    def test_cli_avoids_bundled_catalog(self):
        with patch('ontology_separation.scenario_report.write_report',return_value=12) as w, \
             patch('ontology_separation.cli.load_report',side_effect=AssertionError('bundled lookup')):
            self.assertEqual(main(['scenario-report','Study.lean','-o','table.html']),0)
            w.assert_called_once_with(Path('Study.lean'),Path('table.html'))
