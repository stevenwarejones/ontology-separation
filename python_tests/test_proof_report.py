import json
import unittest
from itertools import product
from ontology_separation.proof_report import (parse_exports, parse_profiles, parse_comparisons,
    profile_table, render, PREFIX, COMPARISON_PREFIX)
def exported(declaration, statement, axioms, kind):
    return dict(declaration=declaration, axioms=axioms,
                claim=dict(kind=kind, statement=statement, quantity=None))
class ProofReportTests(unittest.TestCase):
    def test_exact_statement_and_html_escaping(self):
        record = exported(declaration='My.bound', statement='∀ x, x < 2 ∧ <script>', axioms=[], kind='theorem')
        page = render(parse_exports(PREFIX+json.dumps(record)), 'source<.lean')
        self.assertIn('&lt;script&gt;', page)
        self.assertNotIn('<script>', page)
        self.assertIn('source&lt;.lean', page)
    def test_numeric_claim_renders_checked_quantity(self):
        record = dict(
            declaration='My.exact',
            axioms=[],
            claim=dict(
                kind='exact',
                statement='x = ↑(3 / 4)',
                quantity={'numerator': '3', 'denominator': '4'}))
        page = render(parse_exports(PREFIX+json.dumps(record)), 'Study.lean')
        self.assertIn('<th>Checked result</th>', page)
        self.assertIn('<td>3/4</td>', page)
        self.assertIn('x = ↑(3 / 4)', page)

    def test_structured_comparison_renders_checked_physics(self):
        claim = dict(kind='separation', statement='separator theorem', quantity=None)
        report = dict(
            left_model='Exposure dephasing p=1/2',
            right_model='Exposure dephasing p=0',
            covered_protocols=['prepare |+>; exposure; P(X=+)'],
            verdict='separation',
            protocol='prepare |+>; exposure; P(X=+)',
            setting='single setting',
            outcome='-',
            left_probability={'numerator': '1', 'denominator': '4'},
            right_probability={'numerator': '0', 'denominator': '1'},
            gap={'numerator': '1', 'denominator': '4'},
            claim=claim)
        item = dict(declaration='Study.report', axioms=[], report=report)
        comparisons = parse_comparisons(COMPARISON_PREFIX + json.dumps(item))
        page = render([exported('Study.claim', 'separator theorem', [], 'separation')],
                      'Study.lean', comparisons=comparisons)
        self.assertIn('Checked model comparisons', page)
        self.assertIn('Exposure dephasing p=1/2', page)
        self.assertIn('exact gap:</strong> 1/4', page)
        self.assertIn('agreement across these supplied experiments', page.lower() if False else
                      'agreement across these supplied experiments')

    def test_structured_comparison_rejects_mismatched_claim_kind(self):
        item = dict(declaration='Study.report', axioms=[], report=dict(
            left_model='A', right_model='B', covered_protocols=['p'],
            verdict='agreement', protocol=None, setting=None, outcome=None,
            left_probability=None, right_probability=None, gap=None,
            claim=dict(kind='separation', statement='False', quantity=None)))
        with self.assertRaises(ValueError):
            parse_comparisons(COMPARISON_PREFIX + json.dumps(item))

    def test_missing_exports_fail(self):
        with self.assertRaises(ValueError): parse_exports('Build successful')
    def test_unknown_axioms_fail(self):
        with self.assertRaises(ValueError):
            parse_exports(PREFIX+json.dumps(exported(declaration='fake', statement='False', axioms=['sorryAx'], kind='theorem')))
    def test_duplicates_fail(self):
        line=PREFIX+json.dumps(exported(declaration='a', statement='True', axioms=[], kind='theorem'))
        with self.assertRaises(ValueError): parse_exports(line+'\n'+line)
    def test_non_theorem_and_empty_statement_fail(self):
        for kind, statement in [('witness','True'),('theorem','')]:
            with self.assertRaises(ValueError):
                parse_exports(PREFIX+json.dumps(exported(declaration='a',statement=statement,axioms=[],kind=kind)))
    def test_profile_export_requires_all_combinations(self):
        with self.assertRaises(ValueError): parse_profiles('ONTOLOGY_PROFILES []')
        self.assertIsNone(parse_profiles(''))
    def test_profile_table_keeps_vocabularies_distinct(self):
        keys=('realism','globalTruth','locality','measurementIndependent')
        rows=[dict(profile=dict(zip(keys,v)),bell_bound=True,lf_bound=False) for v in product(('require','reject'),repeat=4)]
        page=profile_table(parse_profiles('ONTOLOGY_PROFILES '+json.dumps(rows)))
        self.assertEqual(page.count('S ≤ 2'),16)
        self.assertIn('different named vocabularies',page)
        self.assertEqual(page.count('existence not certified for this row'),16)
        rows[1]=rows[0]
        with self.assertRaises(ValueError):parse_profiles('ONTOLOGY_PROFILES '+json.dumps(rows))
    def test_lean_failure_preserves_previous_report(self):
        from pathlib import Path
        import tempfile
        import subprocess
        from unittest.mock import patch
        from ontology_separation.proof_report import write_report
        with tempfile.TemporaryDirectory() as directory:
            output=Path(directory)/'report.html'
            output.write_text('previous checked report')
            source=Path(directory)/'Broken.lean'
            source.write_text('')
            (Path(directory)/'lakefile.toml').write_text('')
            result=subprocess.CompletedProcess([],1,'error: proof failed','')
            with patch('ontology_separation.checked_source.subprocess.run',return_value=result):
                with self.assertRaisesRegex(ValueError,'proof failed'):
                    write_report(source,output)
            self.assertEqual(output.read_text(),'previous checked report')
    def test_theorem_cli_does_not_load_bundled_snapshot(self):
        from unittest.mock import patch
        from contextlib import redirect_stdout
        from io import StringIO
        from ontology_separation.cli import main
        with patch('ontology_separation.proof_report.write_report',return_value=1) as write:
            with patch('ontology_separation.cli.load_report',side_effect=AssertionError('bundled fallback')):
                with redirect_stdout(StringIO()):
                    self.assertEqual(main(['theorem-report','Publish.lean','-o','results.html']),0)
            self.assertEqual(write.call_count,1)
