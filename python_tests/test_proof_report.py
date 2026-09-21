import json
import unittest
from itertools import product
from ontology_separation.proof_report import parse_exports, parse_profiles, profile_table, render, PREFIX
class ProofReportTests(unittest.TestCase):
    def test_exact_statement_and_html_escaping(self):
        record = dict(declaration='My.bound', statement='∀ x, x < 2 ∧ <script>', axioms=[], kind='theorem')
        page = render(parse_exports(PREFIX+json.dumps(record)), 'source<.lean')
        self.assertIn('&lt;script&gt;', page)
        self.assertNotIn('<script>', page)
        self.assertIn('source&lt;.lean', page)
    def test_missing_exports_fail(self):
        with self.assertRaises(ValueError): parse_exports('Build successful')
    def test_unknown_axioms_fail(self):
        with self.assertRaises(ValueError):
            parse_exports(PREFIX+json.dumps(dict(declaration='fake', statement='False', axioms=['sorryAx'], kind='theorem')))
    def test_duplicates_fail(self):
        line=PREFIX+json.dumps(dict(declaration='a', statement='True', axioms=[], kind='theorem'))
        with self.assertRaises(ValueError): parse_exports(line+'\n'+line)
    def test_non_theorem_and_empty_statement_fail(self):
        for kind, statement in [('witness','True'),('theorem','')]:
            with self.assertRaises(ValueError):
                parse_exports(PREFIX+json.dumps(dict(declaration='a',statement=statement,axioms=[],kind=kind)))
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
    def test_theorem_cli_does_not_load_legacy_snapshot(self):
        from unittest.mock import patch
        from contextlib import redirect_stdout
        from io import StringIO
        from ontology_separation.cli import main
        with patch('ontology_separation.proof_report.write_report',return_value=1) as write:
            with patch('ontology_separation.cli.load_report',side_effect=AssertionError('legacy fallback')):
                with redirect_stdout(StringIO()):
                    self.assertEqual(main(['theorem-report','Publish.lean','-o','results.html']),0)
            self.assertEqual(write.call_count,1)
