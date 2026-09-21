from pathlib import Path
from unittest.mock import patch
import tempfile
import unittest
from ontology_separation.scaffold import create_scenario
from ontology_separation.cli import main

class ScaffoldTests(unittest.TestCase):
    def test_scaffold_and_refuse_overwrite(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'lakefile.toml').write_text('')
            output=root/'Study.lean'
            create_scenario('MyStudy',output)
            original=output.read_text()
            self.assertIn('#export_scenario MyStudy.comparison',original)
            self.assertNotIn('sorry',original)
            self.assertNotIn('predicted',original)
            with self.assertRaisesRegex(ValueError,'overwrite'):create_scenario('OtherStudy',output)
            self.assertEqual(output.read_text(),original)
    def test_invalid_names_extensions_and_missing_project(self):
        with tempfile.TemporaryDirectory() as d:
            output=Path(d)/'Study.lean'
            for name in ['abc','A;bad','A\nB','Prop','Type','Sort']:
                with self.assertRaises(ValueError):create_scenario(name,output)
            with self.assertRaisesRegex(ValueError,'Lake project'):create_scenario('Good',output)
            with self.assertRaisesRegex(ValueError,'.lean'):create_scenario('Good',Path(d)/'README.md')
            self.assertFalse(output.exists())
    def test_cli_no_bundled_catalog(self):
        with patch('ontology_separation.scaffold.create_scenario',return_value=Path('Study.lean')) as create, \
             patch('ontology_separation.cli.load_report',side_effect=AssertionError('bundled lookup')):
            self.assertEqual(main(['new-scenario','MyStudy','-o','Study.lean']),0)
            create.assert_called_once_with('MyStudy',Path('Study.lean'))

    def test_two_qubit_starter_and_cli(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root/'lakefile.toml').write_text('')
            target = root/'Bell.lean'
            self.assertEqual(main(['new-scenario', 'BellStudy', '--backend', 'two-qubit',
                                   '-o', str(target)]), 0)
            source = target.read_text()
            self.assertIn('open OntologySeparation.TwoQubit', source)
            self.assertIn('#export_scenario BellStudy.comparison', source)
            self.assertIn('.cnot .alice', source)
            self.assertNotIn('sorry', source)
            with self.assertRaisesRegex(ValueError, 'overwrite'):
                create_scenario('BellStudy', target, backend='two-qubit')
            with self.assertRaisesRegex(ValueError, 'backend'):
                create_scenario('Bad', root/'Bad.lean', backend='three-qubit')
            self.assertFalse((root/'Bad.lean').exists())

    def test_lf_scaffold(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'lakefile.toml').touch()
            output=root/'Friends.lean'
            create_scenario('Friends',output,backend='local-friendliness')
            text=output.read_text()
            self.assertIn('import OntologySeparation.LocalFriendliness',text)
            self.assertIn('fully_dephased_realizes_profile',text)
            self.assertNotIn('sorry',text)
