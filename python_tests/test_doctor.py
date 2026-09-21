from pathlib import Path
from unittest.mock import patch
import tempfile
import unittest
from ontology_separation.doctor import diagnose
from ontology_separation.cli import main

class DoctorTests(unittest.TestCase):
    def test_missing_project_never_runs_tools(self):
        with tempfile.TemporaryDirectory() as d, patch('subprocess.run') as run:
            self.assertIn('not found', diagnose(Path(d)))
            run.assert_not_called()
    def test_missing_lake(self):
        with tempfile.TemporaryDirectory() as d, patch('shutil.which', return_value=None):
            root=Path(d); (root/'lakefile.toml').touch()
            text=diagnose(root)
            self.assertIn('Lake: not on PATH',text)
            self.assertIn('cache get',text)
    def test_cache_and_shim_presence_do_not_execute_or_claim_verification(self):
        with tempfile.TemporaryDirectory() as d, patch('shutil.which', return_value='/bin/lake'), patch('subprocess.run') as run:
            root=Path(d); (root/'lakefile.toml').touch()
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.30.0')
            sentinel=root/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Real/Basic.olean'
            sentinel.parent.mkdir(parents=True);sentinel.touch()
            text=diagnose(root)
            self.assertIn('completeness not checked',text)
            self.assertIn('does not verify proofs',text)
            self.assertIn('not executed',text)
            run.assert_not_called()
    def test_cli_does_not_load_catalog(self):
        with patch('ontology_separation.doctor.diagnose',return_value='ready'), \
             patch('ontology_separation.cli.load_report',side_effect=AssertionError):
            self.assertEqual(main(['doctor']),0)
