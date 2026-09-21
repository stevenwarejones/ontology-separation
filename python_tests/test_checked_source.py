from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
import tempfile
import unittest
from ontology_separation.checked_source import project_for, run_lean, validate_output, atomic_write_html

class CheckedSourceTests(unittest.TestCase):
    def test_nearest_project_and_dependency_build(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); (root/'lakefile.toml').write_text('name="parent"')
            nested=root/'child';nested.mkdir();(nested/'lakefile.toml').write_text('name="child"')
            source=nested/'Study.lean';source.write_text('example : True := by trivial')
            self.assertEqual(project_for(source),nested)
            with patch('ontology_separation.checked_source.subprocess.run',
                       return_value=SimpleNamespace(returncode=0,stdout='checked',stderr='')) as run:
                self.assertEqual(run_lean(source),'checked')
                self.assertEqual(run.call_args.args[0],['lake','lean',str(source),'--','-DautoImplicit=false'])
                self.assertEqual(run.call_args.kwargs['cwd'],nested)
    def test_missing_project_and_missing_source(self):
        with tempfile.TemporaryDirectory() as d:
            source=Path(d)/'X.lean'
            with self.assertRaisesRegex(ValueError,'existing Lean'):project_for(source)
            source.write_text('')
            with self.assertRaisesRegex(ValueError,'No Lake project'):project_for(source)
    def test_source_project_and_hardlink_output_protection(self):
        with tempfile.TemporaryDirectory() as d:
            source=Path(d)/'Study.lean';source.write_text('proof')
            with self.assertRaisesRegex(ValueError,'overwrite'):validate_output(source,source)
            with self.assertRaisesRegex(ValueError,'.html'):validate_output(source,Path(d)/'lakefile.toml')
            alias=Path(d)/'alias.html';alias.hardlink_to(source)
            with self.assertRaisesRegex(ValueError,'overwrite'):validate_output(source,alias)
    def test_atomic_replace_failure_preserves_previous_file(self):
        with tempfile.TemporaryDirectory() as d:
            output=Path(d)/'report.html';output.write_text('previous')
            with patch('ontology_separation.checked_source.os.replace',side_effect=OSError('full disk')):
                with self.assertRaises(OSError):atomic_write_html(output,'new')
            self.assertEqual(output.read_text(),'previous')
            self.assertEqual(list(Path(d).iterdir()),[output])
            atomic_write_html(output,'new');self.assertEqual(output.read_text(),'new')
    def test_failed_check_mentions_stale_report(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'lakefile.toml').write_text('');source=root/'X.lean';source.write_text('')
            with patch('ontology_separation.checked_source.subprocess.run',
                       return_value=SimpleNamespace(returncode=1,stdout='bad proof',stderr='')):
                with self.assertRaisesRegex(ValueError,'may be stale'):run_lean(source)
