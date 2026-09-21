from pathlib import Path
import re
import runpy
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
stage=runpy.run_path(str(ROOT/'scripts/build_pages.py'))['stage']

class PagesTests(unittest.TestCase):
    def test_staged_views_have_resolving_links_and_revision(self):
        with tempfile.TemporaryDirectory() as d:
            dest=Path(d)/'site'
            stage(ROOT,dest,'a'*40)
            self.assertTrue((dest/'two-qubit-comparison.html').exists())
            for p in dest.glob('*.html'):
                text=p.read_text()
                self.assertIn('source revision aaaaaaa',text)
                for link in re.findall(r'href="([^"]+)"',text):
                    if '://' not in link and not link.startswith('#'):
                        self.assertTrue((p.parent/link.split('#')[0]).is_file(),(p,link))
            self.assertIn('/blob/'+('a'*40)+'/docs/START_HERE.md',(dest/'index.html').read_text())
    def test_rejects_unversioned_or_existing_destination(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(ValueError):stage(ROOT,Path(d)/'new','main')
            with self.assertRaises(ValueError):stage(ROOT,Path(d),'a'*40)
