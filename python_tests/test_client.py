"""Contract tests for the public interface and Lean-exported evidence matrix."""
from copy import deepcopy
from pathlib import Path
import contextlib
import io
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "python"))
from ontology_separation import Report, load_report
from ontology_separation.cli import main

class ReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = load_report()

    def test_complete_matrix_and_original_scenarios(self):
        r = self.report
        self.assertEqual(len(r.data["scenarios"]), 14)
        self.assertEqual(len(r.data["models"]), 7)
        self.assertEqual(len(r.data["cells"]), 98)
        self.assertEqual({s["id"] for s in r.data["scenarios"]},
                         {f"B{i:02d}" for i in range(1, 5)} | {f"P{i:02d}" for i in range(1, 11)})

    def test_echo_is_distinguishing_but_leakage_is_not(self):
        models = ["unitary_memory", "dephased_memory", "partial_memory"]
        echo = self.report.compare(["B04"], models)
        self.assertEqual({c["result"] for c in echo}, {"1", "1/2", "3/4"})
        leaked = self.report.compare(["P02"], models)
        self.assertEqual({c["result"] for c in leaked}, {"1/2"})
        self.assertTrue(all(c["status"] == "verifiedToyPrediction" for c in leaked))

    def test_research_extensions_are_not_native_predictions(self):
        for cell in self.report.compare(["P01", "P03", "P05", "P06", "P07", "P08", "P10"]):
            self.assertEqual(cell["status"], "verifiedConditional")
            self.assertTrue(cell["declaration"])
            self.assertTrue(any("ADDITIONAL LAW" in a for a in cell["assumptions"]))
            self.assertTrue(cell["limitation"])

    def test_unknown_selection_fails(self):
        with self.assertRaisesRegex(ValueError, "Unknown scenarios"):
            self.report.compare(["not-an-experiment"])
        with self.assertRaisesRegex(ValueError, "Unknown models"):
            self.report.compare(models=["all-interpretations"])

    def test_duplicate_and_missing_cells_rejected(self):
        data = deepcopy(self.report.data)
        data["cells"].append(data["cells"][0])
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            Report(data)
        data = deepcopy(self.report.data)
        data["cells"].pop()
        with self.assertRaisesRegex(ValueError, "full scenario"):
            Report(data)

    def test_verified_label_requires_reference_but_json_does_not_prove_it(self):
        data = deepcopy(self.report.data)
        cell = next(c for c in data["cells"] if c["status"].startswith("verified"))
        cell["declaration"] = None
        with self.assertRaisesRegex(ValueError, "declaration reference"):
            Report(data)
        self.assertIn("not proof verification", self.report.provenance)

    def test_profiles_express_all_binary_combinations(self):
        profiles = self.report.data["binary_profiles"]
        self.assertEqual(len(profiles), 16)
        self.assertEqual(len({json.dumps(p, sort_keys=True) for p in profiles}), 16)
        self.assertIn("realizability", self.report.data["profile_notice"])

    def test_html_escapes_user_content(self):
        data = deepcopy(self.report.data)
        data["scenarios"][0]["title"] = '<script>alert("x")</script>'
        rendered = Report(data).html()
        self.assertNotIn('<script>', rendered)
        self.assertIn('&lt;script&gt;', rendered)
        self.assertIn('<details>', rendered)

    def test_cli_filter_and_error(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(main(["compare", "B02", "--models", "local_friendliness"]), 0)
        self.assertIn("G <= 6", out.getvalue())
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            main(["compare", "B99"])
        self.assertEqual(error.exception.code, 2)

    def test_cli_html_file(self):
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stdout(io.StringIO()):
            p = Path(tmp) / "matrix.html"
            self.assertEqual(main(["html", str(p)]), 0)
            self.assertIn("Local Friendliness", p.read_text())

if __name__ == "__main__":
    unittest.main()
