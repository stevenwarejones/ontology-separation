#!/usr/bin/env python3
"""Regenerate every catalog view through the checked claim exporter."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
from ontology_separation.client import parse_catalog
from ontology_separation.checked_source import run_lean
from ontology_separation.ontology import write_examples

report = parse_catalog(run_lean(ROOT / 'examples/Catalog.lean'))
out = ROOT / "python/ontology_separation/data/report.json"
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(report.data, indent=2) + "\n")
(ROOT / "docs/MATRIX.md").write_text(report.markdown())
(ROOT / "docs/matrix.html").write_text(report.html())
write_examples(report, ROOT / "examples")
print(f"Exported {len(report.data['cells'])} cells from {len(report.data['scenarios'])} experiments")
