#!/usr/bin/env python3
"""Regenerate the snapshot from the already-built Lean executable."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
from ontology_separation.client import Report
from ontology_separation.ontology import write_examples

binary = ROOT / ".lake/build/bin/ontology-separation"
result = subprocess.run([str(binary)], cwd=ROOT, capture_output=True, text=True, check=True)
report = Report(json.loads(result.stdout), "Snapshot exported from the Lean executable; recheck with lake build Tests")
out = ROOT / "python/ontology_separation/data/report.json"
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(report.data, indent=2) + "\n")
(ROOT / "docs/MATRIX.md").write_text(report.markdown())
(ROOT / "docs/matrix.html").write_text(report.html())
write_examples(report, ROOT / "examples")
print(f"Exported {len(report.data['cells'])} cells from {len(report.data['scenarios'])} experiments")
