#!/usr/bin/env python3
"""Check local proof policy and transitive axioms of all registered report claims."""
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
problems = []
for p in (root / "OntologySeparation").rglob("*.lean"):
    text = re.sub(r"/\-.*?\-/", "", p.read_text(), flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", text):
        problems.append(f"Forbidden proof construct: {p.relative_to(root)}")
result = subprocess.run(["lake", "env", "lean", "Tests/Audit.lean"], cwd=root,
                        capture_output=True, text=True)
if result.returncode:
    problems.append(result.stdout + result.stderr)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for block in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout):
    axioms = {a.strip() for a in block.split(",") if a.strip()}
    if axioms - allowed:
        problems.append("Unexpected axioms: " + ", ".join(sorted(axioms - allowed)))
if "sorryAx" in result.stdout:
    problems.append("Unfinished proof dependency")
expected = (root / "Tests/Audit.lean").read_text().count("#print axioms")
if result.stdout.count("depends on axioms") + result.stdout.count("does not depend on any axioms") != expected:
    problems.append("Audit did not report every expected claim")
if problems:
    print("\n".join(problems), file=sys.stderr)
    raise SystemExit(1)
(root / "docs/AXIOM_AUDIT.txt").write_text(result.stdout)
print("Proof policy and transitive axiom audit passed")
