"""Small, dependency-free client for the Lean report format.

Loading JSON validates its structure, not its proofs. Use ``build_report`` to
build the Lean source and obtain a fresh report from that build.
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable
import html
import json
import subprocess
import sys

STATUSES = {"verifiedBound", "verifiedWitness", "verifiedToyPrediction", "unresolved", "outsideScope"}

@dataclass(frozen=True)
class Report:
    data: dict[str, Any]
    provenance: str = "Imported snapshot; JSON validation is not proof verification"

    def __post_init__(self) -> None:
        d = self.data
        if d.get("schema_version") != 1:
            raise ValueError("Unsupported report schema; expected schema_version=1")
        for key in ("scenarios", "models", "cells", "binary_profiles"):
            if not isinstance(d.get(key), list):
                raise ValueError(f"{key} must be a list")
        def ids(key: str) -> set[str]:
            values = [r.get("id") for r in d[key]]
            if any(not isinstance(v, str) or not v for v in values) or len(set(values)) != len(values):
                raise ValueError(f"{key} must have unique nonempty identifiers")
            return set(values)
        scenarios, models = ids("scenarios"), ids("models")
        pairs: set[tuple[str, str]] = set()
        for cell in d["cells"]:
            pair = cell.get("scenario"), cell.get("model")
            if pair in pairs:
                raise ValueError(f"Duplicate matrix cell: {pair}")
            pairs.add(pair)
            if pair[0] not in scenarios or pair[1] not in models:
                raise ValueError(f"Unknown scenario/model in cell: {pair}")
            status = cell.get("status")
            if status not in STATUSES:
                raise ValueError(f"Unknown evidence status: {status!r}")
            if status.startswith("verified") and not cell.get("declaration"):
                raise ValueError("A verified-status cell needs a Lean declaration reference")
            if not status.startswith("verified") and cell.get("declaration") is not None:
                raise ValueError("An unresolved/out-of-scope cell must not carry a proof label")
            if not isinstance(cell.get("result"), str) or not isinstance(cell.get("assumptions"), list):
                raise ValueError("Malformed cell result or assumptions")
        if pairs != {(s, m) for s in scenarios for m in models}:
            raise ValueError("Report must contain the full scenario-by-model product")

    def compare(self, scenarios: Iterable[str] | None = None,
                models: Iterable[str] | None = None) -> list[dict[str, Any]]:
        s = set(scenarios) if scenarios is not None else {x["id"] for x in self.data["scenarios"]}
        m = set(models) if models is not None else {x["id"] for x in self.data["models"]}
        for selected, key in ((s, "scenarios"), (m, "models")):
            unknown = selected - {x["id"] for x in self.data[key]}
            if unknown:
                raise ValueError(f"Unknown {key}: {', '.join(sorted(unknown))}")
        return [dict(c) for c in self.data["cells"] if c["scenario"] in s and c["model"] in m]

    def markdown(self, scenarios: Iterable[str] | None = None,
                 models: Iterable[str] | None = None) -> str:
        cells = self.compare(scenarios, models)
        escape = lambda x: str(x).replace("|", "\\|").replace("\n", " ")
        lines = [self.provenance, "", "| Experiment | Model | Evidence | Result |",
                 "|---|---|---|---|"]
        lines += ["| " + " | ".join(escape(c[k]) for k in ("scenario", "model", "status", "result")) + " |"
                  for c in cells]
        return "\n".join(lines) + "\n"

    def html(self) -> str:
        esc = html.escape
        cells = self.compare()
        rows = []
        for s in self.data["scenarios"]:
            cols = []
            for m in self.data["models"]:
                c = next(c for c in cells if c["scenario"] == s["id"] and c["model"] == m["id"])
                detail = c["limitation"] + "\nAssumptions: " + "; ".join(c["assumptions"])
                if c["declaration"]:
                    detail += "\nLean: " + c["declaration"]
                cols.append(f'<td class="{esc(c["status"])}"><details><summary>{esc(c["result"])}</summary>'
                            f'<p>{esc(c["status"])}</p><pre>{esc(detail)}</pre></details></td>')
            rows.append(f'<tr><th>{esc(s["id"])}<br>{esc(s["title"])}</th>{"".join(cols)}</tr>')
        heads = "".join(f'<th>{esc(m["title"])}<small>{esc(m["kind"])}</small></th>' for m in self.data["models"])
        return f'''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>Ontology Separation</title>
<style>body{{font:15px system-ui;margin:2rem;color:#182838}}h1{{margin-bottom:.2rem}}
.wrap{{overflow:auto}}table{{border-collapse:collapse;min-width:1200px}}th,td{{padding:12px;border:1px solid #d5dce2;text-align:left;vertical-align:top}}
small{{display:block;font-weight:normal;margin-top:5px}}thead th{{background:#172c42;color:white}}
.verifiedWitness,.verifiedBound{{background:#e8f5ee}}.verifiedToyPrediction{{background:#eef3ff}}
.unresolved{{background:#fff6df}}.outsideScope{{background:#f3f4f5;color:#56616b}}
pre{{white-space:pre-wrap;font:13px system-ui}}summary{{cursor:pointer}}button{{padding:8px}}
</style><h1>Ontology Separation</h1><p>Physical theories, explicit assumptions, Lean-checked mathematics.</p>
<p>{esc(self.provenance)}</p><p>Green: bound or witness. Blue: proved toy prediction. Amber: unresolved. Gray: outside adapter scope. Expand a cell for assumptions and limitations.</p>
<div class="wrap"><table><thead><tr><th>Experiment</th>{heads}</tr></thead><tbody>{"".join(rows)}</tbody></table></div>
<h2>Assumption profiles</h2><p>All 16 binary profiles are expressible. Their physical realizability is not asserted. False means negation; unspecified adds no constraint.</p></html>'''


def load_report(path: str | Path | None = None) -> Report:
    p = Path(path) if path is not None else Path(__file__).parent / "data" / "report.json"
    return Report(json.loads(p.read_text(encoding="utf-8")))


def build_report(repo: str | Path, lake: str = "lake") -> Report:
    """Build a trusted local checkout with Lean, then run its report executable."""
    repo = Path(repo).resolve()
    subprocess.run([lake, "build"], cwd=repo, check=True)
    subprocess.run([lake, "build", "Tests"], cwd=repo, check=True)
    subprocess.run([sys.executable, str(repo / "scripts/audit.py")], cwd=repo, check=True)
    binary = repo / ".lake" / "build" / "bin" / "ontology-separation"
    result = subprocess.run([str(binary)], cwd=repo, check=True, capture_output=True, text=True)
    return Report(json.loads(result.stdout), "Fresh report from a successful local Lean build, tests, and axiom audit")
