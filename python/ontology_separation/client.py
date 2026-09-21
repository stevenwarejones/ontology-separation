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

from .evidence import validate_claim, result_text, evidence_label

@dataclass(frozen=True)
class Report:
    data: dict[str, Any]
    provenance: str = "Imported snapshot; JSON validation is not proof verification"

    def __post_init__(self) -> None:
        d = self.data
        if d.get("schema_version") != 3:
            raise ValueError("Unsupported report schema; expected schema_version=3")
        for key in ("scenarios", "models", "cells", "binary_profiles", "extensions"):
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
            if cell.get('applicability') not in {'native', 'additional'}:
                raise ValueError('Missing applicability scope')
            if not isinstance(cell.get('assumptions'), list) or any(not isinstance(a, str) for a in cell['assumptions']):
                raise ValueError('Malformed assumptions')
            if cell['applicability'] == 'additional' and not cell['assumptions']:
                raise ValueError('Additional-law result needs explicit assumptions')
            claim = cell.get('claim')
            if claim is not None:
                validate_claim(claim)
            if not isinstance(cell.get('supporting'), list):
                raise ValueError('Missing supporting-claim list')
            for claim_item in cell['supporting']:
                validate_claim(claim_item)
            derived = {'status': claim['kind'] if claim else 'unavailable',
                       'result': result_text(claim) if claim else 'No interpretation supplied',
                       'declaration': 'OntologySeparation.Catalog.matrix' if claim else None}
            for key, value in derived.items():
                if key in cell and cell[key] != value:
                    raise ValueError('Display metadata does not match its proof-bearing claim: ' + key)
                cell[key] = value
        extension_ids = set()
        for e in d["extensions"]:
            if e.get("scenario") not in scenarios or e["scenario"] in extension_ids:
                raise ValueError("Unknown or duplicate extension scenario")
            extension_ids.add(e["scenario"])
            if not all(isinstance(e.get(k), str) and e[k] for k in
                       ("requiredLaw", "scope", "title")):
                raise ValueError("Extension needs its law and scope")
            validate_claim(e.get('claim'))
            if not isinstance(e.get('supporting'), list):
                raise ValueError('Extension needs supporting-claim list')
            for claim in e['supporting']:
                validate_claim(claim)
            derived = {'result': result_text(e['claim']), 'declaration': 'OntologySeparation.Catalog.extensions'}
            for key, value in derived.items():
                if key in e and e[key] != value:
                    raise ValueError('Extension display does not match its claim')
                e[key] = value
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
        lines = [self.provenance, "", "| Experiment | Model | Applicability | Evidence | Result |",
                 "|---|---|---|---|---|"]
        lines += ["| " + " | ".join(escape(x) for x in (
            c['scenario'], c['model'], 'Additional laws' if c['applicability'] == 'additional' else 'Selected model/class',
            evidence_label(c['claim']), c['result'])) + " |" for c in cells]
        return "\n".join(lines) + "\n"

    def html(self, index_href: str | None = None) -> str:
        esc = html.escape
        nav = f'<p><a href="{esc(index_href, quote=True)}">Experiment and ontology views</a></p>' if index_href else ""
        cells = self.compare()
        rows = []
        for s in self.data["scenarios"]:
            cols = []
            for m in self.data["models"]:
                c = next(c for c in cells if c["scenario"] == s["id"] and c["model"] == m["id"])
                detail = c["limitation"] + "\nAssumptions: " + "; ".join(c["assumptions"])
                if c["declaration"]:
                    detail += "\nLean proposition: " + c["claim"]["statement"]
                    for extra in c["supporting"]:
                        detail += "\n\n" + evidence_label(extra) + ":\n" + extra["statement"]
                summary = 'Checked theorem — expand for full statement' if c['status'] == 'theorem' else c['result']
                badge = '<strong>Additional laws required</strong><br>' if c['applicability'] == 'additional' else ''
                cols.append(f'<td class="{esc(c["status"])}">{badge}<details><summary>{esc(summary)}</summary>'
                            f'<p>{esc(evidence_label(c["claim"]))}</p><pre>{esc(detail)}</pre></details></td>')
            rows.append(f'<tr><th>{esc(s["id"])}<br>{esc(s["title"])}</th>{"".join(cols)}</tr>')
        heads = "".join(f'<th>{esc(m["title"])}<small>{esc(m["kind"])}</small></th>' for m in self.data["models"])
        return f'''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>Ontology Separation</title>
<style>body{{font:15px system-ui;margin:2rem;color:#182838}}h1{{margin-bottom:.2rem}}
.wrap{{overflow:auto}}table{{border-collapse:collapse;min-width:1200px}}th,td{{padding:12px;border:1px solid #d5dce2;text-align:left;vertical-align:top}}
small{{display:block;font-weight:normal;margin-top:5px}}thead th{{background:#172c42;color:white}}
.witness,.realizedBound{{background:#e8f5ee}}.exact{{background:#eef3ff}}
.bound,.theorem{{background:#fff6df}}.unavailable{{background:#f3f4f5;color:#56616b}}
pre{{white-space:pre-wrap;font:13px system-ui}}summary{{cursor:pointer}}button{{padding:8px}}
</style><h1>Ontology Separation</h1><p>Physical theories, explicit assumptions, Lean-checked mathematics.</p>
<p><strong>These cells are not unconditional predictions from complete physical universes.</strong> A conditional cell needs its stated additional laws; a bound alone does not prove a model exists.</p>
<p>{esc(self.provenance)}</p><p>Green: a bound with a satisfying model, or a realized witness. Blue: exact value. Amber: a bound without an existence certificate, or a general theorem. Additional laws are flagged separately. Gray: missing interpretation. Expand a cell for assumptions and limitations.</p>
<div class="wrap"><table><thead><tr><th>Experiment</th>{heads}</tr></thead><tbody>{"".join(rows)}</tbody></table></div>
{nav}<h2>Assumption profiles</h2><p>All 16 binary profiles are expressible. Their physical realizability is not asserted. False means negation; unspecified adds no constraint.</p></html>'''


def load_report(path: str | Path | None = None) -> Report:
    p = Path(path) if path is not None else Path(__file__).parent / "data" / "report.json"
    return Report(json.loads(p.read_text(encoding="utf-8")))


def build_report(repo: str | Path, lake: str = "lake") -> Report:
    """Build a trusted local checkout with Lean, then export its proof-bearing catalog."""
    repo = Path(repo).resolve()
    subprocess.run([lake, "build"], cwd=repo, check=True)
    subprocess.run([lake, "build", "Tests"], cwd=repo, check=True)
    subprocess.run([sys.executable, str(repo / "scripts/audit.py")], cwd=repo, check=True)
    from .checked_source import run_lean
    return parse_catalog(run_lean(repo / 'examples/Catalog.lean', lake=lake),
                         "Fresh report from checked Lean source, tests and axiom audit")


def parse_catalog(stdout: str, provenance: str = "Exported by the checked Lean catalog command") -> Report:
    prefix = 'ONTOLOGY_CATALOG '
    lines = [line[len(prefix):] for line in stdout.splitlines() if line.startswith(prefix)]
    if len(lines) != 1:
        raise ValueError('Expected exactly one checked catalog export')
    return Report(json.loads(lines[0]), provenance)
