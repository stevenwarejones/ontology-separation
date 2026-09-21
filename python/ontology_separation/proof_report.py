"""Export actual Lean claim propositions from trusted local source to offline HTML.
Usage: python -m ontology_separation.proof_report examples/Publish.lean -o report.html
An HTML/JSON snapshot is not an authenticated proof; recheck the Lean source.
"""
from __future__ import annotations
import argparse
import html
import json
from pathlib import Path
from .checked_source import run_lean, validate_output, atomic_write_html

PREFIX = "ONTOLOGY_CLAIM "
from .evidence import validate_claim, evidence_label, result_text
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXES = ("realism", "globalTruth", "locality", "measurementIndependent")


def parse_exports(stdout: str) -> list[dict]:
    records, seen = [], set()
    for line in stdout.splitlines():
        if not line.startswith(PREFIX):
            continue
        r = json.loads(line[len(PREFIX):])
        if (not isinstance(r, dict) or not isinstance(r.get('declaration'), str)
                or not isinstance(r.get('axioms'), list)
                or any(not isinstance(a, str) or a not in ALLOWED_AXIOMS for a in r['axioms'])):
            raise ValueError('Invalid claim export')
        validate_claim(r.get('claim'))
        r['statement'] = r['claim']['statement']
        if r['declaration'] in seen:
            raise ValueError('Duplicate theorem export')
        seen.add(r['declaration'])
        records.append(r)
    if not records:
        raise ValueError('No claims exported; add #export_claim Your.claim or #export_theorem Your.theorem')
    return records


def parse_profiles(stdout: str) -> list[dict] | None:
    lines = [s[len('ONTOLOGY_PROFILES '):] for s in stdout.splitlines() if s.startswith('ONTOLOGY_PROFILES ')]
    if not lines:
        return None
    if len(lines) != 1:
        raise ValueError('Expected one profile export')
    rows = json.loads(lines[0])
    if not isinstance(rows, list) or len(rows) != 16:
        raise ValueError('Expected sixteen profiles')
    seen = set()
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get('profile'), dict):
            raise ValueError('Invalid profile')
        values = tuple(row['profile'].get(k) for k in AXES)
        if any(v not in ('require', 'reject') for v in values) or values in seen:
            raise ValueError('Invalid or duplicate profile')
        seen.add(values)
        if type(row.get('bell_bound')) is not bool or type(row.get('lf_bound')) is not bool:
            raise ValueError('Invalid coverage')
    return rows


def profile_table(profiles: list[dict] | None) -> str:
    if profiles is None:
        return ''
    rows = []
    for row in profiles:
        cells = ''.join('<td>'+('Require' if row['profile'][k] == 'require' else 'Reject')+'</td>' for k in AXES)
        cells += ''.join('<td class="bound">'+value+'<br><small>Conditional bound · existence not certified for this row</small></td>' if row[key] else
                         '<td class="open">No bound derived by these rules</td>'
                         for key, value in [('bell_bound', 'S ≤ 2'), ('lf_bound', 'G ≤ 6')])
        rows.append('<tr>'+cells+'</tr>')
    return '''<h2>Operational assumption profiles</h2><p>These columns use <strong>different named vocabularies</strong>.
OI means outcome independence; PI means conditional parameter independence; MI means independent preparation.
G means joint counterfactual assignments for Bell, and readable fixed friend records for LF.
This does not impose a philosophical definition of realism. The coverage is exported from Lean and applies
<code>OperationalProfiles.bell_bound</code> and <code>lf_bound</code> below.
A bound does not establish realizability. These rows carry no per-profile existence certificate,
even where a witness may be known separately. Amber cells are conditional bounds, not inhabited universes.
An unclassified cell does not establish compatibility.</p>
<div class="scroll"><table><thead><tr><th>OI</th><th>G (vocabulary-specific)</th><th>PI</th><th>MI</th><th>Bell vocabulary</th><th>Friend-record vocabulary</th></tr></thead><tbody>''' + ''.join(rows) + '</tbody></table></div>'


def render(records: list[dict], source: str, profiles: list[dict] | None = None) -> str:
    esc = html.escape
    rows = ''.join('<tr><td><code>'+esc(r['declaration'])+'</code><br>'+esc(evidence_label(r['claim']))+'</td><td><pre>'+esc(r['statement'])+
                   '</pre></td><td>'+esc(', '.join(r['axioms']) or 'None')+'</td></tr>' for r in records)
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Operational results — Ontology Separation</title><style>
body{{font:16px system-ui;margin:2rem;color:#182635;background:#f6f8fb}}p{{max-width:90ch;line-height:1.5}}
table{{border-collapse:collapse;width:100%;background:white}}td,th{{border:1px solid #cbd3dd;padding:.8rem;text-align:left;vertical-align:top}}
pre{{white-space:pre-wrap;overflow-wrap:anywhere;font-size:14px}}code{{overflow-wrap:anywhere}}
.bound{{background:#fff3d6}}.open{{background:#eef0f3;color:#52606c}}.scroll{{overflow-x:auto}}
@media(max-width:700px){{body{{margin:.7rem}}td,th{{padding:.4rem}}}}
</style></head><body><h1>Operational results</h1><p>Formal statements exported by Lean from <code>{esc(source)}</code>.
Each row states exactly what its proof establishes. The definitions determine its physical meaning.
This file is a snapshot: editing HTML or JSON cannot supply a proof. Recheck the trusted Lean source.
These are mathematical results, not statistical claims about experimental data.</p>
{profile_table(profiles)}<h2>Formal theorem statements</h2><div class="scroll"><table><thead><tr><th>Declaration</th><th>Formal proposition</th><th>Logical axioms</th></tr></thead><tbody>{rows}</tbody></table></div></body></html>'''


def write_report(source: Path, output: Path) -> int:
    validate_output(source, output)
    stdout = run_lean(source)
    records = parse_exports(stdout)
    atomic_write_html(output, render(records, str(source), parse_profiles(stdout)))
    return len(records)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        count = write_report(args.source, args.output)
    except (ValueError, OSError) as exc:
        parser.exit(2, str(exc) + '\n')
    print(f'Exported {count} checked claims to {args.output}')

if __name__ == '__main__':
    main()
