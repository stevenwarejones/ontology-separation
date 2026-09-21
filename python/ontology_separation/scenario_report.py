"""Check a trusted Lean comparison and render exact, proof-indexed predictions."""
from __future__ import annotations
import argparse
from fractions import Fraction
import html
import json
from pathlib import Path
import re
from .checked_source import run_lean, validate_output, atomic_write_html
from .proof_report import parse_exports

PREFIX = 'ONTOLOGY_SCENARIO '


def parse_comparison(stdout: str) -> dict:
    lines = [line[len(PREFIX):] for line in stdout.splitlines() if line.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError('Expected exactly one #export_scenario comparison')
    record = json.loads(lines[0])
    if not isinstance(record, dict) or any(not isinstance(record.get(k), str) or not record[k]
                                         for k in ('declaration', 'type')):
        raise ValueError('Missing comparison provenance')
    c = record.get('comparison')
    if not isinstance(c, dict) or c.get('schema') != 'ontology-scenario-v1':
        raise ValueError('Unsupported scenario schema')
    if any(not isinstance(c.get(k), str) for k in ('title', 'description')):
        raise ValueError('Invalid scenario description')
    for axis in ('models', 'protocols'):
        labels = c.get(axis)
        if (not isinstance(labels, list) or not labels
                or any(not isinstance(x, str) or not x.strip() for x in labels)
                or len({' '.join(x.split()) for x in labels}) != len(labels)):
            raise ValueError('Model and protocol labels must be nonempty and unique')
    values = c.get('values')
    if not isinstance(values, list) or len(values) != len(c['models']):
        raise ValueError('Wrong number of model rows')
    for row in values:
        if not isinstance(row, list) or len(row) != len(c['protocols']):
            raise ValueError('Missing or extra protocol cells')
        for cell in row:
            if not isinstance(cell, dict):
                raise ValueError('Invalid rational cell')
            n, d = cell.get('numerator'), cell.get('denominator')
            if (not isinstance(n, str) or not re.fullmatch(r'-?[0-9]+', n)
                    or not isinstance(d, str) or not re.fullmatch(r'[0-9]+', d)
                    or int(d) <= 0):
                raise ValueError('Cells require integer strings and a positive denominator')
    return record


def render(record: dict, source: str, theorems: list[dict]) -> str:
    esc = html.escape
    c = record['comparison']
    head = ''.join('<th scope="col">'+esc(p)+'</th>' for p in c['protocols'])
    rows = []
    for label, values in zip(c['models'], c['values']):
        cells = ''.join('<td>'+str(Fraction(int(v['numerator']), int(v['denominator'])))+'</td>' for v in values)
        rows.append('<tr><th scope="row">'+esc(label)+'</th>'+cells+'</tr>')
    proofs = ''.join('<details><summary>'+esc(t['declaration'])+'</summary><pre>'+esc(t['statement'])+
                     '</pre></details>' for t in theorems)
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>{esc(c['title'])}</title>
<style>body{{font:17px system-ui;color:#182635;background:#f6f8fb;max-width:1100px;margin:3rem auto;padding:0 1rem}}
p{{line-height:1.6;max-width:90ch}}table{{border-collapse:collapse;width:100%;background:white}}
th,td{{border:1px solid #cbd3dd;padding:1rem;text-align:left}}td{{font-size:1.3rem;font-variant-numeric:tabular-nums}}
.scroll{{overflow-x:auto}}details{{padding:1rem;background:white;margin:.8rem 0}}summary{{cursor:pointer;overflow-wrap:anywhere}}
pre{{white-space:pre-wrap;overflow-wrap:anywhere;font-size:.85rem}}code{{overflow-wrap:anywhere}}</style></head>
<body><h1>{esc(c['title'])}</h1><p>{esc(c['description'])}</p>
<div class="scroll"><table><thead><tr><th scope="col">Physical model</th>{head}</tr></thead>
<tbody>{''.join(rows)}</tbody></table></div>
<p>Entries are exact calculated values of the scenario's observable. Every cell is bound to its model,
procedure, and observable by a Lean equality proof. Identical entries establish equality of this statistic;
they do not establish equivalence of entire models. Distinct entries describe different distributions or
statistics, not a guarantee that a finite experimental sample will identify the model.</p>
<h2>Proof provenance</h2><p>Checked source: <code>{esc(source)}</code>.<br>
Comparison declaration: <code>{esc(record['declaration'])}</code>.</p><pre>{esc(record['type'])}</pre>
<p>Model names and descriptions are commentary. Definitions give them physical meaning.
This editable HTML is a snapshot, not a proof certificate. Regenerate it from trusted Lean source.</p>
{proofs}</body></html>'''


def write_report(source: Path, output: Path) -> int:
    validate_output(source, output)
    stdout = run_lean(source)
    record = parse_comparison(stdout)
    # Additional theorem explanations are optional; the Comparison already carries its cell proofs.
    proofs = parse_exports(stdout) if any(x.startswith('ONTOLOGY_THEOREM ') for x in stdout.splitlines()) else []
    document = render(record, str(source), proofs)
    atomic_write_html(output, document)
    c = record['comparison']
    return len(c['models'])*len(c['protocols'])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('-o', '--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        count = write_report(args.source, args.output)
    except (ValueError, OSError) as exc:
        parser.exit(2, str(exc)+'\n')
    print(f'Exported {count} proved cells to {args.output}')

if __name__ == '__main__':
    main()
