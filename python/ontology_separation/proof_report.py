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
COMPARISON_PREFIX = "ONTOLOGY_COMPARISON "
SEARCH_PREFIX = "ONTOLOGY_SEARCH "
from .evidence import validate_claim, evidence_label, result_text
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXES = ("realism", "globalTruth", "locality", "measurementIndependent")


def parse_exports(stdout: str, *, allow_empty: bool = False) -> list[dict]:
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
    if not records and not allow_empty:
        raise ValueError('No claims exported; add #export_claim Your.claim or #export_theorem Your.theorem')
    return records



def _rational_text(value: dict | None) -> str:
    if value is None:
        return ''
    from fractions import Fraction
    return str(Fraction(int(value['numerator']), int(value['denominator'])))


def parse_comparisons(stdout: str) -> list[dict]:
    rows, seen = [], set()
    for line in stdout.splitlines():
        if not line.startswith(COMPARISON_PREFIX):
            continue
        item = json.loads(line[len(COMPARISON_PREFIX):])
        report = item.get('report') if isinstance(item, dict) else None
        if (not isinstance(item, dict) or not isinstance(item.get('declaration'), str) or not isinstance(item.get('axioms'), list)
                or any(not isinstance(a, str) or a not in ALLOWED_AXIOMS for a in item['axioms'])
                or not isinstance(report, dict)):
            raise ValueError('Invalid structured comparison export')
        if item['declaration'] in seen:
            raise ValueError('Duplicate comparison export')
        seen.add(item['declaration'])
        if report.get('verdict') not in {'agreement', 'separation'}:
            raise ValueError('Invalid comparison verdict')
        if any(not isinstance(report.get(k), str) or not report[k].strip()
               for k in ('left_model', 'right_model')):
            raise ValueError('Comparison models must be derived labels')
        if (not isinstance(report.get('covered_protocols'), list)
                or not report['covered_protocols']
                or any(not isinstance(p, str) or not p for p in report['covered_protocols'])):
            raise ValueError('Comparison needs a nonempty covered protocol family')
        validate_claim(report.get('claim'))
        numeric = ('left_probability', 'right_probability', 'gap')
        if report['verdict'] == 'agreement':
            if any(report.get(k) is not None for k in numeric + ('protocol', 'setting', 'outcome')):
                raise ValueError('Agreement cannot acquire separator fields')
            if report['claim']['kind'] != 'agreement':
                raise ValueError('Agreement presentation must carry an agreement claim')
        else:
            if report['claim']['kind'] != 'separation':
                raise ValueError('Separation presentation must carry a separation claim')
            if any(not isinstance(report.get(k), str) or not report[k]
                   for k in ('protocol', 'setting', 'outcome')):
                raise ValueError('Separation needs checked witness labels')
            for key in numeric:
                q = report.get(key)
                if (not isinstance(q, dict) or not isinstance(q.get('numerator'), str)
                        or not isinstance(q.get('denominator'), str)
                        or int(q['denominator']) <= 0):
                    raise ValueError('Separation needs exact rational probabilities and gap')
            from fractions import Fraction
            pa, pb, gap = (Fraction(int(report[k]['numerator']), int(report[k]['denominator']))
                           for k in numeric)
            if not (0 <= pa <= 1 and 0 <= pb <= 1 and gap > 0 and pa - pb == gap):
                raise ValueError('Invalid oriented probability gap')
            if report['protocol'] not in report['covered_protocols']:
                raise ValueError('Separator is outside the displayed family')
        rows.append(item)
    return rows



def parse_searches(stdout: str) -> list[dict]:
    rows, seen = [], set()
    for line in stdout.splitlines():
        if not line.startswith(SEARCH_PREFIX):
            continue
        item = json.loads(line[len(SEARCH_PREFIX):])
        report = item.get('report') if isinstance(item, dict) else None
        if (not isinstance(item, dict) or not isinstance(item.get('declaration'), str)
                or not isinstance(item.get('axioms'), list)
                or any(not isinstance(a, str) or a not in ALLOWED_AXIOMS for a in item['axioms'])
                or not isinstance(report, dict) or report.get('status') not in
                {'base-separates', 'no-candidate', 'found'}):
            raise ValueError('Invalid structured search export')
        if item['declaration'] in seen:
            raise ValueError('Duplicate search export')
        seen.add(item['declaration'])
        base = report.get('base')
        candidate = report.get('candidate')
        base_item = parse_comparisons(COMPARISON_PREFIX + json.dumps(
            {'declaration': item['declaration']+'.base', 'axioms': item['axioms'], 'report': base}))[0]
        candidate_item = None if candidate is None else parse_comparisons(
            COMPARISON_PREFIX + json.dumps({'declaration': item['declaration']+'.candidate',
            'axioms': item['axioms'], 'report': candidate}))[0]
        status = report['status']
        if status == 'base-separates' and (base['verdict'] != 'separation' or candidate is not None):
            raise ValueError('Base-separates search has inconsistent evidence')
        if status == 'no-candidate' and (base['verdict'] != 'agreement' or candidate is None
                                         or candidate['verdict'] != 'agreement'):
            raise ValueError('No-candidate search has inconsistent evidence')
        if status == 'found' and (base['verdict'] != 'agreement' or candidate is None
                                  or candidate['verdict'] != 'separation'):
            raise ValueError('Found search has inconsistent evidence')
        rows.append({'declaration': item['declaration'], 'axioms': item['axioms'],
                     'report': report, 'base_item': base_item, 'candidate_item': candidate_item})
    return rows

def search_cards(searches: list[dict]) -> str:
    if not searches:
        return ''
    cards = []
    for item in searches:
        evidence = [item['base_item']]
        if item['candidate_item'] is not None:
            evidence.append(item['candidate_item'])
        cards.append('<section class="search"><h3>Finite separator search: '+
                     html.escape(item['report']['status'])+'</h3>'+
                     comparison_cards(evidence)+'</section>')
    return '<h2>Checked separator searches</h2>'+''.join(cards)

def comparison_cards(comparisons: list[dict]) -> str:
    if not comparisons:
        return ''
    esc = html.escape
    cards = []
    for item in comparisons:
        r = item['report']
        scope = ', '.join(esc(p) for p in r['covered_protocols'])
        if r['verdict'] == 'agreement':
            detail = ('<p><strong>Checked conclusion:</strong> agreement across these supplied experiments.</p>'
                      '<p><strong>Covered family:</strong> '+scope+'</p>')
        else:
            detail = ('<p><strong>Checked conclusion:</strong> separating experiment found.</p>'
                      '<p><strong>Covered family:</strong> '+scope+'</p>'
                      '<p><strong>Separator:</strong> '+esc(r['protocol'])+
                      ' · '+esc(r['setting'])+' · outcome '+esc(r['outcome'])+'</p>'
                      '<p><strong>'+esc(r['left_model'])+':</strong> '+esc(_rational_text(r['left_probability']))+
                      ' &nbsp; <strong>'+esc(r['right_model'])+':</strong> '+esc(_rational_text(r['right_probability']))+
                      ' &nbsp; <strong>exact gap:</strong> '+esc(_rational_text(r['gap']))+'</p>')
        cards.append('<section class="comparison"><h3>'+esc(r['left_model'])+
                     ' vs '+esc(r['right_model'])+'</h3>'+detail+
                     '<details><summary>Formal claim for this comparison</summary><pre>'+
                     esc(r['claim']['statement'])+'</pre></details></section>')
    return '<h2>Checked model comparisons</h2>'+''.join(cards)

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


def render(records: list[dict], source: str, profiles: list[dict] | None = None, comparisons: list[dict] | None = None, searches: list[dict] | None = None) -> str:
    esc = html.escape
    rows = ''.join('<tr><td><code>'+esc(r['declaration'])+'</code><br>'+esc(evidence_label(r['claim']))+'</td><td>'+esc(result_text(r['claim']) if r['claim'].get('quantity') is not None else evidence_label(r['claim']))+'</td><td><pre>'+esc(r['statement'])+
                   '</pre></td><td>'+esc(', '.join(r['axioms']) or 'None')+'</td></tr>' for r in records)
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Operational results — Ontology Separation</title><style>
body{{font:16px system-ui;margin:2rem;color:#182635;background:#f6f8fb}}p{{max-width:90ch;line-height:1.5}}
table{{border-collapse:collapse;width:100%;background:white}}td,th{{border:1px solid #cbd3dd;padding:.8rem;text-align:left;vertical-align:top}}
pre{{white-space:pre-wrap;overflow-wrap:anywhere;font-size:14px}}code{{overflow-wrap:anywhere}}
.bound{{background:#fff3d6}}.open{{background:#eef0f3;color:#52606c}}.scroll{{overflow-x:auto}}
.comparison{{background:white;border:1px solid #cbd3dd;border-radius:8px;padding:1rem;margin:1rem 0}}
.comparison p{{margin:.45rem 0}}.search{{background:#eef5fb;border:1px solid #9fb9cf;border-radius:8px;padding:1rem;margin:1rem 0}}
@media(max-width:700px){{body{{margin:.7rem}}td,th{{padding:.4rem}}}}
</style></head><body><h1>Operational results</h1><p>Formal statements exported by Lean from <code>{esc(source)}</code>.
Each row states exactly what its proof establishes. The definitions determine its physical meaning.
This file is a snapshot: editing HTML or JSON cannot supply a proof. Recheck the trusted Lean source.
These are mathematical results, not statistical claims about experimental data.</p>
{profile_table(profiles)}{search_cards(searches or [])}{comparison_cards(comparisons or [])}<h2>Formal theorem statements</h2><div class="scroll"><table><thead><tr><th>Declaration</th><th>Checked result</th><th>Formal proposition</th><th>Logical axioms</th></tr></thead><tbody>{rows}</tbody></table></div></body></html>'''


def write_report(source: Path, output: Path) -> int:
    validate_output(source, output)
    stdout = run_lean(source)
    comparisons = parse_comparisons(stdout)
    searches = parse_searches(stdout)
    records = parse_exports(stdout, allow_empty=bool(comparisons or searches))
    atomic_write_html(output, render(records, str(source), parse_profiles(stdout), comparisons, searches))
    return len(records) or len(comparisons) or len(searches)


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
