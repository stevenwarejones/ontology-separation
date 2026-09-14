"""Generate offline experiment/profile views without inventing ontology assignments.

The four-axis vocabulary is user supplied in Lean. The UI's optional operational
bridge is a conditional reading guide, NOT a registered proof for those labels.
"""
from __future__ import annotations
import html
import itertools
import json
from pathlib import Path

AXES = ("realism", "globalTruth", "locality", "measurementIndependent")
LABELS = ("Realism", "Global truth", "Locality", "Measurement independence")

EVIDENCE = [
    dict(id="hensen2015", scenario="B01", kind="Published measurement",
         title="Hensen et al. (2015): event-ready Bell test",
         result="245 trials; reported S = 2.42 ± 0.20; reported local-realist null-test p = 0.039.",
         interpretation="Statistical evidence against the tested local-realist null under its experimental assumptions. The p-value is not the probability that an ontology is true. The reported ± value is not used here as a certified lower confidence bound.",
         scope="Literature record only; raw trials and the statistical analysis have NOT been reverified in Lean. No automatic exclusion of individual philosophical assumptions.",
         url="https://arxiv.org/abs/1508.05949"),
    dict(id="bong2020", scenario="B02", kind="Published proof-of-principle experiment",
         title="Bong et al. (2020): Local Friendliness",
         result="Reports a proof-of-principle LF-inequality violation using a photon's path as the observer proxy.",
         interpretation="Relevant to the stated physical proxy. Does not establish experimental control of a cognitive observer or rule out observer-scale ontologies in general.",
         scope="Literature record only; no numerical LF dataset imported or statistical analysis reverified here. Our exact singlet score is a calculation, not this measurement.",
         url="https://arxiv.org/abs/1907.05607v4"),
]


def profiles():
    return [dict(zip(AXES, bits)) for bits in itertools.product((True, False), repeat=4)]


def profile_rule(scenario, profile):
    """Conditional antecedents; never infer a model's predicates from its label."""
    r, g, l, i = (profile[x] for x in AXES)
    if scenario in ("B01", "B03") and r and l and i:
        return "Bell bridge required: S ≤ 2. A verified violation excludes the conjunction under that bridge."
    if scenario == "B02" and g and l and i:
        return "LF bridge required: G ≤ 6. The calculated witness excludes the LF class, conditional on this profile mapping."
    if scenario == "P01" and g:
        return "If global truth supplies a joint distribution of these records: triangle score ≤ 2; score 3 is impossible."
    if scenario == "P10" and g:
        return "If global truth supplies these public joint records: disagreement(A,C) ≤ disagreement(A,B) + disagreement(B,C)."
    return "No prediction from these four stances alone; see the explicit experimental laws below."


STYLE = """
body{font:15px system-ui;color:#173047;background:#f8fafc;margin:0 auto;padding:24px;max-width:1500px}
a{color:#145f99}h1{margin-bottom:8px}p{max-width:1050px;line-height:1.5}.notice{background:#fff3d6;padding:16px;border-left:4px solid #bd8617}
table{border-collapse:collapse;width:100%;background:white;margin:16px 0}th,td{border:1px solid #cbd5e1;padding:10px;text-align:left;vertical-align:top}
th{background:#e7edf4}td{line-height:1.4}.scroll{overflow:auto}.conditional{background:#fff3d6}.formal{background:#e5f4ed}.empirical{background:#fde8e6}.unknown{background:#f0f2f5}
select,button{font:inherit;padding:7px;margin:4px}label{margin-right:14px}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(320px,1fr));gap:16px}
code{overflow-wrap:anywhere}small{display:block;margin-top:6px}details{margin:12px 0}summary{cursor:pointer;font-weight:600}.card{background:white;padding:16px;border:1px solid #cbd5e1}
"""


def shell(title, body, script=""):
    return ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{html.escape(title)}</title><style>{STYLE}</style></head><body>'
            f'{body}{script}</body></html>')


def experiment_html(report, scenario):
    esc = html.escape
    sid = scenario["id"]
    entries = [e for e in report.data["extensions"] if e["scenario"] == sid]
    cells = report.compare([sid])
    profile_data = [dict(values=p, rule=profile_rule(sid, p)) for p in profiles()]
    rows = []
    for k, entry in enumerate(profile_data):
        bits = ''.join(f'<td>{"Require" if entry["values"][a] else "Reject"}</td>' for a in AXES)
        rows.append(f'<tr><td>{k+1:02d}</td>{bits}<td>{esc(entry["rule"])}</td></tr>')
    table = '<table id="all-profiles"><thead><tr><th>Profile</th>' + ''.join(f'<th>{x}</th>' for x in LABELS) + '<th>Conditional consequence</th></tr></thead><tbody>' + ''.join(rows) + '</tbody></table>'
    cell_rows = ''.join('<tr><th>'+esc(c['model'])+'</th><td>'+esc(c['status'])+'</td><td>'+esc(c['result'])+'</td><td>'+esc('; '.join(c['assumptions']))+'<small>'+esc(c['limitation'])+'</small><small>Lean: '+esc(c['declaration'] or 'none')+'</small></td></tr>' for c in cells)
    ext_html = ''.join(f'<article class="card"><h3>{esc(e["title"])}</h3><p><b>Added law:</b> {esc(e["requiredLaw"])}</p><p>{esc(e["result"])}</p><p>{esc(e["contrast"])}</p><p>{esc(e["scope"])}</p><code>{esc(e["declaration"])}</code></article>' for e in entries)
    measured = [e for e in EVIDENCE if e['scenario'] == sid]
    evidence = ''.join(f'<article class="card"><h3><a href="{esc(e["url"], quote=True)}">{esc(e["title"])}</a></h3><p>{esc(e["result"])}</p><p>{esc(e["interpretation"])}</p><p>{esc(e["scope"])}</p></article>' for e in measured)
    if not measured:
        evidence = '<p>No laboratory measurement is imported for this scenario. Displayed exact values are mathematical calculations.</p>'
    body = f'''<nav><a href="index.html">All experiments</a> · <a href="matrix.html">Model matrix</a> · <a href="evidence.html">Evidence ledger</a></nav>
<h1>{esc(sid)} · {esc(scenario['title'])}</h1><p>{esc(scenario['protocol']['observable'])}</p>
<div class="notice"><b>Profiles are requirements, not sixteen established universes.</b> Require means the predicate; reject means its negation. Measurement independence is statistical, not philosophical free will. The four labels do not specify dynamics. A Lean <code>ProfileBridge</code> must connect your vocabulary to a theorem before it can exclude a profile.</div>
<h2>Compare ontology dimensions</h2><p>Choose two axes. The four panels show every combination of the other two, covering all 16 profiles.</p>
<label>Rows <select id="axis-x">{''.join(f'<option value="{i}">{x}</option>' for i,x in enumerate(LABELS))}</select></label>
<label>Columns <select id="axis-y">{''.join(f'<option value="{i}" {"selected" if i==2 else ""}>{x}</option>' for i,x in enumerate(LABELS))}</select></label>
<p><label><input id="bridge" type="checkbox"> Preview consequences assuming the stated operational bridge</label></p>
<p><label><input id="closure" type="checkbox"> Additionally assume realism implies global truth</label></p>
<p>Amber: conditional bound. Green: contradiction under the selected extra premise. Red: relevant published statistical evidence, conditional on the bridge. Gray: unclassified. No color means an ontology is proved true.</p>
<div id="slices" class="grid"></div><details><summary>All sixteen profiles (available without JavaScript)</summary><div class="scroll">{table}</div></details>
<h2>Model-by-experiment results</h2><p>“verifiedConditional” means a proved result under explicitly ADDED laws. It is not inferred from the model column alone.</p>
<div class="scroll"><table><thead><tr><th>Model</th><th>Evidence</th><th>Result</th><th>Assumptions and scope</th></tr></thead><tbody>{cell_rows}</tbody></table></div>
<h2>Concrete experimental extensions</h2>{ext_html or '<p>See the exact protocol and additional channel assumptions in the model table above.</p>'}
<h2>Published experimental evidence</h2>{evidence}<p><b>Remaining ambition:</b> {esc(scenario['obligations'])}</p>'''
    payload = json.dumps(dict(profiles=profile_data, axes=AXES, labels=LABELS, scenario=sid), separators=(',', ':')).replace('<','\\u003c').replace('>','\\u003e').replace('&','\\u0026')
    script = '<script id="profile-data" type="application/json">'+payload+'</script>\n<script>\n'+PROFILE_JS+'\n</script>'
    return shell(f'{sid} ontology profiles', body, script)


PROFILE_JS = r"""
const data = JSON.parse(document.getElementById('profile-data').textContent);
const xSelect=document.getElementById('axis-x'), ySelect=document.getElementById('axis-y');
function cellState(p, bridge, closure) {
  if (closure && p.values.realism && !p.values.globalTruth)
    return ['formal','Inconsistent IF realism entails global truth. This extra implication is not universal.'];
  if (!bridge) return ['unknown','No proved vocabulary bridge selected; no ontology exclusion asserted.'];
  if (data.scenario==='B01' && p.values.realism && p.values.locality && p.values.measurementIndependent)
    return ['empirical','Bell conjunction statistically challenged (Hensen 2015, p=0.039), IF this operational bridge applies. Not a proof that an individual axis is false.'];
  return [p.rule.startsWith('No prediction')?'unknown':'conditional',p.rule];
}
function renderSlices(changed) {
  let x=Number(xSelect.value),y=Number(ySelect.value);
  if(x===y){if(changed===xSelect){y=(x+1)%4;ySelect.value=String(y);}else{x=(y+1)%4;xSelect.value=String(x);}}
  const rest=[0,1,2,3].filter(a=>a!==x&&a!==y), root=document.getElementById('slices');root.replaceChildren();
  for(const a of [true,false])for(const b of [true,false]){
    const section=document.createElement('section'),heading=document.createElement('h3');
    heading.textContent=data.labels[rest[0]]+' = '+a+'; '+data.labels[rest[1]]+' = '+b;section.append(heading);
    const table=document.createElement('table'),header=table.insertRow();
    for(const t of [data.labels[x]+' / '+data.labels[y],'Require','Reject']){const th=document.createElement('th');th.textContent=t;header.append(th);}
    for(const xv of [true,false]){const row=table.insertRow();const th=document.createElement('th');th.textContent=xv?'Require':'Reject';row.append(th);
      for(const yv of [true,false]){const p=data.profiles.find(p=>p.values[data.axes[x]]===xv&&p.values[data.axes[y]]===yv&&p.values[data.axes[rest[0]]]===a&&p.values[data.axes[rest[1]]]===b);
        const [style,label]=cellState(p,document.getElementById('bridge').checked,document.getElementById('closure').checked);
        const cell=row.insertCell();cell.className=style;cell.textContent=label;
      }
    }section.append(table);root.append(section);
  }
}
for(const el of [xSelect,ySelect,document.getElementById('bridge'),document.getElementById('closure')])el.addEventListener('change',()=>renderSlices(el));
renderSlices();
"""


def write_examples(report, directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    links = []
    for s in report.data['scenarios']:
        filename = s['id']+'.html'
        (directory/filename).write_text(experiment_html(report,s), encoding='utf-8')
        links.append(f'<li><a href="{filename}">{html.escape(s["id"]+" · "+s["title"])}</a></li>')
    (directory/'matrix.html').write_text(report.html(index_href='index.html'), encoding='utf-8')
    ledger = ''.join(f'<article class="card"><h2><a href="{e["url"]}">{html.escape(e["title"])}</a></h2><p>{html.escape(e["kind"]+": "+e["result"])}</p><p>{html.escape(e["interpretation"])}</p><p>{html.escape(e["scope"])}</p></article>' for e in EVIDENCE)
    (directory/'evidence.html').write_text(shell('Experimental evidence', '<a href="index.html">All views</a><h1>Evidence ledger</h1><p>Published measurements are separate from Lean-calculated witnesses. Compatibility never proves an ontology true. No raw-data reanalysis is claimed.</p>'+ledger), encoding='utf-8')
    (directory/'index.html').write_text(shell('Ontology Separation examples', '<h1>Ontology Separation · examples</h1><p>Open these files locally; no server, network, or package installation is needed.</p><p><a href="matrix.html">14 × 7 model matrix</a> · <a href="evidence.html">Experimental evidence ledger</a></p><div class="notice">Native model results and conditional extensions are separate. A populated cell is not necessarily a prediction from its column alone. All sixteen ontology profiles are visible for each experiment; physical realizability is not presumed.</div><h2>Experiment and ontology views</h2><ul>'+''.join(links)+'</ul>'), encoding='utf-8')
