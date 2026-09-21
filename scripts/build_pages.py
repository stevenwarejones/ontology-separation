#!/usr/bin/env python3
"""Stage committed HTML snapshots; rewrite source links to the exact deployed revision."""
from pathlib import Path
import argparse
import html
import re
import subprocess


def stage(root: Path, output: Path, revision: str) -> None:
    if not re.fullmatch(r'[0-9a-f]{40}', revision):
        raise ValueError('A full Git commit SHA is required for source provenance')
    if output.exists():
        raise ValueError('Choose a new staging directory')
    output.mkdir(parents=True)
    base = f'https://github.com/stevenwarejones/ontology-separation/blob/{revision}/'
    for source in (root/'examples').glob('*.html'):
        text = source.read_text()
        def link(match):
            target = match.group(1)
            if target.startswith('../docs/'):
                target = base + target[3:]
            elif target.endswith('.lean'):
                target = base + 'examples/' + target
            return 'href="'+html.escape(target, quote=True)+'"'
        text = re.sub(r'href="([^"]+)"', link, text)
        banner = (f'<p style="padding:.75rem;background:#e8eef7">Published snapshot · '
                  f'<a href="{base}README.md">source revision {revision[:7]}</a>. '
                  'Browsing does not recheck proofs.</p>')
        if re.search(r'<body[ >]', text):
            text = re.sub(r'(<body[^>]*>)', lambda m: m.group(1)+banner, text, count=1)
        else:
            text = text.replace('<h1', banner+'<h1', 1)
        (output/source.name).write_text(text)
    if not (output/'index.html').is_file():
        raise ValueError('No examples index found')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    stage(root, args.output, revision)
