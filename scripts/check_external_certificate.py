#!/usr/bin/env python3
"""Compare every Lean LP coefficient against the pinned upstream reconstruction.

The fingerprints were obtained by running the source verifier's reconstruction,
not from the Lean definitions. This detects transcription drift; the mathematical
proof is separately kernel-checked in ForcedSignaling.lean. No network/dependency
on the external repository is required by CI.
"""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def main():
    manifest = json.loads((ROOT / 'docs/research/certificates/forced-signaling-k8.json').read_text())
    run = subprocess.run(['lake', 'env', 'lean', 'Tests/ForcedSignalingSnapshot.lean'],
                         cwd=ROOT, capture_output=True, text=True, check=True)
    lines = run.stdout.splitlines()
    if len(lines) != 273:
        raise ValueError('Expected header and exactly 272 constraint rows')
    actual = json.loads(lines[0])
    actual['constraints'] = [json.loads(line) for line in lines[1:]]
    if actual.keys() != manifest['sha256'].keys():
        raise ValueError('Missing or extra certificate components')
    for key, value in actual.items():
        encoded = json.dumps(value, separators=(',', ':')).encode('utf-8')
        if hashlib.sha256(encoded).hexdigest() != manifest['sha256'][key]:
            raise ValueError(f'Pinned source/Lean coefficient mismatch: {key}')
    print('All LP coefficients and dual entries match the pinned upstream reconstruction')

if __name__ == '__main__':
    main()
