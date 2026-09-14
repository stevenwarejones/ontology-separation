#!/usr/bin/env sh
set -eu
lake build
lake build Tests
lake env lean examples/CustomUniverse.lean
python3 scripts/audit.py
python3 scripts/export.py
python3 scripts/test.py
node scripts/check_examples.cjs
