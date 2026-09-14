#!/usr/bin/env sh
set -eu
lake build
lake build Tests
python3 scripts/audit.py
python3 scripts/export.py
python3 -m unittest discover -s tests -v
