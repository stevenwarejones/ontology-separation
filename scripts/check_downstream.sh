#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/../examples/downstream"
# The parent check already built the shared, pinned dependencies.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
lake env lean Publish.lean
lake env lean Checks.lean
PYTHONPATH=../../python python3 -m ontology_separation.proof_report Publish.lean -o ../bell-law-study.html
