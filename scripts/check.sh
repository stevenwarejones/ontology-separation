#!/usr/bin/env sh
set -eu
lake build
lake build Tests
lake env lean examples/CustomUniverse.lean
lake env lean examples/PhysicistWorkflow.lean
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/Publish.lean -o examples/operational-results.html
python3 scripts/audit.py
python3 scripts/check_export.py
python3 scripts/export.py
python3 scripts/test.py
node scripts/check_examples.cjs
sh scripts/check_downstream.sh
python3 scripts/check_scenario_export.py
PYTHONPATH=python python3 -m ontology_separation.scenario_report examples/downstream/RecipeStudy.lean -o examples/recipe-comparison.html
python3 scripts/check_recipes.py
