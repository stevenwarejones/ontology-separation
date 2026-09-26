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
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/RecordAccessStudy.lean -o examples/record-access.html
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/ModelClassStudy.lean -o examples/model-classes.html
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/PartialLeakageStudy.lean -o examples/partial-leakage.html
python3 scripts/test.py
node scripts/check_examples.cjs
sh scripts/check_downstream.sh
python3 scripts/check_scenario_export.py
PYTHONPATH=python python3 -m ontology_separation.scenario_report examples/downstream/RecipeStudy.lean -o examples/recipe-comparison.html
PYTHONPATH=python python3 -m ontology_separation.scenario_report examples/downstream/TwoQubitStudy.lean -o examples/two-qubit-comparison.html
PYTHONPATH=python python3 -m ontology_separation.scenario_report examples/downstream/FriendStudy.lean -o examples/local-friendliness-protocol.html
python3 scripts/check_recipes.py

PYTHONPATH=python python3 -m ontology_separation.proof_report examples/EnvironmentAccessStudy.lean -o examples/environment-access.html

PYTHONPATH=python python3 -m ontology_separation.proof_report examples/EnvironmentDiscriminationStudy.lean -o examples/environment-discrimination.html

PYTHONPATH=python python3 -m ontology_separation.proof_report examples/FiniteShotStudy.lean -o examples/finite-shot.html

PYTHONPATH=python python3 -m ontology_separation.proof_report examples/PartialEnvironmentStudy.lean -o examples/partial-environment.html
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/LFAssumptionStudy.lean -o examples/lf-assumptions.html

python3 scripts/check_external_certificate.py
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/ExternalCertificateStudy.lean -o examples/external-certificate.html

PYTHONPATH=python python3 -m ontology_separation.proof_report examples/SignalingStudy.lean -o examples/signaling-tradeoff.html
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/LFPaperStudy.lean -o examples/lf-paper.html

PYTHONPATH=python python3 -m ontology_separation.proof_report examples/LFReadoutStudy.lean -o examples/lf-readout.html
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/PathInterferenceStudy.lean -o examples/path-interference.html
PYTHONPATH=python python3 -m ontology_separation.proof_report examples/PhaseInterventionStudy.lean -o examples/phase-intervention.html
