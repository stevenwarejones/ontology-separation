#!/usr/bin/env sh
set -eu
# Default to the same bounded-memory execution used by CI. Callers may override
# this deliberately; every child Lake/Lean process inherits the chosen limit.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

check() {
  check_started=$(date +%s)
  printf '\n[check] %s\n' "$*"
  if "$@"; then
    check_status=0
  else
    check_status=$?
  fi
  check_elapsed=$(( $(date +%s) - check_started ))
  printf '[check] %ss, exit %s: %s\n' "$check_elapsed" "$check_status" "$*"
  if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
    printf '| `%s` | %ss | %s |\n' "$*" "$check_elapsed" "$check_status" >> "$GITHUB_STEP_SUMMARY"
  fi
  return "$check_status"
}

if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  printf '### Verification timings\n\n| Command | Elapsed | Exit |\n| --- | ---: | ---: |\n' >> "$GITHUB_STEP_SUMMARY"
fi
check lake build
check lake build Tests
check lake env lean examples/CustomUniverse.lean
check lake env lean examples/PhysicistWorkflow.lean
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/Publish.lean -o examples/operational-results.html
check python3 scripts/audit.py
check python3 scripts/check_export.py
check python3 scripts/export.py
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/RecordAccessStudy.lean -o examples/record-access.html
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/ModelClassStudy.lean -o examples/model-classes.html
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/PartialLeakageStudy.lean -o examples/partial-leakage.html
check python3 scripts/test.py
check node scripts/check_examples.cjs
check sh scripts/check_downstream.sh
check python3 scripts/check_scenario_export.py
PYTHONPATH=python check python3 -m ontology_separation.scenario_report examples/downstream/RecipeStudy.lean -o examples/recipe-comparison.html
PYTHONPATH=python check python3 -m ontology_separation.scenario_report examples/downstream/TwoQubitStudy.lean -o examples/two-qubit-comparison.html
PYTHONPATH=python check python3 -m ontology_separation.scenario_report examples/downstream/FriendStudy.lean -o examples/local-friendliness-protocol.html
check python3 scripts/check_recipes.py

PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/EnvironmentAccessStudy.lean -o examples/environment-access.html

PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/EnvironmentDiscriminationStudy.lean -o examples/environment-discrimination.html

PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/FiniteShotStudy.lean -o examples/finite-shot.html

PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/PartialEnvironmentStudy.lean -o examples/partial-environment.html
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/LFAssumptionStudy.lean -o examples/lf-assumptions.html

check python3 scripts/check_external_certificate.py
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/ExternalCertificateStudy.lean -o examples/external-certificate.html

PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/SignalingStudy.lean -o examples/signaling-tradeoff.html
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/LFPaperStudy.lean -o examples/lf-paper.html

PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/LFReadoutStudy.lean -o examples/lf-readout.html
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/PathInterferenceStudy.lean -o examples/path-interference.html
PYTHONPATH=python check python3 -m ontology_separation.proof_report examples/PhaseInterventionStudy.lean -o examples/phase-intervention.html
