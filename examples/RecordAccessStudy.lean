import OntologySeparation.Experiments.RecordAccess
import OntologySeparation.Reporting.Claim

/-! Recheck: python -m ontology_separation.proof_report examples/RecordAccessStudy.lean
-o examples/record-access.html

The experiment and access are independent of the selected physical model.
Read docs/RECORD_ACCESS_GUIDE.md before interpreting these claims. -/
#export_theorem OntologySeparation.RecordAccess.same_local_state
#export_theorem OntologySeparation.RecordAccess.all_local_tests
#export_theorem OntologySeparation.RecordAccess.locally_equivalent
#export_claim OntologySeparation.RecordAccess.localComparisonClaim
#export_claim OntologySeparation.RecordAccess.coherentClaim
#export_claim OntologySeparation.RecordAccess.dephasedClaim
#export_theorem OntologySeparation.RecordAccess.joint_not_equivalent
#export_claim OntologySeparation.RecordAccess.jointComparisonClaim
