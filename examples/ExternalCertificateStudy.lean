import OntologySeparation.Certificates.ForcedSignaling
import OntologySeparation.Reporting.Claim

/-!
This is a certificate-review example, not a new apparatus or ontology recipe.
The exported theorem quantifies over every point satisfying the explicit LP.
For the separate proved physical response-model → LP bridge and sharp witness,
see SignalingStudy.lean and docs/SIGNALING_GUIDE.md.
-/
#export_theorem OntologySeparation.ForcedSignaling.bound
#export_theorem OntologySeparation.ForcedSignaling.zeroBudget_score
