import OntologySeparation.Signaling

open OntologySeparation

-- Change this one allowed TV budget, then regenerate the proof report.
-- Scope: finite conditional-local response models; the fixed six-term S₄ score.
def signalingStudy := SignalingStudy.design (1/8)

noncomputable def classBound := signalingStudy.boundClaim
noncomputable def attainingResponseModel := signalingStudy.attainmentClaim
noncomputable def actualWitnessSignaling := signalingStudy.signalingClaim

#export_claim classBound
#export_claim attainingResponseModel
#export_claim actualWitnessSignaling
