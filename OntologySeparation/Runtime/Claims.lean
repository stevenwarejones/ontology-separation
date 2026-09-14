import Lean

/-! Enumerated theorem references for the executable. Catalog/Evidence resolves
EVERY constructor to a Lean proof and verifies declaration-name consistency. -/
namespace OntologySeparation.Catalog

inductive ClaimId where
  | bellLocal | bellQuantum | bellPR | lfBound | lfQuantum | lfControl | echo | leak | phase
  | nsFraction | noisyBell | noisyLF | nsLF | triangle | recovery | jointRecovery | relabel | query | order | mediator | agreement | contamination | localThree | innerPR | singletNS | freeExtension | exclusion
  deriving Repr, BEq, DecidableEq

def ClaimId.declaration : ClaimId → String
  | .bellLocal => "QIT.Bell.CHSH.value_le_two_of_isLocal"
  | .bellQuantum => "OntologySeparation.Catalog.bellQuantumEvidence"
  | .bellPR => "OntologySeparation.Catalog.bellPREvidence"
  | .lfBound => "OntologySeparation.Catalog.lfBoundEvidence"
  | .lfQuantum => "OntologySeparation.Catalog.lfQuantumEvidence"
  | .lfControl => "OntologySeparation.LF.exists_bell_violation_within_LF"
  | .echo => "OntologySeparation.Memory.echo_probability"
  | .leak => "OntologySeparation.Memory.leakedEcho_probability"
  | .phase => "OntologySeparation.Memory.phaseEcho_probability"
  | .triangle => "OntologySeparation.Research.no_pairwise_gluing"
  | .recovery => "OntologySeparation.Research.restricted_recovery"
  | .jointRecovery => "OntologySeparation.Research.joint_recovery"
  | .relabel => "OntologySeparation.Research.passive_relabel"
  | .query => "OntologySeparation.Research.random_query_bound"
  | .order => "OntologySeparation.Research.noisy_order_probability"
  | .mediator => "OntologySeparation.Research.phase_state_not_complex_product"
  | .agreement => "OntologySeparation.Research.public_error_bound"
  | .contamination => "OntologySeparation.Shared.LF_contamination_required"
  | .localThree => "OntologySeparation.Shared.local_three_LF_bound"
  | .innerPR => "OntologySeparation.Shared.lf_inner_PR"
  | .singletNS => "OntologySeparation.Shared.singlet_noSignaling"
  | .freeExtension => "OntologySeparation.independent_sector_underdetermined"
  | .exclusion => "OntologySeparation.ProfileBridge.excludes"
  | .nsLF => "OntologySeparation.Shared.LF_ns_sharp"
  | .noisyBell => "OntologySeparation.DephasedSinglet.bell_score"
  | .noisyLF => "OntologySeparation.DephasedSinglet.LF_score"
  | .nsFraction => "OntologySeparation.Shared.LF_NS_fraction_required"

end OntologySeparation.Catalog
