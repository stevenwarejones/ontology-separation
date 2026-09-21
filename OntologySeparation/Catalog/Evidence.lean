import OntologySeparation.Experiments.FriendProtocol
import OntologySeparation.Models.DephasedSinglet
import OntologySeparation.Experiments.Research
import OntologySeparation.Adapters.Shared
import OntologySeparation.Core.Exclusion
import OntologySeparation.Experiments.Bell
import OntologySeparation.Experiments.LocalFriendliness
import OntologySeparation.Models.Memory
import OntologySeparation.Core.Claim

/-! Reportable claims carry Lean proofs. The UI text is explanatory; each named
`declaration` below is an actual theorem whose statement can be inspected in Lean. -/
namespace OntologySeparation.Catalog

theorem bellQuantumEvidence :
    Bell.score Bell.singletBehavior = 1502/625 ∧ ¬ Bell.localTheory Bell.singletBehavior :=
  ⟨Bell.singlet_score, Bell.quantumSeparation.excludes⟩

theorem bellPREvidence :
    QIT.Bell.CHSH.value QIT.Bell.CHSH.prBox = 4 ∧
      ¬ Bell.localTheory Bell.prWitness.behavior :=
  ⟨QIT.Bell.CHSH.value_prBox, Bell.local_vs_noSignaling.excludes⟩

theorem lfBoundEvidence (p : Behavior LF.interface) (h : LF.theory p) :
    RealQuantum.genuineLF p ≤ 6 := LF.genuineBound.valid p h

theorem lfQuantumEvidence :
    RealQuantum.genuineLF RealQuantum.lfBehavior = 1214656/180625 ∧
      ¬ LF.theory RealQuantum.lfBehavior :=
  ⟨RealQuantum.lfBehavior_value, LF.quantumSeparation.excludes⟩

noncomputable section

def bellLocalModel : Behavior Bell.interface :=
  Bell.fromQIT (QIT.Bell.deterministicBehavior ⟨fun _ => false, fun _ => false⟩)
theorem bellLocal_admissible : Bell.localTheory bellLocalModel :=
  ⟨_, QIT.Bell.deterministic_isLocal _, rfl⟩
def bellLocalClaim : Claim :=
  .realizedBound Bell.localTheory Bell.score 2 Bell.localBound.valid bellLocalModel bellLocal_admissible

def bellQuantumClaim : Claim := .witness (RealQuantum.singletTheory 2) Bell.score
  Bell.singletBehavior ⟨Bell.alice, Bell.bob, rfl⟩ (1502/625) (by simpa using Bell.singlet_score)
def bellPRClaim : Claim := .witness Bell.noSignalingTheory Bell.score Bell.prWitness.behavior
  Bell.prWitness.admissible 4 (by change Bell.score (Bell.fromQIT QIT.Bell.CHSH.prBox) = _; rw [Bell.score_fromQIT, QIT.Bell.CHSH.value_prBox]; norm_num)
def lfBoundClaim : Claim := .realizedBound LF.theory RealQuantum.genuineLF 6
  LF.genuineBound.valid Shared.saturatingModel.behavior Shared.saturating_is_LF
def lfQuantumClaim : Claim := .witness (RealQuantum.singletTheory 3) RealQuantum.genuineLF
  (LocalFriendlinessRecipe.interpret LocalFriendlinessRecipe.Law.coherent LocalFriendlinessRecipe.reference)
  (by rw [LocalFriendlinessRecipe.reference_behavior]; exact RealQuantum.lfBehavior_realized)
  (1214656/180625)
  (by rw [LocalFriendlinessRecipe.reference_behavior]; simpa using RealQuantum.lfBehavior_value)
def nsLFClaim : Claim := .realizedBound Shared.NoSignaling RealQuantum.genuineLF 10
  Shared.LF_noSignaling_bound Shared.nsExtreme Shared.nsExtreme_noSignaling

/-- The three-setting local class includes every finite mixture, not only the witness's size. -/
def localThreeTheory (p : Behavior LF.interface) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (m : Shared.LocalThree ι), m.toLF.behavior = p
def localThreeWorld : Shared.LocalThree Unit where
  weights := ⟨fun _ => 1, by intro _; norm_num, by simp⟩
  alice := fun _ _ => false
  bob := fun _ _ => true
def localThreeClaim : Claim := .realizedBound localThreeTheory RealQuantum.genuineLF 6
  (by intro p hp; obtain ⟨ι, hi, m, rfl⟩ := hp; letI := hi; exact Shared.local_three_LF_bound m)
  localThreeWorld.toLF.behavior ⟨Unit, inferInstance, localThreeWorld, rfl⟩

def innerPRClaim : Claim := .witness (fun q : LF.Component => Shared.NoSignaling q.behavior)
  (fun q => Bell.score (Shared.inner q.behavior)) LF.prComponent (Shared.lf_noSignaling _)
  4 (by simpa using Shared.lf_inner_PR)
def lfControlClaim : Claim := .witness (fun q : LF.Component => LF.componentScore q ≤ 6)
  LF.innerCHSH LF.prComponent LF.prComponent_genuineLF 4 (by simpa using LF.prComponent_innerCHSH)
def bellExclusionClaim : Claim := .exclusion Bell.localTheory Bell.singletBehavior Bell.quantumSeparation.excludes

def echoClaim : Claim := .theoremResult _ Memory.echo_probability
def leakClaim : Claim := .theoremResult _ Memory.leakedEcho_probability
def phaseClaim : Claim := .theoremResult _ Memory.phaseEcho_probability

def memoryClaim (m : Memory.Model) (gates : List Memory.Gate) : Claim :=
  .exact (Memory.probability m gates : ℝ) (Memory.probability m gates) rfl

def noisyBellClaim (m : Memory.Model) : Claim :=
  .exact (Bell.score (DephasedSinglet.behavior Bell.alice Bell.bob (m.strength : ℝ)
    (by exact_mod_cast m.nonneg) (by exact_mod_cast m.atMostOne)))
    ((1502-1152*m.strength)/625) (by rw [DephasedSinglet.bell_score]; push_cast; rfl)
def noisyLFClaim (m : Memory.Model) : Claim :=
  .exact (RealQuantum.genuineLF (DephasedSinglet.behavior RealQuantum.lfAlice RealQuantum.lfBob
    (m.strength : ℝ) (by exact_mod_cast m.nonneg) (by exact_mod_cast m.atMostOne)))
    ((1214656-476928*m.strength)/180625) (by rw [DephasedSinglet.LF_score]; push_cast; rfl)

def triangleClaim : Claim := .theoremResult _ Research.no_pairwise_gluing
def recoveryClaim : Claim := .theoremResult _ Research.restricted_recovery
def jointRecoveryClaim : Claim := .theoremResult _ Research.joint_recovery
def relabelClaim : Claim := .theoremResult _ Research.passive_relabel
def queryClaim : Claim := .theoremResult _ Research.random_query_bound
def orderClaim : Claim := .theoremResult _ Research.noisy_order_probability
def mediatorClaim : Claim := .theoremResult _ Research.phase_state_not_complex_product
def agreementClaim : Claim := .theoremResult _ Research.public_error_bound
def contaminationClaim : Claim := .theoremResult _ Shared.LF_contamination_required
def nsFractionClaim : Claim := .theoremResult _ Shared.LF_NS_fraction_required

def lfExclusionClaim : Claim :=
  .exclusion LF.theory
    (LocalFriendlinessRecipe.interpret LocalFriendlinessRecipe.Law.coherent LocalFriendlinessRecipe.reference)
    LocalFriendlinessRecipe.coherent_excludes_LF

def lfProtocolBridgeClaim : Claim := .theoremResult _ LocalFriendlinessRecipe.reference_behavior
def lfDephasedProfileClaim : Claim := .theoremResult _ LocalFriendlinessRecipe.fully_dephased_realizes_profile
def nsAttainmentClaim : Claim := .exact (RealQuantum.genuineLF Shared.nsExtreme) 10
  (by simpa using Shared.nsExtreme_score)

def researchSupporting (id : String) : List Claim :=
  if id == "P01" then [.theoremResult _ Research.triangle_mixture_bound]
  else if id == "P03" then [.theoremResult _ Shared.LF_NS_contamination_attained]
  else if id == "P05" then [.theoremResult _ Research.real_randomized_recovery, jointRecoveryClaim, relabelClaim]
  else if id == "P07" then [.theoremResult _ Research.phase_state_normalized, .theoremResult _ Research.phase_state_entangled]
  else if id == "P08" then [jointRecoveryClaim]
  else []

end
end OntologySeparation.Catalog
