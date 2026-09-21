import OntologySeparation.Operational.Bell
import OntologySeparation.Operational.FriendRecords
import OntologySeparation.Core.Channels

/-! Countermodels to individual Bell laws; no claim that nature implements PR boxes. -/
namespace OntologySeparation.Countermodels
noncomputable section
def deterministic (f : Bell.interface.Setting → Bool × Bool) : Behavior Bell.interface where
  prob s := (Channel.deterministic f s).mass
  nonneg s := (Channel.deterministic f s).nonneg
  normalized s := (Channel.deterministic f s).total
theorem deterministic_screening (f : Bell.interface.Setting → Bool × Bool)
    (x y : Fin 2) (a b : Bool) :
    (deterministic f).prob (x,y) (a,b) =
      (∑ b', (deterministic f).prob (x,y) (a,b')) * (∑ a', (deterministic f).prob (x,y) (a',b)) := by
  cases h : f (x,y) with
  | mk c d => cases c <;> cases d <;> cases a <;> cases b <;>
      simp [deterministic, Channel.deterministic, h]
def unitPrior : FiniteDistribution Unit := ⟨fun _ => 1, by simp, by simp⟩
def signaling : OperationalBell.Model Unit where
  preparation := fun _ => unitPrior
  response := fun _ => deterministic (fun s => (false, decide (s.1 = 1 ∧ s.2 = 1)))
theorem signaling_screened : OperationalBell.OutcomeIndependent signaling :=
  fun _ x y a b => deterministic_screening _ x y a b
theorem signaling_independent : OperationalBell.MeasurementIndependent signaling := by
  intro s t l; rfl
theorem signaling_score : Bell.score signaling.behavior = 4 := by
  norm_num [Bell.score, Bell.correlator, OperationalBell.Model.behavior, signaling,
    deterministic, Channel.deterministic, unitPrior, QIT.Bell.CHSH.outcomeSign, Fintype.sum_prod_type]
theorem signaling_not_local : ¬ OperationalBell.ParameterIndependent signaling := by
  intro h
  have hb := OperationalBell.chsh_bound signaling signaling_screened h signaling_independent
  rw [signaling_score] at hb
  norm_num at hb
def dependentPreparation : OperationalBell.Model (Bool × Bool) where
  preparation s := ⟨(Bell.fromQIT QIT.Bell.CHSH.prBox).prob s,
    (Bell.fromQIT QIT.Bell.CHSH.prBox).nonneg s, (Bell.fromQIT QIT.Bell.CHSH.prBox).normalized s⟩
  response l := deterministic (fun _ => l)
theorem dependent_screened : OperationalBell.OutcomeIndependent dependentPreparation :=
  fun _ x y a b => deterministic_screening _ x y a b
theorem dependent_local : OperationalBell.ParameterIndependent dependentPreparation := by
  intro l
  constructor <;> intros <;> rfl
theorem dependent_probability (s : Bell.interface.Setting) (o : Bool × Bool) :
    dependentPreparation.behavior.prob s o = (Bell.fromQIT QIT.Bell.CHSH.prBox).prob s o := by
  simp [OperationalBell.Model.behavior, dependentPreparation, deterministic, Channel.deterministic]
theorem dependent_score : Bell.score dependentPreparation.behavior = 4 := by
  have hs : Bell.score dependentPreparation.behavior = Bell.score (Bell.fromQIT QIT.Bell.CHSH.prBox) := by
    simp only [Bell.score, Bell.correlator, dependent_probability]
  rw [hs, Bell.score_fromQIT, QIT.Bell.CHSH.value_prBox]
theorem dependent_not_independent : ¬ OperationalBell.MeasurementIndependent dependentPreparation := by
  intro h
  have hb := OperationalBell.chsh_bound dependentPreparation dependent_screened dependent_local h
  rw [dependent_score] at hb
  norm_num at hb

/-- Quantum public probabilities with candidate fixed record labels. The labels
are not assumed readable; that law can be tested and is disproved below. -/
def quantumFriendCandidate : FriendRecords.Model Unit where
  preparation := fun _ => unitPrior
  response := fun _ => RealQuantum.lfBehavior
  charlie := fun _ => false
  debbie := fun _ => false

theorem quantumFriend_local : FriendRecords.ConditionalLocality quantumFriendCandidate := by
  intro l
  exact Shared.singlet_noSignaling RealQuantum.lfAlice RealQuantum.lfBob

theorem quantumFriend_independent : FriendRecords.IndependentPreparation quantumFriendCandidate := by
  intro s t l; rfl

theorem quantumFriend_behavior : quantumFriendCandidate.behavior = RealQuantum.lfBehavior := by
  have he : quantumFriendCandidate.behavior.prob = RealQuantum.lfBehavior.prob := by
    funext s o
    simp [FriendRecords.Model.behavior, quantumFriendCandidate, unitPrior]
  cases ha : quantumFriendCandidate.behavior
  cases hb : RealQuantum.lfBehavior
  simp only [ha, hb] at he
  cases he
  rfl

theorem quantumFriend_not_readable : ¬ FriendRecords.ReadableRecords quantumFriendCandidate := by
  intro h
  have hb := FriendRecords.bound quantumFriendCandidate h quantumFriend_local quantumFriend_independent
  rw [quantumFriend_behavior] at hb
  exact (not_lt_of_ge hb) RealQuantum.lfBehavior_violates

theorem rejected_records_realized :
    (AssumptionProfile.mk .unspecified .reject .require .require).Realizable
      (FriendRecords.vocabulary (Λ := Unit)) :=
  ⟨quantumFriendCandidate, trivial, quantumFriend_not_readable,
    quantumFriend_local, quantumFriend_independent⟩

end
end OntologySeparation.Countermodels
