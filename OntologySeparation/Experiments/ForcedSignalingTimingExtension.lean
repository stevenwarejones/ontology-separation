import OntologySeparation.Experiments.ForcedSignalingTiming
import OntologySeparation.Experiments.LC4FullDistribution
import OntologySeparation.Operational.VCausalTimingCompletion

/-! Extension of every LC4-matching blind protocol to the two connected timing
branches. The late measurement samples the normalized quantum conditional on
records already produced. It has access to both late inputs in that branch.
This is a finite menu of interventions, not one model for all possible layouts. -/
namespace OntologySeparation.ForcedSignalingTimingExtension
noncomputable section
open scoped BigOperators
open HiddenInfluence VCausal ForcedSignalingLC4Witness
open ForcedSignalingTiming LC4FullDistribution

private theorem map_recordProb (d : FiniteDistribution VisibleOutcome)
    (f : VisibleOutcome → Triple) (r : Triple) :
    (FiniteKernel.map d f).mass r = recordProb d f r := by
  simp [FiniteKernel.map_mass, recordProb, mul_ite]

private theorem run_abd_independent {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) (r : Triple) :
    recordProb (p.run e y z) abdRecord r = recordProb (p.run e y false) abdRecord r := by
  unfold recordProb Protocol.run
  rw [FiniteKernel.map_mean, FiniteKernel.map_mean]
  rfl

private theorem run_acd_independent {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) (r : Triple) :
    recordProb (p.run e y z) acdRecord r = recordProb (p.run e false z) acdRecord r := by
  unfold recordProb Protocol.run
  rw [FiniteKernel.map_mean, FiniteKernel.map_mean]
  rfl

theorem target_ABD_matches {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (r : Triple) :
    (FiniteKernel.map (p.run e y z) abdRecord).mass r =
      (FiniteKernel.map (quantum e y z) abdRecord).mass r := by
  obtain ⟨a,b,d⟩ := r
  have he : ∃ x w, earlyOf x w = e := by
    fin_cases e
    · exact ⟨false,false,rfl⟩
    · exact ⟨false,true,rfl⟩
    · exact ⟨true,false,rfl⟩
    · exact ⟨true,true,rfl⟩
  obtain ⟨x,w,rfl⟩ := he
  rw [map_recordProb, run_abd_independent, ← protocol_ABD, h.abd, quantum_abd]

theorem target_ACD_matches {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (r : Triple) :
    (FiniteKernel.map (p.run e y z) acdRecord).mass r =
      (FiniteKernel.map (quantum e y z) acdRecord).mass r := by
  obtain ⟨a,c,d⟩ := r
  have he : ∃ x w, earlyOf x w = e := by
    fin_cases e
    · exact ⟨false,false,rfl⟩
    · exact ⟨false,true,rfl⟩
    · exact ⟨true,false,rfl⟩
    · exact ⟨true,true,rfl⟩
  obtain ⟨x,w,rfl⟩ := he
  rw [map_recordProb, run_acd_independent, ← protocol_ACD, h.acd, quantum_acd]

/-- The only newly sampled information is the delayed party's outcome. The
preservation theorem states this on every positive-probability transition. -/
def delayC {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) : FiniteDistribution VisibleOutcome :=
  FiniteKernel.complete (p.run e y z) (quantum e y z) abdRecord

def delayB {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) : FiniteDistribution VisibleOutcome :=
  FiniteKernel.complete (p.run e y z) (quantum e y z) acdRecord

theorem delayC_quantum {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o : VisibleOutcome) :
    (delayC p e y z).mass o = (quantum e y z).mass o :=
  FiniteKernel.complete_eq_target _ _ _ (target_ABD_matches p h e y z) o

theorem delayB_quantum {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o : VisibleOutcome) :
    (delayB p e y z).mass o = (quantum e y z).mass o :=
  FiniteKernel.complete_eq_target _ _ _ (target_ACD_matches p h e y z) o

theorem delayC_keeps_existing_records {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o o' : VisibleOutcome)
    (ho : (p.run e y z).mass o ≠ 0)
    (ho' : (FiniteKernel.condition (quantum e y z) abdRecord (abdRecord o)).mass o' ≠ 0) :
    abdRecord o' = abdRecord o :=
  FiniteKernel.complete_preserves_record _ _ _ (target_ABD_matches p h e y z) o o' ho ho'

theorem delayB_keeps_existing_records {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o o' : VisibleOutcome)
    (ho : (p.run e y z).mass o ≠ 0)
    (ho' : (FiniteKernel.condition (quantum e y z) acdRecord (acdRecord o)).mass o' ≠ 0) :
    acdRecord o' = acdRecord o :=
  FiniteKernel.complete_preserves_record _ _ _ (target_ACD_matches p h e y z) o o' ho ho'


/-- A single mechanism for the blind branch and both connected branches. -/
def quantumTiming {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) : TimingProtocol p :=
  TimingProtocol.completeTarget p quantum

theorem quantumTiming_runC {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o : VisibleOutcome) :
    ((quantumTiming p).runC e y z).mass o = (quantum e y z).mass o :=
  TimingProtocol.completeTarget_runC p quantum e y z (target_ABD_matches p h e y z) o

theorem quantumTiming_runB {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (e : Early) (y z : Bool) (o : VisibleOutcome) :
    ((quantumTiming p).runB e y z).mass o = (quantum e y z).mass o :=
  TimingProtocol.completeTarget_runB p quantum e y z (target_ACD_matches p h e y z) o

theorem quantumTiming_connected {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel) :
    ConnectedMatches (quantumTiming p) := by
  constructor
  · intro x y w a b d
    unfold recordProb
    simp_rw [quantumTiming_runC p h]
    change recordProb _ _ _ = _
    rw [← map_recordProb, quantum_abd]
  · intro x z w a c d
    unfold recordProb
    simp_rw [quantumTiming_runB p h]
    change recordProb _ _ _ = _
    rw [← map_recordProb, quantum_acd]

/-- The exact blind optimum is attained even when both delayed branches must
reproduce the full quantum joint distribution. This is a finite timing menu. -/
theorem attaining_timing_extension {L : Layout} {v : ℚ} {order : EarlyOrder}
    (timing : TimingLayout L v) (ho : GeometryOrder L v order) :
    ∃ (m : VCausal.Model L v order (EarlyRecord × (Early → Strategy)))
      (t : TimingProtocol m.toProtocol),
      ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel ∧
      m.toProtocol.toModel.signaling = (Real.sqrt 2 - 1) / 4 ∧
      (∀ e y z o, (t.runC e y z).mass o = (quantum e y z).mass o) ∧
      (∀ e y z o, (t.runB e y z).mass o = (quantum e y z).mass o) := by
  let hL := timing.blind
  let m := ForcedSignalingVCausal.witnessOn hL ho
  have hm := ForcedSignalingVCausal.witnessOn_matches hL ho
  exact ⟨m, quantumTiming m.toProtocol, hm,
    ForcedSignalingVCausal.witnessOn_signaling hL ho,
    quantumTiming_runC m.toProtocol hm, quantumTiming_runB m.toProtocol hm⟩

end
end OntologySeparation.ForcedSignalingTimingExtension
