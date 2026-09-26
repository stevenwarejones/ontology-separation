import OntologySeparation.Operational.VCausalFiniteSupport
import OntologySeparation.Experiments.ForcedSignalingVCausal
import OntologySeparation.Operational.VCausalAssumptions

open OntologySeparation OntologySeparation.VCausal
open OntologySeparation.HiddenInfluence

example (p q r : Event) (v : ℚ) (hpq : precedes v p q) (hqr : precedes v q r) :
    precedes v p r := precedes_trans hpq hqr

example : ¬ EarlyAllowed .aFirst (fun e => (backwardsTable e).record) :=
  backwardsTable_not_allowed

example (order : EarlyOrder) (q : Early → FiniteDistribution Strategy) :
    (∃ (Ω : Type) (_ : Fintype Ω) (p : Protocol order Ω),
      ∀ e s, (p.strategies e).mass s = (q e).mass s) ↔
    (∃ (Ω : Type) (_ : Fintype Ω) (p : EarlyModel order Ω), EarlyMatches p q) :=
  realizable_iff_early order q

example {L : Layout} {v : ℚ} {order : EarlyOrder}
    (hL : LC4Layout L v) (ho : GeometryOrder L v order) :
    ∃ m : VCausal.Model L v order (EarlyRecord × (Early → Strategy)),
      ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel ∧
      m.toProtocol.toModel.signaling = (Real.sqrt 2 - 1) / 4 :=
  (ForcedSignalingVCausal.vcausal_exact_forced_signaling hL ho).2

private def concrete : Layout
  | .A => ⟨0,0⟩
  | .D => ⟨1,0⟩
  | .B => ⟨2,-1⟩
  | .C => ⟨2,1⟩

example : ∃ m : VCausal.Model concrete 2 .aFirst (EarlyRecord × (Early → Strategy)),
    ForcedSignalingTheorem2.MatchesCluster m.toProtocol.toModel ∧
    m.toProtocol.toModel.signaling = (Real.sqrt 2 - 1) / 4 := by
  apply (ForcedSignalingVCausal.vcausal_exact_forced_signaling (order := .aFirst) ?_ ?_).2
  · constructor <;> norm_num [concrete, precedes]
  · norm_num [GeometryOrder, concrete, precedes]

/-- A real B→C hidden connection must be rejected by the blind-layout predicate. -/
private def connectedLate : Layout
  | .A => ⟨0,0⟩
  | .D => ⟨1,0⟩
  | .B => ⟨2,0⟩
  | .C => ⟨3,0⟩

example : ¬ LC4Layout connectedLate 2 := by
  intro h
  exact h.bc (by norm_num [connectedLate, precedes])

/-- Hidden cones are open: equality at their boundary is rejected. -/
example : ¬ precedes 2 ⟨0,0⟩ ⟨1,2⟩ := by norm_num [precedes]

/-- An infinite ambient hidden space is allowed when its law has finite support. -/
example (p : SupportedProtocol .aFirst ℕ) (e : Early) (y z : Bool) (o : VisibleOutcome) :
    p.toProtocol.toModel.behavior.prob (e,lateFromBool y z) o.toOutcome =
      ∑ ω ∈ p.support, p.weight ω * (if (p.table ω e).visible y z = o then 1 else 0) :=
  p.full_behavior e y z o
