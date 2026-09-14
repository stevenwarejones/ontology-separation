import OntologySeparation.Core.Operational
import QIT.Nonlocality.Bell

/-! A probability-preserving adapter; reuse Lean-QIT's Bell definitions and proofs. -/
namespace OntologySeparation
namespace Bell

noncomputable section

abbrev interface : Interface := { Setting := Fin 2 × Fin 2, Outcome := Bool × Bool }

/-- Keep the upstream behavior available while exposing our common interface. -/
def fromQIT (p : QIT.Bell.CHSHBehavior) : Behavior interface where
  prob s o := p.prob o.1 o.2 s.1 s.2
  nonneg _ _ := NNReal.coe_nonneg _
  normalized s := by
    have h := p.sum_prob s.1 s.2
    exact_mod_cast (show ∑ o : Bool × Bool, p.prob o.1 o.2 s.1 s.2 = 1 by
      simpa [Fintype.sum_prod_type] using h)

/-- The adapter preserves every probability entry by definition. -/
theorem fromQIT_prob (p : QIT.Bell.CHSHBehavior) (s : Fin 2 × Fin 2) (o : Bool × Bool) :
    (fromQIT p).prob s o = (p.prob o.1 o.2 s.1 s.2 : ℝ) := rfl

/-- Image of the upstream local class, not an assumed score bound. -/
def localTheory : Theory interface := fun p =>
  ∃ q, QIT.Bell.IsLocal q ∧ fromQIT q = p

def noSignalingTheory : Theory interface := fun p =>
  ∃ q, QIT.Bell.IsNoSignaling q ∧ fromQIT q = p

def correlator (p : Behavior interface) (x y : Fin 2) : ℝ :=
  ∑ o : Bool × Bool,
    QIT.Bell.CHSH.outcomeSign o.1 * QIT.Bell.CHSH.outcomeSign o.2 * p.prob (x, y) o

def score (p : Behavior interface) : ℝ :=
  correlator p 0 0 + correlator p 0 1 + correlator p 1 0 - correlator p 1 1

theorem score_fromQIT (p : QIT.Bell.CHSHBehavior) :
    score (fromQIT p) = QIT.Bell.CHSH.value p := by
  rw [QIT.Bell.CHSH.value_eq_correlators]
  rfl

def localBound : Bound localTheory score where
  ceiling := 2
  valid p hp := by
    obtain ⟨q, hq, rfl⟩ := hp
    rw [score_fromQIT]
    exact QIT.Bell.CHSH.value_le_two_of_isLocal q hq

def prWitness : Witness noSignalingTheory where
  behavior := fromQIT QIT.Bell.CHSH.prBox
  admissible := ⟨_, QIT.Bell.CHSH.prBox_isNoSignaling, rfl⟩

def local_vs_noSignaling : Separation localTheory noSignalingTheory score where
  bound := localBound
  witness := prWitness
  violation := by
    change (2 : ℝ) < score (fromQIT QIT.Bell.CHSH.prBox)
    rw [score_fromQIT, QIT.Bell.CHSH.value_prBox]
    norm_num

end
end Bell
end OntologySeparation
