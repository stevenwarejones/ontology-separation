import OntologySeparation.Models.LocalFriendliness
import OntologySeparation.Models.RealQuantum

/-! The genuine LF bound and explicit singlet violation share one observable. -/
namespace OntologySeparation.LF
noncomputable section

/-- The probability-table score equals the component's moment score. -/
theorem component_score_bridge (q : Component) :
    RealQuantum.genuineLF q.behavior = componentScore q := by
  cases hc : q.charlie <;> cases hd : q.debbie <;>
    simp [RealQuantum.genuineLF, RealQuantum.marginalA, RealQuantum.marginalB,
    RealQuantum.correlator, Component.behavior, Component.prob, Component.a,
    Component.b, Component.e, RealQuantum.sign, sign, componentScore,
    Fintype.sum_prod_type, hc, hd] <;> ring

/-- Linearity carries the component theorem to the public mixture distribution. -/
theorem model_score_bridge {ι : Type} [Fintype ι] (m : Model ι) :
    RealQuantum.genuineLF m.behavior = m.score := by
  classical
  have hA (x y : Fin 3) : RealQuantum.marginalA m.behavior x y =
      ∑ i, m.weight i * RealQuantum.marginalA (m.component i).behavior x y := by
    simp only [RealQuantum.marginalA, Model.behavior, Component.behavior]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro o _
    ring
  have hB (x y : Fin 3) : RealQuantum.marginalB m.behavior x y =
      ∑ i, m.weight i * RealQuantum.marginalB (m.component i).behavior x y := by
    simp only [RealQuantum.marginalB, Model.behavior, Component.behavior]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro o _
    ring
  have hE (x y : Fin 3) : RealQuantum.correlator m.behavior x y =
      ∑ i, m.weight i * RealQuantum.correlator (m.component i).behavior x y := by
    simp only [RealQuantum.correlator, Model.behavior, Component.behavior]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro o _
    ring
  unfold RealQuantum.genuineLF
  simp_rw [hA, hB, hE]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  unfold Model.score
  apply Finset.sum_congr rfl
  intro i _
  rw [← component_score_bridge]
  unfold RealQuantum.genuineLF
  ring


def genuineBound : Bound theory RealQuantum.genuineLF where
  ceiling := 6
  valid p hp := by
    obtain ⟨ι, hι, m, rfl⟩ := hp
    letI := hι
    rw [model_score_bridge]
    exact m.score_le_six

def quantumSeparation : Separation theory (RealQuantum.singletTheory 3)
    RealQuantum.genuineLF where
  bound := genuineBound
  witness := ⟨RealQuantum.lfBehavior, RealQuantum.lfBehavior_realized⟩
  violation := RealQuantum.lfBehavior_violates

end
end OntologySeparation.LF
