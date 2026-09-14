import OntologySeparation.Adapters.Shared

/-! Explicit extension of the memory-noise family to a bipartite preparation.
This extra preparation/channel law is NOT implied by a two-qubit memory toy. -/
namespace OntologySeparation.DephasedSinglet
noncomputable section

/-- The computationally dephased singlet is the equal mixture |01>, |10>.
Local projective probabilities are products of the corresponding squared components. -/
def diagonalProb (a b : RealQuantum.Basis) (s t : Bool) : ℝ :=
  ((a.vector s).1^2 * (b.vector t).2^2 + (a.vector s).2^2 * (b.vector t).1^2) / 2

def diagonal {n : Nat} (a b : Fin n → RealQuantum.Basis) :
    Behavior (RealQuantum.interface n) where
  prob xy st := diagonalProb (a xy.1) (b xy.2) st.1 st.2
  nonneg xy st := by unfold diagonalProb; positivity
  normalized xy := by
    have h : ((a xy.1).c^2+(a xy.1).s^2)*((b xy.2).c^2+(b xy.2).s^2) = 1 := by
      rw [(a xy.1).unit, (b xy.2).unit]; norm_num
    simp [diagonalProb, RealQuantum.Basis.vector, Fintype.sum_prod_type]
    nlinarith [h]

/-- p is the weight of complete Z dephasing on the singlet. -/
def behavior {n : Nat} (a b : Fin n → RealQuantum.Basis) (p : ℝ)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : Behavior (RealQuantum.interface n) :=
  (diagonal a b).mix (RealQuantum.behavior a b) p h0 h1

theorem diagonal_bell : Bell.score (diagonal Bell.alice Bell.bob) = 14/25 := by
  norm_num [Bell.score, Bell.correlator, diagonal, diagonalProb, Bell.alice, Bell.bob,
    RealQuantum.Basis.vector, Bell.b43, Bell.b01, RealQuantum.basis45, RealQuantum.basis35,
    QIT.Bell.CHSH.outcomeSign, Fintype.sum_prod_type]

/-- Correlation scores are affine in the state mixture. -/
theorem bell_score (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Bell.score (behavior Bell.alice Bell.bob p h0 h1) = (1502-1152*p)/625 := by
  have hm : Bell.score (behavior Bell.alice Bell.bob p h0 h1) =
      p*Bell.score (diagonal Bell.alice Bell.bob) + (1-p)*Bell.score Bell.singletBehavior := by
    simp [Bell.score, Bell.correlator, behavior, Behavior.mix, Bell.singletBehavior,
      QIT.Bell.CHSH.outcomeSign, Fintype.sum_prod_type]
    ring
  rw [hm, diagonal_bell, Bell.singlet_score]
  ring

theorem diagonal_LF : RealQuantum.genuineLF (diagonal RealQuantum.lfAlice RealQuantum.lfBob) =
    737728/180625 := by
  norm_num [RealQuantum.genuineLF, RealQuantum.marginalA, RealQuantum.marginalB,
    RealQuantum.correlator, diagonal, diagonalProb, RealQuantum.Basis.vector,
    RealQuantum.zBasis, RealQuantum.basis35, RealQuantum.basis45, RealQuantum.basis1517,
    RealQuantum.sign, Fintype.sum_prod_type]

theorem LF_score (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    RealQuantum.genuineLF (behavior RealQuantum.lfAlice RealQuantum.lfBob p h0 h1) =
      (1214656-476928*p)/180625 := by
  rw [behavior, Shared.LF_mix_score, diagonal_LF]
  change p * (737728/180625) + (1-p) * RealQuantum.genuineLF RealQuantum.lfBehavior = _
  rw [RealQuantum.lfBehavior_value]
  ring

theorem bell_noise_threshold (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    2 < Bell.score (behavior Bell.alice Bell.bob p h0 h1) ↔ p < 7/32 := by
  rw [bell_score]
  constructor <;> intro h <;> linarith

theorem LF_noise_threshold (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    6 < RealQuantum.genuineLF (behavior RealQuantum.lfAlice RealQuantum.lfBob p h0 h1) ↔
      p < 65453/238464 := by
  rw [LF_score]
  constructor <;> intro h <;> linarith

end
end OntologySeparation.DephasedSinglet
