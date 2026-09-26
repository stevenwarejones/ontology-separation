import OntologySeparation.Experiments.ForcedSignalingLC4Witness
import OntologySeparation.Operational.VCausalTiming

namespace OntologySeparation.LC4FullDistribution
noncomputable section
open scoped BigOperators
open HiddenInfluence ForcedSignalingLC4 VCausal

instance : Inhabited VisibleOutcome := ⟨⟨false,false,false,false⟩⟩

/-- Exact rational coefficients, checked against every Born entry below.
This cache avoids reducing the same matrix products in each marginal proof. -/
private def bornTable : Array Q2 := #[
  q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (-1/16),
  q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (-1/16), q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (1/16),
  q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32),
  q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32),
  q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32),
  q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32),
  q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (-1/16),
  q (0) (0), q (1/8) (-1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (1/16), q (0) (0),
  q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (-1/16),
  q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (-1/16), q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (1/16),
  q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32),
  q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32),
  q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32),
  q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32),
  q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (-1/16),
  q (0) (0), q (1/8) (-1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (1/16), q (0) (0),
  q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (-1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (1/16),
  q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (-1/16),
  q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32),
  q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32),
  q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32),
  q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32),
  q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32),
  q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32),
  q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (1/16), q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (-1/16),
  q (1/8) (1/16), q (0) (0), q (0) (0), q (1/8) (-1/16), q (1/8) (-1/16), q (0) (0), q (0) (0), q (1/8) (1/16),
  q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32),
  q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32),
  q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32),
  q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32),
  q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32),
  q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (-1/32), q (1/16) (1/32), q (1/16) (1/32), q (1/16) (-1/32)]

private def tableProb (x y z w a b c d : Bool) : Q2 :=
  bornTable[128*x.toNat + 64*y.toNat + 32*z.toNat + 16*w.toNat +
    8*a.toNat + 4*b.toNat + 2*c.toNat + d.toNat]!

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullProb_eq_table : ∀ x y z w a b c d,
    fullProb x y z w a b c d = tableProb x y z w a b c d := by
  intro x y z w a b c d
  cases x <;> cases y <;> cases z <;> cases w <;> cases a <;> cases b <;> cases c <;> cases d <;>
    with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem coefficient_bounds : ∀ x y z w a b c d,
    let p := fullProb x y z w a b c d
    0 ≤ p.1 + 2*p.2 ∧ 0 ≤ p.1 - 2*p.2 := by
  simp only [fullProb_eq_table]
  intro x y z w a b c d
  cases x <;> cases y <;> cases z <;> cases w <;> cases a <;> cases b <;> cases c <;> cases d <;>
    with_unfolding_all decide +kernel

private theorem probability_nonnegative (x y z w a b c d : Bool) :
    0 ≤ Q2.toReal (fullProb x y z w a b c d) := by
  obtain ⟨hl,hu⟩ := coefficient_bounds x y z w a b c d
  have hlr : (0 : ℝ) ≤ ((fullProb x y z w a b c d).1 : ℝ) +
      2*((fullProb x y z w a b c d).2 : ℝ) := by exact_mod_cast hl
  have hur : (0 : ℝ) ≤ ((fullProb x y z w a b c d).1 : ℝ) -
      2*((fullProb x y z w a b c d).2 : ℝ) := by exact_mod_cast hu
  unfold Q2.toReal
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := ForcedSignalingLC4Witness.sqrtTwo_le_two
  by_cases h : (0 : ℝ) ≤ ((fullProb x y z w a b c d).2 : ℝ)
  · nlinarith
  · nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalQ : ∀ x y z w,
    (∑ o : VisibleOutcome, fullProb x y z w o.a o.b o.c o.d) = qrat 1 := by
  simp only [fullProb_eq_table]
  intro x y z w
  cases x <;> cases y <;> cases z <;> cases w <;>
    with_unfolding_all decide +kernel

def quantum (e : Early) (y z : Bool) : FiniteDistribution VisibleOutcome where
  mass o := Q2.toReal (fullProb (xSetting e) y z (wSetting e) o.a o.b o.c o.d)
  nonneg o := probability_nonnegative _ _ _ _ _ _ _ _
  total := by rw [← toReal_sum, totalQ, toReal_qrat]; norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem abdQ : ∀ x y z w a b d,
    (∑ o : VisibleOutcome, if abdRecord o = (a,b,d)
      then fullProb x y z w o.a o.b o.c o.d else 0) = abd x y w a b d := by
  simp only [abd, fullProb_eq_table]
  intro x y z w a b d
  cases x <;> cases y <;> cases z <;> cases w <;> cases a <;> cases b <;> cases d <;>
    with_unfolding_all decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem acdQ : ∀ x y z w a c d,
    (∑ o : VisibleOutcome, if acdRecord o = (a,c,d)
      then fullProb x y z w o.a o.b o.c o.d else 0) = acd x z w a c d := by
  simp only [acd, fullProb_eq_table]
  intro x y z w a c d
  cases x <;> cases y <;> cases z <;> cases w <;> cases a <;> cases c <;> cases d <;>
    with_unfolding_all decide +kernel

theorem quantum_abd (x y z w a b d : Bool) :
    (FiniteKernel.map (quantum (ForcedSignalingLC4Witness.earlyOf x w) y z) abdRecord).mass (a,b,d) =
      Q2.toReal (abd x y w a b d) := by
  rw [FiniteKernel.map_mass]
  have he : xSetting (ForcedSignalingLC4Witness.earlyOf x w) = x ∧
      wSetting (ForcedSignalingLC4Witness.earlyOf x w) = w := by
    cases x <;> cases w <;> decide
  simp only [quantum, he.1, he.2]
  rw [← abdQ x y z w a b d, toReal_sum]
  apply Finset.sum_congr rfl
  intro o _
  split <;> simp_all

theorem quantum_acd (x y z w a c d : Bool) :
    (FiniteKernel.map (quantum (ForcedSignalingLC4Witness.earlyOf x w) y z) acdRecord).mass (a,c,d) =
      Q2.toReal (acd x z w a c d) := by
  rw [FiniteKernel.map_mass]
  have he : xSetting (ForcedSignalingLC4Witness.earlyOf x w) = x ∧
      wSetting (ForcedSignalingLC4Witness.earlyOf x w) = w := by
    cases x <;> cases w <;> decide
  simp only [quantum, he.1, he.2]
  rw [← acdQ x y z w a c d, toReal_sum]
  apply Finset.sum_congr rfl
  intro o _
  split <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem noSignalAQ : ∀ y z w b c d,
    (∑ a : Bool, fullProb false y z w a b c d) =
    (∑ a : Bool, fullProb true y z w a b c d) := by
  simp only [fullProb_eq_table]
  intro y z w b c d
  cases y <;> cases z <;> cases w <;> cases b <;> cases c <;> cases d <;>
    with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem noSignalDQ : ∀ x y z a b c,
    (∑ d : Bool, fullProb x y z false a b c d) =
    (∑ d : Bool, fullProb x y z true a b c d) := by
  simp only [fullProb_eq_table]
  intro x y z a b c
  cases x <;> cases y <;> cases z <;> cases a <;> cases b <;> cases c <;>
    with_unfolding_all decide +kernel

/-- The full Born law has zero A-to-BCD signaling. -/
theorem quantum_noSignalA (y z w b c d : Bool) :
    (∑ a : Bool, (quantum (ForcedSignalingLC4Witness.earlyOf false w) y z).mass ⟨a,b,c,d⟩) =
    (∑ a : Bool, (quantum (ForcedSignalingLC4Witness.earlyOf true w) y z).mass ⟨a,b,c,d⟩) := by
  have he : ∀ x w, xSetting (ForcedSignalingLC4Witness.earlyOf x w) = x ∧
      wSetting (ForcedSignalingLC4Witness.earlyOf x w) = w := by decide +kernel
  simp only [quantum, he, ← toReal_sum, noSignalAQ]

/-- The full Born law has zero D-to-ABC signaling. -/
theorem quantum_noSignalD (x y z a b c : Bool) :
    (∑ d : Bool, (quantum (ForcedSignalingLC4Witness.earlyOf x false) y z).mass ⟨a,b,c,d⟩) =
    (∑ d : Bool, (quantum (ForcedSignalingLC4Witness.earlyOf x true) y z).mass ⟨a,b,c,d⟩) := by
  have he : ∀ x w, xSetting (ForcedSignalingLC4Witness.earlyOf x w) = x ∧
      wSetting (ForcedSignalingLC4Witness.earlyOf x w) = w := by decide +kernel
  simp only [quantum, he, ← toReal_sum, noSignalDQ]

end
end OntologySeparation.LC4FullDistribution
