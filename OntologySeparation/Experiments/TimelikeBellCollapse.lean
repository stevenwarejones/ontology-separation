import OntologySeparation.Experiments.TimelikeOperationalCore
import OntologySeparation.Operational.Bell
import Mathlib.Tactic.FinCases

/-! In the 2222 reduction, the three operational timelike laws produce an
ordinary Bell screening-off model.

This is a negative discovery result: the reduced core cannot by itself reveal a
new beyond-Bell structure. A genuinely new timelike theorem must retain more of
the pseudo-event semantics than the three consequence laws formalized here. -/
namespace OntologySeparation.TimelikeBellCollapse
noncomputable section
open TimelikeOperationalCore

def outcomeProb (mean : ℝ) (o : Bool) : ℝ :=
  (1 + RealQuantum.sign o * mean) / 2

theorem outcomeProb_nonneg (mean : ℝ) (h : -1 ≤ mean ∧ mean ≤ 1) (o : Bool) :
    0 ≤ outcomeProb mean o := by
  cases o <;> simp [outcomeProb, RealQuantum.sign] <;> linarith

theorem outcomeProb_sum (mean : ℝ) :
    ∑ o : Bool, outcomeProb mean o = 1 := by
  simp [outcomeProb, RealQuantum.sign, Fintype.sum_bool]
  ring

def productResponse (alice : Fin 2 → ℝ) (bob : Fin 2 → ℝ)
    (ha : ∀ x, -1 ≤ alice x ∧ alice x ≤ 1)
    (hb : ∀ y, -1 ≤ bob y ∧ bob y ≤ 1) :
    Behavior Bell.interface where
  prob s o := outcomeProb (alice s.1) o.1 * outcomeProb (bob s.2) o.2
  nonneg s o := mul_nonneg
    (outcomeProb_nonneg _ (ha s.1) o.1)
    (outcomeProb_nonneg _ (hb s.2) o.2)
  normalized s := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [outcomeProb_sum]
    simp [outcomeProb_sum]

theorem productResponse_marginalA
    (alice : Fin 2 → ℝ) (bob : Fin 2 → ℝ)
    (ha : ∀ x, -1 ≤ alice x ∧ alice x ≤ 1)
    (hb : ∀ y, -1 ≤ bob y ∧ bob y ≤ 1)
    (x y : Fin 2) (a : Bool) :
    ∑ b, (productResponse alice bob ha hb).prob (x,y) (a,b) =
      outcomeProb (alice x) a := by
  simp [productResponse, ← Finset.mul_sum, outcomeProb_sum]

theorem productResponse_marginalB
    (alice : Fin 2 → ℝ) (bob : Fin 2 → ℝ)
    (ha : ∀ x, -1 ≤ alice x ∧ alice x ≤ 1)
    (hb : ∀ y, -1 ≤ bob y ∧ bob y ≤ 1)
    (x y : Fin 2) (b : Bool) :
    ∑ a, (productResponse alice bob ha hb).prob (x,y) (a,b) =
      outcomeProb (bob y) b := by
  rw [show (∑ a, (productResponse alice bob ha hb).prob (x,y) (a,b)) =
    (∑ a, outcomeProb (alice x) a) * outcomeProb (bob y) b by
      simp [productResponse, Finset.sum_mul]]
  rw [outcomeProb_sum, one_mul]

theorem productResponse_noSignaling
    (alice : Fin 2 → ℝ) (bob : Fin 2 → ℝ)
    (ha : ∀ x, -1 ≤ alice x ∧ alice x ≤ 1)
    (hb : ∀ y, -1 ≤ bob y ∧ bob y ≤ 1) :
    Shared.NoSignaling (productResponse alice bob ha hb) := by
  constructor
  · intro x y y' a
    rw [productResponse_marginalA, productResponse_marginalA]
  · intro x x' y b
    rw [productResponse_marginalB, productResponse_marginalB]

theorem productResponse_outcomeIndependent
    (alice : Fin 2 → ℝ) (bob : Fin 2 → ℝ)
    (ha : ∀ x, -1 ≤ alice x ∧ alice x ≤ 1)
    (hb : ∀ y, -1 ≤ bob y ∧ bob y ≤ 1)
    (x y : Fin 2) (a b : Bool) :
    (productResponse alice bob ha hb).prob (x,y) (a,b) =
      (∑ b', (productResponse alice bob ha hb).prob (x,y) (a,b')) *
      (∑ a', (productResponse alice bob ha hb).prob (x,y) (a',b)) := by
  rw [productResponse_marginalA, productResponse_marginalB]
  rfl

theorem productResponse_correlator
    (alice : Fin 2 → ℝ) (bob : Fin 2 → ℝ)
    (ha : ∀ x, -1 ≤ alice x ∧ alice x ≤ 1)
    (hb : ∀ y, -1 ≤ bob y ∧ bob y ≤ 1)
    (x y : Fin 2) :
    Bell.correlator (productResponse alice bob ha hb) x y = alice x * bob y := by
  simp [Bell.correlator, productResponse, outcomeProb, RealQuantum.sign,
    QIT.Bell.CHSH.outcomeSign, Fintype.sum_prod_type]
  ring

def toOperationalBell (m : Model) : OperationalBell.Model Bool where
  preparation := m.hidden
  response l := productResponse
    (fun x => m.alice l x 0)
    (fun y => m.bob l 0 y)
    (fun x => m.alice_bounds l x 0)
    (fun y => m.bob_bounds l 0 y)

theorem toOperationalBell_independent (m : Model)
    (hs : Holds .stablePseudoEvents m) :
    OperationalBell.MeasurementIndependent (toOperationalBell m) := by
  change ∀ s t l, (m.hidden s).mass l = (m.hidden t).mass l
  exact hs

theorem toOperationalBell_local (m : Model) :
    OperationalBell.ParameterIndependent (toOperationalBell m) := by
  intro l
  exact productResponse_noSignaling _ _
    (fun x => m.alice_bounds l x 0)
    (fun y => m.bob_bounds l 0 y)

theorem toOperationalBell_screened (m : Model) :
    OperationalBell.OutcomeIndependent (toOperationalBell m) := by
  intro l x y a b
  exact productResponse_outcomeIndependent _ _
    (fun x => m.alice_bounds l x 0)
    (fun y => m.bob_bounds l 0 y) x y a b

/-- The visible correlators of the Bell screening-off embedding equal the
timelike model's correlators whenever the screening laws hold. -/
theorem correlator_preserved (m : Model)
    (hs : Holds .stablePseudoEvents m)
    (ha : Holds .aliceScreened m)
    (hb : Holds .bobScreened m)
    (x y : Fin 2) :
    Bell.correlator (toOperationalBell m).behavior x y = correlator m x y := by
  rw [TimelikeOperationalCore.correlator_base m hs ha hb]
  unfold OperationalBell.Model.behavior FiniteDistribution.mean
  simp_rw [hs (x,y) (0,0)]
  rw [Finset.sum_congr rfl]
  intro l _
  rw [productResponse_correlator]
  rfl

/-- Consequently the CHSH score is preserved exactly. -/
theorem score_preserved (m : Model)
    (hs : Holds .stablePseudoEvents m)
    (ha : Holds .aliceScreened m)
    (hb : Holds .bobScreened m) :
    Bell.score (toOperationalBell m).behavior = score m := by
  unfold Bell.score TimelikeOperationalCore.score
  rw [correlator_preserved m hs ha hb, correlator_preserved m hs ha hb,
    correlator_preserved m hs ha hb, correlator_preserved m hs ha hb]

/-- The reduced timelike core therefore embeds in the ordinary Bell
screening-off assumptions used elsewhere in this repository. -/
theorem embeds_screening_off (m : Model)
    (hs : Holds .stablePseudoEvents m)
    (ha : Holds .aliceScreened m)
    (hb : Holds .bobScreened m) :
    OperationalBell.OutcomeIndependent (toOperationalBell m) ∧
    OperationalBell.ParameterIndependent (toOperationalBell m) ∧
    OperationalBell.MeasurementIndependent (toOperationalBell m) :=
  ⟨toOperationalBell_screened m, toOperationalBell_local m,
    toOperationalBell_independent m hs⟩

end
end OntologySeparation.TimelikeBellCollapse
