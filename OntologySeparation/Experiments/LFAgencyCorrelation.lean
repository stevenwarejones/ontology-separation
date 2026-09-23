import OntologySeparation.Experiments.LFAgencyRelaxationDiagnostics
import Mathlib.Tactic

/-!
Exact correlation algebra for the real two-qubit singlet model used by the
Local-Agency relaxation study.
-/

namespace OntologySeparation.LFAgencyRelaxation.Correlation
noncomputable section

def blochX (a : RealQuantum.Basis) : ℝ := a.c^2 - a.s^2
def blochY (a : RealQuantum.Basis) : ℝ := 2*a.c*a.s

theorem bloch_unit (a : RealQuantum.Basis) :
    blochX a ^ 2 + blochY a ^ 2 = 1 := by
  unfold blochX blochY
  have h := a.unit
  nlinarith [sq_nonneg (a.c^2 - a.s^2)]

def basisCorr (a b : RealQuantum.Basis) : ℝ :=
  ∑ o : Bool × Bool,
    RealQuantum.sign o.1 * RealQuantum.sign o.2 *
      RealQuantum.probability a b o.1 o.2

theorem basisCorr_formula (a b : RealQuantum.Basis) :
    basisCorr a b = -(blochX a * blochX b + blochY a * blochY b) := by
  simp [basisCorr, RealQuantum.probability, RealQuantum.Basis.vector,
    RealQuantum.sign, Fintype.sum_prod_type, blochX, blochY]
  ring

theorem probability_eq_corr (a b : RealQuantum.Basis) (x y : Bool) :
    RealQuantum.probability a b x y =
      (1 + RealQuantum.sign x * RealQuantum.sign y * basisCorr a b) / 4 := by
  have hab : (a.c^2+a.s^2)*(b.c^2+b.s^2) = 1 := by
    rw [a.unit, b.unit]
    norm_num
  cases x <;> cases y <;>
    simp [RealQuantum.probability, RealQuantum.Basis.vector, RealQuantum.sign,
      basisCorr_formula, blochX, blochY] <;>
    nlinarith [hab]

theorem correlator_behavior {n : Nat} (A B : Fin n → RealQuantum.Basis) (x y : Fin n) :
    RealQuantum.correlator (RealQuantum.behavior A B) x y = basisCorr (A x) (B y) := by
  rfl

end
end OntologySeparation.LFAgencyRelaxation.Correlation
