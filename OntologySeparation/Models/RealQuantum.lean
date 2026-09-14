import OntologySeparation.Core.Operational
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact Born probabilities for real projective measurements of a two-qubit singlet.
This is a restricted, explicit quantum model, not the class of all quantum theories.
The amplitude is det(u,v)/sqrt(2); no numerical simulator is trusted. -/
namespace OntologySeparation.RealQuantum

noncomputable section

/-- The first column of a real orthonormal qubit measurement basis. -/
structure Basis where
  c : ℝ
  s : ℝ
  unit : c ^ 2 + s ^ 2 = 1

/-- The outcome-true column is the orthogonal complement of outcome-false. -/
def Basis.vector (b : Basis) (o : Bool) : ℝ × ℝ :=
  if o then (-b.s, b.c) else (b.c, b.s)

/-- Squared singlet amplitude for two local projective outcomes. -/
def probability (a b : Basis) (x y : Bool) : ℝ :=
  ((a.vector x).1 * (b.vector y).2 - (a.vector x).2 * (b.vector y).1) ^ 2 / 2

theorem probability_nonneg (a b : Basis) (x y : Bool) : 0 ≤ probability a b x y := by
  unfold probability
  positivity

theorem probability_normalized (a b : Basis) :
    ∑ o : Bool × Bool, probability a b o.1 o.2 = 1 := by
  simp [Fintype.sum_prod_type, probability, Basis.vector]
  have hab : (a.c^2+a.s^2)*(b.c^2+b.s^2) = 1 := by rw [a.unit, b.unit]; norm_num
  nlinarith [hab]

/-- Identification with the Born rule, using a normalized singlet amplitude. -/
theorem probability_born (a b : Basis) (x y : Bool) :
    probability a b x y =
    (((a.vector x).1 * (b.vector y).2 - (a.vector x).2 * (b.vector y).1)
      / Real.sqrt 2) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rfl

theorem singlet_normalized :
    (1 / Real.sqrt 2 : ℝ) ^ 2 + (-1 / Real.sqrt 2 : ℝ) ^ 2 = 1 := by
  rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

abbrev interface (n : Nat) : Interface := { Setting := Fin n × Fin n, Outcome := Bool × Bool }

def behavior {n : Nat} (a b : Fin n → Basis) : Behavior (interface n) where
  prob xy ab := probability (a xy.1) (b xy.2) ab.1 ab.2
  nonneg _xy _ab := probability_nonneg _ _ _ _
  normalized _xy := probability_normalized _ _

/-- This model class has actual normalized measurement bases as witnesses. -/
def singletTheory (n : Nat) : Theory (interface n) := fun p =>
  ∃ a b : Fin n → Basis, behavior a b = p

def sign (o : Bool) : ℝ := if o then -1 else 1

def correlator {n : Nat} (p : Behavior (interface n)) (x y : Fin n) : ℝ :=
  ∑ o : Bool × Bool, sign o.1 * sign o.2 * p.prob (x, y) o

def marginalA {n : Nat} (p : Behavior (interface n)) (x : Fin n) (y : Fin n) : ℝ :=
  ∑ o : Bool × Bool, sign o.1 * p.prob (x, y) o

def marginalB {n : Nat} (p : Behavior (interface n)) (x : Fin n) (y : Fin n) : ℝ :=
  ∑ o : Bool × Bool, sign o.2 * p.prob (x, y) o

/-- Rational bases make exact experimental witnesses inexpensive to check. -/
def zBasis : Basis := ⟨1, 0, by norm_num⟩
def basis35 : Basis := ⟨3/5, -4/5, by norm_num⟩
def basis45 : Basis := ⟨4/5, -3/5, by norm_num⟩
def basis1517 : Basis := ⟨15/17, -8/17, by norm_num⟩

def lfAlice (x : Fin 3) : Basis := if x.val = 1 then basis35 else zBasis
def lfBob (y : Fin 3) : Basis := if y.val = 0 then basis45 else if y.val = 1 then zBasis else basis1517

@[simp] theorem lfAlice_zero : lfAlice 0 = zBasis := rfl
@[simp] theorem lfAlice_one : lfAlice 1 = basis35 := rfl
@[simp] theorem lfAlice_two : lfAlice 2 = zBasis := rfl
@[simp] theorem lfBob_zero : lfBob 0 = basis45 := rfl
@[simp] theorem lfBob_one : lfBob 1 = zBasis := rfl
@[simp] theorem lfBob_two : lfBob 2 = basis1517 := rfl

def lfBehavior : Behavior (interface 3) := behavior lfAlice lfBob

/-- Bong Eq. (13), with its bound not subtracted and zero-based settings. -/
def genuineLF (p : Behavior (interface 3)) : ℝ :=
  -marginalA p 0 0 - marginalA p 1 0 - marginalB p 0 0 - marginalB p 0 1
  -correlator p 0 0 - 2 * correlator p 0 1 - 2 * correlator p 1 0
  + 2 * correlator p 1 1 - correlator p 1 2 - correlator p 2 1 - correlator p 2 2

theorem lfBehavior_value : genuineLF lfBehavior = 1214656 / 180625 := by
  norm_num [genuineLF, marginalA, marginalB, correlator, lfBehavior, behavior,
    probability, Basis.vector, sign, zBasis, basis35,
    basis45, basis1517, Fintype.sum_prod_type]

theorem lfBehavior_violates : 6 < genuineLF lfBehavior := by
  rw [lfBehavior_value]
  norm_num

theorem lfBehavior_realized : singletTheory 3 lfBehavior := ⟨lfAlice, lfBob, rfl⟩

end
end OntologySeparation.RealQuantum
