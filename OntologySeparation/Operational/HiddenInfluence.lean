import OntologySeparation.Core.Extensions
import OntologySeparation.Certificates.ForcedSignaling

/-! Finite conditional locality for a blind pair B,C. A,D are the early parties.
A hidden atom specifies early outcomes (a,d) and complete response tables for B,C.
Its distribution may depend on early settings (x,w), never on late choices (y,z).
This is a causal response model, not a derivation from spacetime geometry. -/
namespace OntologySeparation.HiddenInfluence
open scoped BigOperators
abbrev Atom := Fin 256
abbrev Early := Fin 4
abbrev Late := Fin 4
abbrev Outcome := Fin 16
abbrev Context := Fin 16
abbrev Recipient := Fin 8

def early (j : Atom) : Early := ⟨j.val / 64, by omega⟩
private def bitResponse (table setting : ℕ) : ℕ := table / (2 ^ setting) % 2

/-- Output order abcd; atom order x,w,a,d,fB,fC. The early context is selected
by `early`; the two late outputs consult only their own setting. -/
def output (j : Atom) (l : Late) : Outcome :=
  ⟨8 * (j.val / 32 % 2) + 4 * bitResponse (j.val / 4 % 4) (l.val / 2) +
    2 * bitResponse (j.val % 4) (l.val % 2) + j.val / 16 % 2, by
    unfold bitResponse
    have h1 := Nat.mod_lt (j.val / (2 ^ (l.val / 2)) / 4) (by omega : 0 < 2)
    have h2 := Nat.mod_lt ((j.val / 4 % 4) / 2 ^ (l.val / 2)) (by omega : 0 < 2)
    have h3 := Nat.mod_lt ((j.val % 4) / 2 ^ (l.val % 2)) (by omega : 0 < 2)
    omega⟩

/-- Separate normalized hidden-atom distributions for each early setting.
No LP inequality, signaling budget or score bound is assumed here. -/
structure Model where
  weight : Atom → ℝ
  nonnegative : ∀ j, 0 ≤ weight j
  normalized : ∀ e, ∑ j, (if early j = e then weight j else 0) = 1

abbrev interface : Interface := { Setting := Early × Late, Outcome := Outcome }

noncomputable def Model.behavior (m : Model) : Behavior interface where
  prob s o := ∑ j, if early j = s.1 ∧ output j s.2 = o then m.weight j else 0
  nonneg s o := Finset.sum_nonneg fun j _ => by split <;> simp [m.nonnegative]
  normalized s := by
    rw [Finset.sum_comm]
    simpa [ite_and, Finset.sum_ite_irrel] using m.normalized s.1

/-- Observable mean; no hidden variables appear in the statistic's definition. -/
noncomputable def mean (p : Behavior interface) (e : Early) (l : Late)
    (f : Outcome → ℝ) : ℝ := ∑ o, p.prob (e,l) o * f o

theorem mean_eq (m : Model) (e : Early) (l : Late) (f : Outcome → ℝ) :
    mean m.behavior e l f = ∑ j, (if early j = e then f (output j l) else 0) * m.weight j := by
  unfold mean Model.behavior
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : early j = e <;> simp [h, mul_comm]

/-- Recipient marginal after discarding one party's output. -/
noncomputable def marginal (p : Behavior interface) (e : Early) (l : Late)
    (project : Outcome → Recipient) (o : Recipient) : ℝ :=
  mean p e l (fun full => if project full = o then 1 else 0)

def recipientA (o : Outcome) : Recipient := ⟨o.val % 8, by omega⟩
def recipientD (o : Outcome) : Recipient := ⟨o.val / 2, by omega⟩

def contextEarly (c : Context) (side : Bool) : Early :=
  ⟨if c.val < 8 then 2 * side.toNat + c.val / 4
    else 2 * ((c.val - 8) / 4) + side.toNat, by cases side <;> simp <;> split <;> omega⟩
def contextLate (c : Context) : Late := ⟨c.val % 4, by omega⟩
def project (c : Context) : Outcome → Recipient :=
  if c.val < 8 then recipientA else recipientD

/-- Signed change in the full recipient distribution under an early setting flip. -/
noncomputable def difference (p : Behavior interface) (c : Context) (o : Recipient) : ℝ :=
  marginal p (contextEarly c false) (contextLate c) (project c) o -
    marginal p (contextEarly c true) (contextLate c) (project c) o

/-- Total variation, including the factor 1/2, in one specified comparison. -/
noncomputable def tv (p : Behavior interface) (c : Context) : ℝ :=
  (∑ o, |difference p c o|) / 2

/-- All 16 early-setting comparisons, not an average or one selected marginal. -/
def Within (p : Behavior interface) (delta : ℝ) : Prop := ∀ c, tv p c ≤ delta

def eventCoeff (e : Early) (l : Late) (proj : Outcome → Recipient)
    (o : Recipient) (j : Atom) : ℤ :=
  if early j = e ∧ proj (output j l) = o then 1 else 0

def differenceCoeff (c : Context) (o : Recipient) (j : Atom) : ℤ :=
  eventCoeff (contextEarly c false) (contextLate c) (project c) o j -
    eventCoeff (contextEarly c true) (contextLate c) (project c) o j

theorem difference_eq (m : Model) (c : Context) (o : Recipient) :
    difference m.behavior c o = ∑ j, (differenceCoeff c o j : ℝ) * m.weight j := by
  unfold difference marginal
  rw [mean_eq, mean_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [differenceCoeff, eventCoeff, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero, sub_mul, ite_and]

private def sign (n : ℕ) : ℤ := if n % 2 = 0 then 1 else -1

def termEarly (t : Fin 6) : Early := (#[1,1,2,2,2,1] : Array Early)[t.val]
def termLate (t : Fin 6) : Late := (#[0,2,0,2,0,1] : Array Late)[t.val]
def termWeight (t : Fin 6) : ℤ := (#[1,1,1,-1,2,2] : Array ℤ)[t.val]
/-- AB, AB, ABD, ABD, CD, ACD outcome products, in that order. -/
def parity (t : Fin 6) (o : Outcome) : ℤ :=
  let a := o.val / 8
  let b := o.val / 4 % 2
  let c := o.val / 2 % 2
  let d := o.val % 2
  if t.val < 2 then sign (a+b)
  else if t.val < 4 then sign (a+b+d)
  else if t.val = 4 then sign (c+d) else sign (a+c+d)

/-- Fixed operational completion:
AB(0,0,0,1)+AB(0,1,0,1)+ABD(1,0,0,0)-ABD(1,1,0,0)
+2CD(1,0,0,0)+2ACD(0,0,1,1), settings ordered x,y,z,w. -/
noncomputable def score (p : Behavior interface) : ℝ :=
  ∑ t : Fin 6, (termWeight t : ℝ) * mean p (termEarly t) (termLate t) (fun o => parity t o)

def scoreCoeff (j : Atom) : ℤ :=
  ∑ t : Fin 6, termWeight t *
    (if early j = termEarly t then parity t (output j (termLate t)) else 0)

theorem score_eq (m : Model) : score m.behavior = ∑ j, (scoreCoeff j : ℝ) * m.weight j := by
  simp only [score, mean_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [scoreCoeff, Int.cast_sum, Int.cast_mul, Finset.sum_mul, mul_assoc]

end OntologySeparation.HiddenInfluence
