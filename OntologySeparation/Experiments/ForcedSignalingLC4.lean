import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Exact LC4 target for forced signaling

This file defines the four-qubit linear-cluster target used by the
forced-signaling Theorem 2 calculation directly over Q(sqrt 2).

No probability table is imported.  The state is
  CZ_AB CZ_BC CZ_CD |+>^4
with amplitudes ±1/4, and the local projectors are exactly the Li et al.
settings:
  A = (X,Z)
  B = ((Z+X)/sqrt 2, (Z-X)/sqrt 2)
  C = (Z,X)
  D = (X,Z).

The full Born probabilities and the observable no-blind-pair ABD/ACD
marginals are computed by finite matrix-element sums in the quadratic field.
This is the physical target consumed by the later exact Sigma certificate.
-/

namespace OntologySeparation.ForcedSignalingLC4

abbrev Q2 := ℚ × ℚ

def qrat (r : ℚ) : Q2 := (r,0)
def qsqrt2 : Q2 := (0,1)
def q (a b : ℚ) : Q2 := (a,b)

/-- Multiplication in Q(sqrt 2): (a+b√2)(c+d√2). -/
def qmul (x y : Q2) : Q2 :=
  (x.1*y.1 + 2*x.2*y.2, x.1*y.2 + x.2*y.1)

@[simp] theorem qrat_zero : qrat 0 = 0 := rfl

noncomputable def Q2.toReal (x : Q2) : ℝ :=
  (x.1 : ℝ) + (x.2 : ℝ) * Real.sqrt 2

@[simp] theorem toReal_zero : Q2.toReal 0 = 0 := by simp [Q2.toReal]
@[simp] theorem toReal_qrat (r : ℚ) : Q2.toReal (qrat r) = (r : ℝ) := by
  simp [Q2.toReal, qrat]
@[simp] theorem toReal_add (x y : Q2) :
    Q2.toReal (x+y) = Q2.toReal x + Q2.toReal y := by
  simp [Q2.toReal]
  ring

theorem toReal_qmul (x y : Q2) :
    Q2.toReal (qmul x y) = Q2.toReal x * Q2.toReal y := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Q2.toReal, qmul, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  ring_nf
  rw [hs]

theorem toReal_sum_finset {α : Type} (s : Finset α) (f : α → Q2) :
    Q2.toReal (∑ i ∈ s, f i) = ∑ i ∈ s, Q2.toReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Q2.toReal]
  | @insert a s ha ih =>
      simp [ha, toReal_add, ih]

theorem toReal_sum {α : Type} [Fintype α] (f : α → Q2) :
    Q2.toReal (∑ i, f i) = ∑ i, Q2.toReal (f i) := by
  simpa using toReal_sum_finset (Finset.univ : Finset α) f

abbrev Basis4 := Bool × Bool × Bool × Bool

def bitA (i : Basis4) : Bool := i.1
def bitB (i : Basis4) : Bool := i.2.1
def bitC (i : Basis4) : Bool := i.2.2.1
def bitD (i : Basis4) : Bool := i.2.2.2

def bnat (b : Bool) : ℕ := if b then 1 else 0

def clusterParity (i : Basis4) : ℕ :=
  (bnat (bitA i && bitB i) +
   bnat (bitB i && bitC i) +
   bnat (bitC i && bitD i)) % 2

def clusterAmp (i : Basis4) : Q2 :=
  qrat (if clusterParity i = 0 then (1:ℚ)/4 else -1/4)

set_option maxRecDepth 100000 in
theorem cluster_normalized :
    ∑ i : Basis4, qmul (clusterAmp i) (clusterAmp i) = qrat 1 := by
  norm_num [clusterAmp, clusterParity, bnat, bitA, bitB, bitC, bitD,
    qmul, qrat, Fintype.sum_prod_type, Fintype.sum_bool]

def outSign (o : Bool) : ℚ := if o then -1 else 1

def zEffect (o i j : Bool) : Q2 :=
  if i = j ∧ i = o then qrat 1 else 0

def xEffect (o i j : Bool) : Q2 :=
  if i = j then qrat (1/2)
  else qrat (outSign o / 2)

def bEffect (setting outcome i j : Bool) : Q2 :=
  let s := outSign outcome
  let t : ℚ := if setting then -1 else 1
  if i = j then
    if i then q (1/2) (-s/4) else q (1/2) (s/4)
  else
    q 0 (s*t/4)

def aEffect (setting outcome i j : Bool) : Q2 :=
  if setting then zEffect outcome i j else xEffect outcome i j

def cEffect (setting outcome i j : Bool) : Q2 :=
  if setting then xEffect outcome i j else zEffect outcome i j

def dEffect (setting outcome i j : Bool) : Q2 :=
  if setting then zEffect outcome i j else xEffect outcome i j

def fullProb
    (x y z w a b c d : Bool) : Q2 :=
  ∑ i : Basis4, ∑ j : Basis4,
    qmul (qmul (qmul (qmul
      (qmul (clusterAmp i) (clusterAmp j))
      (aEffect x a (bitA i) (bitA j)))
      (bEffect y b (bitB i) (bitB j)))
      (cEffect z c (bitC i) (bitC j)))
      (dEffect w d (bitD i) (bitD j))

def abd (x y w a b d : Bool) : Q2 :=
  fullProb x y false w a b false d +
  fullProb x y false w a b true d

def acd (x z w a c d : Bool) : Q2 :=
  fullProb x false z w a false c d +
  fullProb x false z w a true c d

/-- The two no-blind-pair marginal families used by the Sigma program are
ABD at z=0 and ACD at y=0. -/

def corr2 (x y z w : Bool) (pa pb : Bool) : Q2 :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
    qmul (qrat (outSign (if pa then a else c) * outSign (if pb then b else d)))
      (fullProb x y z w a b c d)

def corrABD (x y z w : Bool) : Q2 :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
    qmul (qrat (outSign a * outSign b * outSign d)) (fullProb x y z w a b c d)

def corrACD (x y z w : Bool) : Q2 :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
    qmul (qrat (outSign a * outSign c * outSign d)) (fullProb x y z w a b c d)

def score : Q2 :=
  corr2 false false false true true true +
  corr2 false true false true true true +
  corrABD true false false false -
  corrABD true true false false +
  qmul (qrat 2) (corr2 true false false false false false) +
  qmul (qrat 2) (corrACD false false true true)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Separate correlators keep the kernel computations small and reusable.
private theorem ab0_exact : corr2 false false false true true true = q 0 (1/2) := by
  decide +kernel
private theorem ab1_exact : corr2 false true false true true true = q 0 (1/2) := by
  decide +kernel
private theorem abd0_exact : corrABD true false false false = q 0 (1/2) := by
  decide +kernel
private theorem abd1_exact : corrABD true true false false = q 0 (-1/2) := by
  decide +kernel
private theorem cd_exact : corr2 true false false false false false = qrat 1 := by
  decide +kernel
private theorem acd_exact : corrACD false false true true = qrat 1 := by
  decide +kernel

/-- Exact LC4 value S4 = 4 + 2 sqrt(2), derived from the state/projectors. -/
theorem score_exact : score = q 4 2 := by
  rw [score, ab0_exact, ab1_exact, abd0_exact, abd1_exact, cd_exact, acd_exact]
  norm_num [qmul, qrat, q]

theorem score_exact_real :
    Q2.toReal score = 4 + 2 * Real.sqrt 2 := by
  rw [score_exact]
  simp [Q2.toReal, q]

end OntologySeparation.ForcedSignalingLC4
