import OntologySeparation.Recipes.Qubit
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-! Exact real two-qubit states. Rational vectors are rays, not assumed normalized.
Every pure readout is the Born rule for a normalized real amplitude; mixtures are
convex combinations. No floating point arithmetic enters the proof. -/
namespace OntologySeparation.TwoQubit

@[ext] structure Amplitudes where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq

def Amplitudes.normSq (v : Amplitudes) : ℚ := v.a^2 + v.b^2 + v.c^2 + v.d^2
@[ext] structure Pure where
  vector : Amplitudes
  positive : 0 < vector.normSq

def Pure.of (a b c d : ℚ) (valid : 0 < Amplitudes.normSq ⟨a,b,c,d⟩ := by norm_num [Amplitudes.normSq]) : Pure :=
  ⟨⟨a,b,c,d⟩, valid⟩
inductive Wire where
  | alice | bob
  deriving DecidableEq

/-- A real orthogonal basis, specified by a nonzero rational direction.
Its columns are (c,s) and (-s,c), divided by sqrt(c²+s²). -/
structure Basis where
  c : ℚ
  s : ℚ
  positive : 0 < c^2 + s^2

def Basis.of (c s : ℚ) (valid : 0 < c^2+s^2 := by norm_num) : Basis := ⟨c,s,valid⟩
def Basis.z : Basis := .of 1 0
def Basis.x : Basis := .of 1 1

/-- H is represented without its common 1/sqrt(2) factor; ray normalization
restores it. Rotations below likewise omit only a common normalization factor. -/
inductive Gate where
  | h (wire : Wire) | x (wire : Wire) | z (wire : Wire)
  | cnot (control : Wire) | swap
  | readBasis (wire : Wire) (basis : Basis)

def Gate.apply (g : Gate) (v : Amplitudes) : Amplitudes :=
  match g with
  | .h .alice => ⟨v.a+v.c, v.b+v.d, v.a-v.c, v.b-v.d⟩
  | .h .bob => ⟨v.a+v.b, v.a-v.b, v.c+v.d, v.c-v.d⟩
  | .x .alice => ⟨v.c,v.d,v.a,v.b⟩
  | .x .bob => ⟨v.b,v.a,v.d,v.c⟩
  | .z .alice => ⟨v.a,v.b,-v.c,-v.d⟩
  | .z .bob => ⟨v.a,-v.b,v.c,-v.d⟩
  | .cnot .alice => ⟨v.a,v.b,v.d,v.c⟩
  | .cnot .bob => ⟨v.a,v.d,v.c,v.b⟩
  | .swap => ⟨v.a,v.c,v.b,v.d⟩
  | .readBasis .alice q => ⟨q.c*v.a+q.s*v.c, q.c*v.b+q.s*v.d,
      -q.s*v.a+q.c*v.c, -q.s*v.b+q.c*v.d⟩
  | .readBasis .bob q => ⟨q.c*v.a+q.s*v.b, -q.s*v.a+q.c*v.b,
      q.c*v.c+q.s*v.d, -q.s*v.c+q.c*v.d⟩

def Gate.scale : Gate → ℚ
  | .h _ => 2
  | .readBasis _ q => q.c^2+q.s^2
  | _ => 1

theorem Gate.normSq (g : Gate) (v : Amplitudes) :
    (g.apply v).normSq = g.scale * v.normSq := by
  cases g with
  | h w => cases w <;> simp [apply, scale, Amplitudes.normSq] <;> ring
  | x w => cases w <;> simp [apply, scale, Amplitudes.normSq] <;> ring
  | z w => cases w <;> simp [apply, scale, Amplitudes.normSq]
  | cnot w => cases w <;> simp [apply, scale, Amplitudes.normSq] <;> ring
  | swap => simp [apply, scale, Amplitudes.normSq]; ring
  | readBasis w q => cases w <;> simp [apply, scale, Amplitudes.normSq] <;> ring

theorem Gate.scale_pos (g : Gate) : 0 < g.scale := by
  cases g <;> simp [scale]
  exact Basis.positive _

def Pure.gate (v : Pure) (g : Gate) : Pure :=
  ⟨g.apply v.vector, by rw [g.normSq]; exact mul_pos g.scale_pos v.positive⟩

def Amplitudes.entry (v : Amplitudes) (o : Bool × Bool) : ℚ :=
  match o with
  | (false,false) => v.a | (false,true) => v.b
  | (true,false) => v.c | (true,true) => v.d

def Pure.probability (v : Pure) (o : Bool × Bool) : ℚ :=
  (v.vector.entry o)^2 / v.vector.normSq

theorem Pure.nonneg (v : Pure) (o : Bool × Bool) : 0 ≤ v.probability o :=
  div_nonneg (sq_nonneg _) (le_of_lt v.positive)
theorem Pure.normalized (v : Pure) : ∑ o : Bool × Bool, v.probability o = 1 := by
  simp [probability, Amplitudes.entry, Fintype.sum_prod_type]
  rw [← add_div, ← add_div, ← add_div]
  convert div_self (ne_of_gt v.positive) using 1
  simp [Amplitudes.normSq]
  ring

/-- Normalized real amplitude in the computational basis. -/
noncomputable def Pure.amplitude (v : Pure) (o : Bool × Bool) : ℝ :=
  (v.vector.entry o : ℝ) / Real.sqrt (v.vector.normSq : ℝ)

theorem Pure.born (v : Pure) (o : Bool × Bool) :
    (v.probability o : ℝ) = v.amplitude o ^ 2 := by
  have h : (0 : ℝ) ≤ (v.vector.normSq : ℝ) := by exact_mod_cast le_of_lt v.positive
  simp [probability, amplitude, div_pow, Real.sq_sqrt h]

theorem Pure.amplitude_normalized (v : Pure) : ∑ o : Bool × Bool, v.amplitude o ^ 2 = 1 := by
  simp_rw [← v.born]
  have h := v.normalized
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, Rat.cast_add, Rat.cast_one] using congrArg (fun q : ℚ => (q : ℝ)) h

/-- Measuring Bob in another basis cannot change Alice's marginal. -/
theorem Pure.alice_marginal (v : Pure) (q : Basis) (a : Bool) :
    ∑ b : Bool, (v.gate (.readBasis .bob q)).probability (a,b) =
      ∑ b : Bool, v.probability (a,b) := by
  have hn := ne_of_gt v.positive
  have hq := ne_of_gt q.positive
  cases a <;> simp only [Fintype.sum_bool, probability, gate, Gate.normSq, Gate.scale]
    <;> simp only [Gate.apply, Amplitudes.entry]
    <;> field_simp <;> ring

/-- Measuring Alice in another basis cannot change Bob's marginal. -/
theorem Pure.bob_marginal (v : Pure) (q : Basis) (b : Bool) :
    ∑ a : Bool, (v.gate (.readBasis .alice q)).probability (a,b) =
      ∑ a : Bool, v.probability (a,b) := by
  have hn := ne_of_gt v.positive
  have hq := ne_of_gt q.positive
  cases b <;> simp only [Fintype.sum_bool, probability, gate, Gate.normSq, Gate.scale]
    <;> simp only [Gate.apply, Amplitudes.entry]
    <;> field_simp <;> ring

theorem Pure.read_commute (v : Pure) (a b : Basis) :
    (v.gate (.readBasis .alice a)).gate (.readBasis .bob b) =
      (v.gate (.readBasis .bob b)).gate (.readBasis .alice a) := by
  ext <;> simp [gate, Gate.apply] <;> ring

/-- A finite convex ensemble. Mixture weights are validated Rates. -/
inductive State where
  | pure (v : Pure)
  | mix (weight : Recipes.Rate) (left right : State)

def State.probability : State → (Bool × Bool) → ℚ
  | .pure v, o => v.probability o
  | .mix p l r, o => p.value * l.probability o + (1-p.value)*r.probability o

theorem State.nonneg (v : State) (o : Bool × Bool) : 0 ≤ v.probability o := by
  induction v with
  | pure v => exact v.nonneg o
  | mix p l r hl hr => exact add_nonneg (mul_nonneg p.nonneg hl) (mul_nonneg (sub_nonneg.mpr p.le_one) hr)

theorem State.normalized (v : State) : ∑ o : Bool × Bool, v.probability o = 1 := by
  induction v with
  | pure v => exact v.normalized
  | mix p l r hl hr =>
    simp only [probability, Finset.sum_add_distrib, ← Finset.mul_sum, hl, hr]
    ring

def State.gate : State → Gate → State
  | .pure v, g => .pure (v.gate g)
  | .mix p l r, g => .mix p (l.gate g) (r.gate g)

theorem State.alice_marginal (v : State) (q : Basis) (a : Bool) :
    ∑ b : Bool, (v.gate (.readBasis .bob q)).probability (a,b) =
      ∑ b : Bool, v.probability (a,b) := by
  induction v with
  | pure v => exact v.alice_marginal q a
  | mix p l r hl hr =>
    simp only [gate, probability, Finset.sum_add_distrib, ← Finset.mul_sum, hl, hr]

theorem State.bob_marginal (v : State) (q : Basis) (b : Bool) :
    ∑ a : Bool, (v.gate (.readBasis .alice q)).probability (a,b) =
      ∑ a : Bool, v.probability (a,b) := by
  induction v with
  | pure v => exact v.bob_marginal q b
  | mix p l r hl hr =>
    simp only [gate, probability, Finset.sum_add_distrib, ← Finset.mul_sum, hl, hr]

theorem State.read_commute (v : State) (a b : Basis) :
    (v.gate (.readBasis .alice a)).gate (.readBasis .bob b) =
      (v.gate (.readBasis .bob b)).gate (.readBasis .alice a) := by
  induction v with
  | pure v => simp only [gate, v.read_commute a b]
  | mix p l r hl hr => simp only [gate, hl, hr]

/-- p=1 means full dephasing. A Z flip occurs with probability p/2. -/
def State.dephase (v : State) (w : Wire) (p : Recipes.Rate) : State :=
  .mix ⟨p.value/2, by exact div_nonneg p.nonneg (by norm_num), by linarith [p.le_one]⟩ (v.gate (.z w)) v

noncomputable def State.behavior (v : State) : Behavior { Setting := Unit, Outcome := Bool × Bool } where
  prob _ o := (v.probability o : ℝ)
  nonneg _ o := by exact_mod_cast v.nonneg o
  normalized _ := by
    have h := v.normalized
    simpa only [Fintype.sum_prod_type, Fintype.sum_bool, Rat.cast_add, Rat.cast_one] using congrArg (fun q : ℚ => (q : ℝ)) h

end OntologySeparation.TwoQubit
