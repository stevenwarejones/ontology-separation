import OntologySeparation.Core.Operational
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bong et al. (2020), Eq. (13), in the conditional no-signaling formulation
(Eqs. 3–6). The friends' outputs are fixed within a component; other outputs
are NOT jointly predetermined. Index 0 denotes asking the friend.
Reference: https://arxiv.org/abs/1907.05607v4 -/

namespace OntologySeparation.LF

noncomputable section

/-- Binary outcome sign: false = +1, true = -1. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

/-- A conditional two-setting no-signaling behavior in moment coordinates.
Positivity of its 16 outcome probabilities is the only inner-box constraint. -/
structure Component where
  charlie : Bool
  debbie : Bool
  alice : Fin 2 → ℝ
  bob : Fin 2 → ℝ
  corr : Fin 2 → Fin 2 → ℝ
  positive : ∀ x y s t,
    0 ≤ 1 + sign s * alice x + sign t * bob y + sign s * sign t * corr x y

/-- Genuine LF facet 1, before subtracting its bound of six. -/
def componentScore (q : Component) : ℝ :=
  -sign q.charlie - q.alice 0 - sign q.debbie - q.bob 0
  - sign q.charlie * sign q.debbie
  - 2 * sign q.charlie * q.bob 0 - 2 * q.alice 0 * sign q.debbie
  + 2 * q.corr 0 0 - q.corr 0 1 - q.corr 1 0 - q.corr 1 1

/-- Eq. (13) follows from conditional positivity, with no outcome-independence axiom. -/
theorem componentScore_le_six (q : Component) : componentScore q ≤ 6 := by
  have h0000 := q.positive 0 0 false false
  have h0001 := q.positive 0 0 false true
  have h0010 := q.positive 0 0 true false
  have h0011 := q.positive 0 0 true true
  have h0100 := q.positive 0 1 false false
  have h0101 := q.positive 0 1 false true
  have h0110 := q.positive 0 1 true false
  have h0111 := q.positive 0 1 true true
  have h1000 := q.positive 1 0 false false
  have h1001 := q.positive 1 0 false true
  have h1010 := q.positive 1 0 true false
  have h1011 := q.positive 1 0 true true
  have h1100 := q.positive 1 1 false false
  have h1101 := q.positive 1 1 false true
  have h1110 := q.positive 1 1 true false
  have h1111 := q.positive 1 1 true true
  simp only [sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, mul_one,
    mul_neg, neg_neg] at *
  unfold componentScore
  cases hc : q.charlie <;> cases hd : q.debbie <;>
    simp [sign] <;> linarith

/-- Extend the inner box by inserting the actual friend outputs at setting zero. -/
def Component.a (q : Component) (x : Fin 3) : ℝ :=
  if h : x.val = 0 then sign q.charlie else q.alice ⟨x.val - 1, by omega⟩

def Component.b (q : Component) (y : Fin 3) : ℝ :=
  if h : y.val = 0 then sign q.debbie else q.bob ⟨y.val - 1, by omega⟩

def Component.e (q : Component) (x y : Fin 3) : ℝ :=
  if hx : x.val = 0 then sign q.charlie * q.b y
  else if hy : y.val = 0 then q.a x * sign q.debbie
  else q.corr ⟨x.val - 1, by omega⟩ ⟨y.val - 1, by omega⟩

/-- A mixture has one setting-independent distribution over conditional components.
This is the no-superdeterminism part of the model. -/
structure Model (ι : Type) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  normalized : ∑ i, weight i = 1
  component : ι → Component

def Model.score {ι : Type} [Fintype ι] (m : Model ι) : ℝ :=
  ∑ i, m.weight i * componentScore (m.component i)

/-- Genuine LF bound for arbitrary finite mixtures of conditional NS boxes. -/
theorem Model.score_le_six {ι : Type} [Fintype ι] (m : Model ι) : m.score ≤ 6 := by
  calc
    m.score ≤ ∑ i, m.weight i * 6 :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (componentScore_le_six (m.component i)) (m.nonneg i)
    _ = 6 := by rw [← Finset.sum_mul, m.normalized]; norm_num

/-- A PR inner box is allowed by LF although its non-friend CHSH value is four. -/
def prComponent : Component where
  charlie := false
  debbie := false
  alice := fun _ => 0
  bob := fun _ => 0
  corr := fun x y => if x = 1 ∧ y = 1 then -1 else 1
  positive := by
    intro x y s t
    fin_cases x <;> fin_cases y <;> cases s <;> cases t <;> norm_num [sign]

def innerCHSH (q : Component) : ℝ :=
  q.corr 0 0 + q.corr 0 1 + q.corr 1 0 - q.corr 1 1

theorem prComponent_innerCHSH : innerCHSH prComponent = 4 := by
  norm_num [innerCHSH, prComponent]

theorem prComponent_genuineLF : componentScore prComponent ≤ 6 :=
  componentScore_le_six prComponent

/-- Witness that a Bell violation on non-friend settings does not exclude LF. -/
theorem exists_bell_violation_within_LF :
    ∃ q : Component, 2 < innerCHSH q ∧ componentScore q ≤ 6 := by
  refine ⟨prComponent, ?_, prComponent_genuineLF⟩
  rw [prComponent_innerCHSH]
  norm_num

/-- Both marginal expectations lie in [-1,1], derived from inner-box positivity. -/
theorem Component.alice_bounds (q : Component) (x : Fin 2) :
    -1 ≤ q.alice x ∧ q.alice x ≤ 1 := by
  have h1 := q.positive x 0 false false
  have h2 := q.positive x 0 false true
  have h3 := q.positive x 0 true false
  have h4 := q.positive x 0 true true
  simp [sign] at *
  constructor <;> linarith

theorem Component.bob_bounds (q : Component) (y : Fin 2) :
    -1 ≤ q.bob y ∧ q.bob y ≤ 1 := by
  have h1 := q.positive 0 y false false
  have h2 := q.positive 0 y false true
  have h3 := q.positive 0 y true false
  have h4 := q.positive 0 y true true
  simp [sign] at *
  constructor <;> linarith

abbrev interface : Interface := { Setting := Fin 3 × Fin 3, Outcome := Bool × Bool }

def Component.prob (q : Component) (xy : Fin 3 × Fin 3) (st : Bool × Bool) : ℝ :=
  (1 + sign st.1 * q.a xy.1 + sign st.2 * q.b xy.2
    + sign st.1 * sign st.2 * q.e xy.1 xy.2) / 4

theorem signed_nonneg {v : ℝ} (hv : -1 ≤ v ∧ v ≤ 1) (s : Bool) :
    0 ≤ 1 + sign s * v := by
  cases s <;> simp [sign] <;> linarith [hv.1, hv.2]

theorem Component.a_bounds (q : Component) (x : Fin 3) : -1 ≤ q.a x ∧ q.a x ≤ 1 := by
  by_cases hx : x.val = 0
  · cases hc : q.charlie <;> simp [Component.a, hx, sign, hc]
  · simpa [Component.a, hx] using q.alice_bounds ⟨x.val - 1, by omega⟩

theorem Component.b_bounds (q : Component) (y : Fin 3) : -1 ≤ q.b y ∧ q.b y ≤ 1 := by
  by_cases hy : y.val = 0
  · cases hd : q.debbie <;> simp [Component.b, hy, sign, hd]
  · simpa [Component.b, hy] using q.bob_bounds ⟨y.val - 1, by omega⟩

theorem Component.prob_nonneg (q : Component) (xy : Fin 3 × Fin 3)
    (st : Bool × Bool) : 0 ≤ q.prob xy st := by
  obtain ⟨x,y⟩ := xy
  obtain ⟨s,t⟩ := st
  by_cases hx : x.val = 0
  · have hc : -1 ≤ sign q.charlie ∧ sign q.charlie ≤ 1 := by
      cases q.charlie <;> norm_num [sign]
    calc
      0 ≤ ((1 + sign s * sign q.charlie) * (1 + sign t * q.b y)) / 4 :=
        div_nonneg (mul_nonneg (signed_nonneg hc s) (signed_nonneg (q.b_bounds y) t))
          (by norm_num)
      _ = q.prob (x,y) (s,t) := by
        simp [Component.prob, Component.a, Component.e, hx]
        ring
  · by_cases hy : y.val = 0
    · have hd : -1 ≤ sign q.debbie ∧ sign q.debbie ≤ 1 := by
        cases q.debbie <;> norm_num [sign]
      calc
        0 ≤ ((1 + sign s * q.a x) * (1 + sign t * sign q.debbie)) / 4 :=
          div_nonneg (mul_nonneg (signed_nonneg (q.a_bounds x) s) (signed_nonneg hd t))
            (by norm_num)
        _ = q.prob (x,y) (s,t) := by
          simp [Component.prob, Component.b, Component.e, hx, hy]
          ring
    · simp only [Component.prob, Component.a, Component.b, Component.e, hx, hy,
        ↓reduceDIte]
      exact div_nonneg (q.positive _ _ s t) (by norm_num)

def Component.behavior (q : Component) : Behavior interface where
  prob := q.prob
  nonneg := q.prob_nonneg
  normalized xy := by
    simp [Component.prob, Fintype.sum_prod_type, sign]
    ring

/-- The conditional distribution has setting-independent local marginals. -/
theorem Component.marginal_alice (q : Component) (x y : Fin 3) (s : Bool) :
    ∑ t : Bool, q.prob (x,y) (s,t) = (1 + sign s * q.a x) / 2 := by
  cases s <;> simp [Component.prob, sign] <;> ring

theorem Component.marginal_bob (q : Component) (x y : Fin 3) (t : Bool) :
    ∑ s : Bool, q.prob (x,y) (s,t) = (1 + sign t * q.b y) / 2 := by
  cases t <;> simp [Component.prob, sign] <;> ring

/-- Asking Charlie reads his actual component record with certainty. -/
theorem Component.read_charlie (q : Component) (y : Fin 3) :
    ∑ t : Bool, q.prob (0,y) (q.charlie,t) = 1 := by
  rw [q.marginal_alice]
  cases hc : q.charlie <;> norm_num [Component.a, sign, hc]

theorem Component.read_debbie (q : Component) (x : Fin 3) :
    ∑ s : Bool, q.prob (x,0) (s,q.debbie) = 1 := by
  rw [q.marginal_bob]
  cases hd : q.debbie <;> norm_num [Component.b, sign, hd]

def Model.behavior {ι : Type} [Fintype ι] (m : Model ι) : Behavior interface where
  prob xy st := ∑ i, m.weight i * (m.component i).prob xy st
  nonneg xy st := Finset.sum_nonneg fun i _ =>
    mul_nonneg (m.nonneg i) ((m.component i).prob_nonneg xy st)
  normalized xy := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [show ∀ i, ∑ st, (m.component i).prob xy st = 1 from
      fun i => (m.component i).behavior.normalized xy, mul_one]
    exact m.normalized

/-- Operational image of all finite LF conditional-box models. -/
def theory : Theory interface := fun p =>
  ∃ (ι : Type) (_ : Fintype ι) (m : Model ι), m.behavior = p

end
end OntologySeparation.LF
