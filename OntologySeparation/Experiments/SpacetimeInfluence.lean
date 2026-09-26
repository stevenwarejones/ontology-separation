import OntologySeparation.Core.Channels
import OntologySeparation.Core.ExperimentAccess
import Mathlib.Tactic.FinCases

/-! A finite causal channel calculation. Relativistic localization and experimental
randomization are separate physical premises; no continuum field theory is assumed. -/
namespace OntologySeparation.SpacetimeInfluence
noncomputable section

abbrev interface (O : Type) [Fintype O] : Interface :=
  { Setting := Bool, Outcome := O }

/-- Complete receiver outcomes, before any sender-dependent selection. -/
def influence {O : Type} [Fintype O] (p : Behavior (interface O)) : ℝ :=
  (∑ b, |p.prob true b - p.prob false b|) / 2

/-- Shared preparation, an arbitrary sender channel, and a receiver channel that
has no setting input. Shared causes can correlate both outputs. -/
structure Model (Λ A B : Type) [Fintype Λ] [Fintype A] [Fintype B] where
  preparation : FiniteDistribution Λ
  sender : Bool → Channel Λ A
  receiver : Channel Λ B

namespace Model
variable {Λ A B : Type} [Fintype Λ] [Fintype A] [Fintype B]

def joint (m : Model Λ A B) : Behavior (interface (A × B)) where
  prob x ab := ∑ l, m.preparation.mass l *
    ((m.sender x l).mass ab.1 * (m.receiver l).mass ab.2)
  nonneg x ab := Finset.sum_nonneg fun l _ => mul_nonneg
    (m.preparation.nonneg l) (mul_nonneg ((m.sender x l).nonneg ab.1)
      ((m.receiver l).nonneg ab.2))
  normalized x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Fintype.sum_prod_type,
      ← Finset.mul_sum, FiniteDistribution.total, mul_one,
      FiniteDistribution.total, mul_one]
    exact m.preparation.total

/-- Summing the normalized sender channel removes the intervention. -/
theorem marginal_formula (m : Model Λ A B) (x : Bool) (b : B) :
    (∑ a, m.joint.prob x (a,b)) =
      ∑ l, m.preparation.mass l * (m.receiver l).mass b := by
  simp only [joint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.mul_sum, ← Finset.sum_mul, FiniteDistribution.total, one_mul]

def observed (m : Model Λ A B) : Behavior (interface B) where
  prob x b := ∑ a, m.joint.prob x (a,b)
  nonneg x b := Finset.sum_nonneg fun a _ => m.joint.nonneg x (a,b)
  normalized x := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact m.joint.normalized x

theorem no_influence (m : Model Λ A B) : influence m.observed = 0 := by
  simp [influence, observed, marginal_formula]

theorem marginal_independent (m : Model Λ A B) (x y : Bool) (b : B) :
    m.observed.prob x b = m.observed.prob y b := by
  simp [observed, marginal_formula]
end Model

/-- With two complete outcomes TV is exactly the selected-outcome gap. -/
theorem binary_influence (p : Behavior (interface Bool)) :
    influence p = |p.prob true true - p.prob false true| := by
  have h0 := p.normalized false
  have h1 := p.normalized true
  simp only [Fintype.sum_bool] at h0 h1
  have h : p.prob true false - p.prob false false =
      -(p.prob true true - p.prob false true) := by linarith
  simp only [influence, Fintype.sum_bool, h, abs_neg]
  ring

def bernoulli (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : FiniteDistribution Bool :=
  ⟨(coin r h0 h1).prob (), (coin r h0 h1).nonneg (), (coin r h0 h1).normalized ()⟩

/-- A normalized operational alternative, not a relativistic dynamical theory. -/
def alternative (g : ℝ) (h0 : 0 ≤ g) (h1 : g ≤ 1) : Behavior (interface Bool) where
  prob x b := (coin (if x then (1+g)/2 else (1-g)/2)
    (by cases x <;> simp <;> linarith) (by cases x <;> simp <;> linarith)).prob () b
  nonneg x b := by cases x <;> cases b <;> simp [coin] <;> linarith
  normalized x := by cases x <;> simp [coin]

theorem alternative_gap (g : ℝ) (h0 : 0 ≤ g) (h1 : g ≤ 1) :
    influence (alternative g h0 h1) = g := by
  rw [binary_influence]
  have h : (alternative g h0 h1).prob true true -
      (alternative g h0 h1).prob false true = g := by simp [alternative, coin]; ring
  rw [h, abs_of_nonneg h0]

theorem alternative_excluded (g : ℝ) (h0 : 0 < g) (h1 : g ≤ 1)
    {Λ A : Type} [Fintype Λ] [Fintype A] (m : Model Λ A Bool) :
    ¬ ObservationallyEquivalent m.observed (alternative g h0.le h1) := by
  intro h
  have hn := m.no_influence
  have he : influence m.observed = influence (alternative g h0.le h1) := by
    simp only [influence, h true, h false]
  rw [he, alternative_gap] at hn
  linarith

/-- Explicit shared-bit model: perfect correlation does not imply signaling. -/
def sharedBit : Model Bool Bool Bool where
  preparation := bernoulli (1/2) (by norm_num) (by norm_num)
  sender _ := Channel.deterministic id
  receiver := Channel.deterministic id

theorem sharedBit_correlated :
    sharedBit.joint.prob false (true,true) = 1/2 ∧
    sharedBit.joint.prob false (true,false) = 0 ∧
    sharedBit.observed.prob false true = 1/2 ∧ influence sharedBit.observed = 0 := by
  constructor
  · norm_num [sharedBit, Model.joint, bernoulli, coin, Channel.deterministic,
      Fintype.sum_bool]
  constructor
  · norm_num [sharedBit, Model.joint, bernoulli, coin, Channel.deterministic,
      Fintype.sum_bool]
  constructor
  · simp only [Model.observed, Model.marginal_formula]
    norm_num [sharedBit, bernoulli, coin,
      Channel.deterministic, Fintype.sum_bool]
  · exact sharedBit.no_influence

/-- Complete receiver-only access cannot reveal whether a hidden bit is copied
at the sender. This is an equivalence of these two finite models only. -/
def uncorrelatedBit : Model Bool Bool Bool :=
  { sharedBit with sender := fun _ _ => bernoulli (1/2) (by norm_num) (by norm_num) }

def receiverPredictions (hiddenCopy : Bool) (_ : Unit) : Behavior (interface Bool) :=
  if hiddenCopy then sharedBit.observed else uncorrelatedBit.observed

theorem receiver_access_equivalent :
    ExperimentAccess.Equivalent receiverPredictions (fun _ => True) true false := by
  intro p hp x b
  simp only [receiverPredictions, if_true, Bool.false_eq_true, if_false,
    Model.observed, Model.marginal_formula]
  rfl

/-- Independent fair bits r,y; retain exactly r=y. Selection success is 1/2,
but the retained r equals y with certainty. The unconditional r stays fair. -/
def fairPair : FiniteDistribution (Bool × Bool) where
  mass _ := 1/4
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem postselection_counterexample :
    (∑ r : Bool, fairPair.mass (r,false)) = 1/2 ∧
    (∑ r : Bool, fairPair.mass (r,true)) = 1/2 ∧
    fairPair.mass (true,false) / (∑ r : Bool, fairPair.mass (r,false)) = 1/2 ∧
    fairPair.mass (true,true) / (∑ r : Bool, fairPair.mass (r,true)) = 1/2 ∧
    fairPair.mass (true,true) / (∑ r : Bool, if r = true then fairPair.mass (r,true) else 0) = 1 ∧
    (0 : ℝ) / (∑ r : Bool, if r = false then fairPair.mass (r,false) else 0) = 0 := by
  norm_num [fairPair, Fintype.sum_bool]

/-- Removing preparation independence permits b=x with a fixed identity readout. -/
def dependentPreparation : Behavior (interface Bool) :=
  Channel.behavior (Channel.deterministic id) (Channel.deterministic id)

theorem dependentPreparation_gap : influence dependentPreparation = 1 := by
  rw [binary_influence]
  norm_num [dependentPreparation, Channel.behavior, Channel.andThen,
    Channel.deterministic, Fintype.sum_bool]

end
end OntologySeparation.SpacetimeInfluence
