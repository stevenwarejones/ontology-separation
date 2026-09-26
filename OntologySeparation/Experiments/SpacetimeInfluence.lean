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

/-- Relax only preparation independence. Sender channels remain normalized and
receiver has no setting input; all sender outcomes are still summed. -/
structure PreparationDependentModel (Λ A B : Type)
    [Fintype Λ] [Fintype A] [Fintype B] where
  preparation : Bool → FiniteDistribution Λ
  sender : Bool → Channel Λ A
  receiver : Channel Λ B

namespace PreparationDependentModel
variable {Λ A B : Type} [Fintype Λ] [Fintype A] [Fintype B]
def atSetting (m : PreparationDependentModel Λ A B) (x : Bool) : Model Λ A B :=
  ⟨m.preparation x, m.sender, m.receiver⟩
def observed (m : PreparationDependentModel Λ A B) : Behavior (interface B) where
  prob x := (m.atSetting x).observed.prob x
  nonneg x := (m.atSetting x).observed.nonneg x
  normalized x := (m.atSetting x).observed.normalized x
end PreparationDependentModel

/-- Relax only the absence of a setting input at the receiver. Preparation is
shared, sender channels normalized, and sampling complete. -/
structure ReceiverDependentModel (Λ A B : Type)
    [Fintype Λ] [Fintype A] [Fintype B] where
  preparation : FiniteDistribution Λ
  sender : Bool → Channel Λ A
  receiver : Bool → Channel Λ B

namespace ReceiverDependentModel
variable {Λ A B : Type} [Fintype Λ] [Fintype A] [Fintype B]
def atSetting (m : ReceiverDependentModel Λ A B) (x : Bool) : Model Λ A B :=
  ⟨m.preparation, m.sender, m.receiver x⟩
def observed (m : ReceiverDependentModel Λ A B) : Behavior (interface B) where
  prob x := (m.atSetting x).observed.prob x
  nonneg x := (m.atSetting x).observed.nonneg x
  normalized x := (m.atSetting x).observed.normalized x
end ReceiverDependentModel

/-- Remove only complete sampling: condition an unchanged causal model on a
sender-side acceptance event. The positive denominator is an explicit premise. -/
structure SelectedModel (Λ A B : Type) [Fintype Λ] [Fintype A] [Fintype B] where
  underlying : Model Λ A B
  keep : Bool → A → Bool

namespace SelectedModel
variable {Λ A B : Type} [Fintype Λ] [Fintype A] [Fintype B]
def weight (m : SelectedModel Λ A B) (x : Bool) (b : B) : ℝ :=
  ∑ a, if m.keep x a then m.underlying.joint.prob x (a,b) else 0
def acceptance (m : SelectedModel Λ A B) (x : Bool) : ℝ := ∑ b, m.weight x b

def observed (m : SelectedModel Λ A B) (h : ∀ x, 0 < m.acceptance x) :
    Behavior (interface B) where
  prob x b := m.weight x b / m.acceptance x
  nonneg x b := div_nonneg (Finset.sum_nonneg fun a _ => by
    split
    · exact m.underlying.joint.nonneg x (a,b)
    · exact le_rfl) (h x).le
  normalized x := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt (h x))
end SelectedModel

/-- Deterministic setting-dependent preparation, with the original fixed sender
and receiver readouts. Only the preparation field gains a setting argument. -/
def dependentPreparation : PreparationDependentModel Bool Bool Bool where
  preparation := Channel.deterministic id
  sender := sharedBit.sender
  receiver := sharedBit.receiver

theorem dependentPreparation_gap : influence dependentPreparation.observed = 1 := by
  rw [binary_influence]
  norm_num [PreparationDependentModel.observed, PreparationDependentModel.atSetting,
    Model.observed, Model.joint, dependentPreparation, sharedBit,
    Channel.deterministic, Fintype.sum_bool]

/-- Same fair source and normalized sender, but a direct setting-reading receiver. -/
def dependentReceiver : ReceiverDependentModel Bool Bool Bool where
  preparation := sharedBit.preparation
  sender := sharedBit.sender
  receiver x := Channel.deterministic (fun _ => x)

theorem dependentReceiver_gap : influence dependentReceiver.observed = 1 := by
  rw [binary_influence]
  norm_num [ReceiverDependentModel.observed, ReceiverDependentModel.atSetting,
    Model.observed, Model.joint, dependentReceiver, sharedBit,
    bernoulli, coin, Channel.deterministic, Fintype.sum_bool]

/-- Keep a sender record exactly when it equals the setting. The underlying
preparation, normalized sender and setting-blind receiver are unchanged. -/
def selectedSharedBit : SelectedModel Bool Bool Bool where
  underlying := sharedBit
  keep x a := decide (a = x)

theorem selectedSharedBit_acceptance (x : Bool) :
    selectedSharedBit.acceptance x = 1/2 := by
  cases x <;> norm_num [SelectedModel.acceptance, SelectedModel.weight,
    selectedSharedBit, sharedBit, Model.joint, bernoulli, coin,
    Channel.deterministic, Fintype.sum_bool]

def postselected : Behavior (interface Bool) :=
  selectedSharedBit.observed (fun x => by rw [selectedSharedBit_acceptance]; norm_num)

/-- Explicit positive selection rate in each setting, fair unconditional
receiver, and unit TV after conditioning on the defined sender event. -/
theorem postselection_counterexample :
    (∀ x, selectedSharedBit.acceptance x = 1/2) ∧
    (∀ x, sharedBit.observed.prob x true = 1/2) ∧
    influence sharedBit.observed = 0 ∧ influence postselected = 1 := by
  refine ⟨selectedSharedBit_acceptance, ?_, sharedBit.no_influence, ?_⟩
  · intro x
    simp only [Model.observed, Model.marginal_formula]
    norm_num [sharedBit, bernoulli, coin, Channel.deterministic, Fintype.sum_bool]
  · rw [binary_influence]
    norm_num [postselected, SelectedModel.observed, SelectedModel.weight,
      SelectedModel.acceptance, selectedSharedBit, sharedBit, Model.joint,
      bernoulli, coin, Channel.deterministic, Fintype.sum_bool]

/-- Field-level preservation witnesses distinguish the three mechanisms even
though their final receiver tables agree. -/
theorem countermodel_fields :
    dependentPreparation.sender = sharedBit.sender ∧
    dependentPreparation.receiver = sharedBit.receiver ∧
    dependentReceiver.preparation = sharedBit.preparation ∧
    dependentReceiver.sender = sharedBit.sender ∧
    selectedSharedBit.underlying = sharedBit := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end
end OntologySeparation.SpacetimeInfluence
