import OntologySeparation.Operational.HiddenInfluenceStrategies

/-!
Finite stochastic conditional-local response kernels for the hidden-influence
scenario, and their deterministic refinement into `HiddenInfluence.Model`.

The stochastic model samples a finite hidden state for each early context and,
conditioned on that state, samples A and D outputs and independent B/C local
responses. B's response kernel receives only B's late setting; C's receives only
C's. Sampling both potential late responses converts the model into a
distribution over deterministic `Strategy` values without changing any selected
conditional-local probabilities.
-/

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators
noncomputable section

namespace FiniteKernel

/-- Point mass used to embed deterministic responses into stochastic kernels. -/
def pure {α : Type} [Fintype α] [DecidableEq α] (x : α) :
    FiniteDistribution α where
  mass y := if y = x then 1 else 0
  nonneg y := by split <;> simp
  total := by simp

/-- Finite mixture/bind. This is only a probability-distribution helper; it adds
no physical assumption. -/
def bind {α β : Type} [Fintype α] [Fintype β]
    (d : FiniteDistribution α) (k : α → FiniteDistribution β) :
    FiniteDistribution β where
  mass y := ∑ x, d.mass x * (k x).mass y
  nonneg y := Finset.sum_nonneg fun x _ =>
    mul_nonneg (d.nonneg x) ((k x).nonneg y)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (k _).total, mul_one]
    exact d.total

@[simp] theorem pure_mass {α : Type} [Fintype α] [DecidableEq α]
    (x y : α) : (pure x).mass y = if y = x then 1 else 0 := rfl

@[simp] theorem bind_mass {α β : Type} [Fintype α] [Fintype β]
    (d : FiniteDistribution α) (k : α → FiniteDistribution β) (y : β) :
    (bind d k).mass y = ∑ x, d.mass x * (k x).mass y := rfl

@[simp] theorem bind_pure_mass {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] (x : α) (k : α → FiniteDistribution β) (y : β) :
    (bind (pure x) k).mass y = (k x).mass y := by
  classical
  simp [bind, pure]

end FiniteKernel

private def responseBit (n k : ℕ) : Bool := decide (n / (2^k) % 2 = 1)

/-- Decode the named deterministic strategy packed into an atom. -/
def atomStrategy (j : Atom) : Strategy where
  a := responseBit j.val 5
  d := responseBit j.val 4
  b0 := responseBit j.val 2
  b1 := responseBit j.val 3
  c0 := responseBit j.val 0
  c1 := responseBit j.val 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem strategyAtom_atomStrategy : ∀ j : Atom,
    strategyAtom (early j) (atomStrategy j) = j := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem atomStrategy_strategyAtom : ∀ e : Early, ∀ s : Strategy,
    atomStrategy (strategyAtom e s) = s := by
  with_unfolding_all decide +kernel

/-- The packed atom type is exactly four early contexts times the 64 named
deterministic local response strategies. -/
def atomEquiv : Early × Strategy ≃ Atom where
  toFun k := strategyAtom k.1 k.2
  invFun j := (early j, atomStrategy j)
  left_inv k := by
    apply Prod.ext
    · exact strategy_early k.1 k.2
    · exact atomStrategy_strategyAtom k.1 k.2
  right_inv := strategyAtom_atomStrategy

/-- Every existing packed response model can be unpacked into four ordinary
distributions over named deterministic strategies. -/
def Model.toStrategies (m : Model) (e : Early) : FiniteDistribution Strategy where
  mass s := m.weight (strategyAtom e s)
  nonneg s := m.nonnegative (strategyAtom e s)
  total := by
    have h := m.normalized e
    rw [← atomEquiv.sum_comp] at h
    simpa [atomEquiv, Fintype.sum_prod_type, strategy_early, Finset.sum_ite_irrel] using h

theorem Model.fromStrategies_toStrategies_weight (m : Model) (j : Atom) :
    (Model.fromStrategies m.toStrategies).weight j = m.weight j := by
  change (∑ k : Early × Strategy,
    if strategyAtom k.1 k.2 = j then
      m.weight (strategyAtom k.1 k.2) else 0) = m.weight j
  rw [atomEquiv.sum_comp]
  simp [atomEquiv]

/-- Packing and unpacking a response model preserves every public probability. -/
theorem Model.fromStrategies_toStrategies (m : Model) :
    ObservationallyEquivalent (Model.fromStrategies m.toStrategies).behavior m.behavior := by
  intro s o
  unfold Model.behavior
  simp_rw [m.fromStrategies_toStrategies_weight]

/-- A finite stochastic conditional-local hidden-response model. The hidden
distribution may depend on the early context. Conditioned on that hidden state,
A and D are sampled locally and B/C each receive only their own late setting.

Allowing stochastic A/D here avoids assuming that the hidden state has already
been refined to contain the early outcomes. -/
structure StochasticModel (Ω : Type) [Fintype Ω] where
  hidden : Early → FiniteDistribution Ω
  a : Early → Ω → FiniteDistribution Bool
  d : Early → Ω → FiniteDistribution Bool
  b : Early → Ω → Fin 2 → FiniteDistribution Bool
  c : Early → Ω → Fin 2 → FiniteDistribution Bool

private def boolSetting (x : Bool) : Fin 2 :=
  ⟨x.toNat, by cases x <;> simp⟩

/-- Independently sample all potential outputs for one hidden state. Sampling
unselected B/C potential outcomes is the deterministic-refinement construction;
the theorem `selected_probability` below proves that they integrate out. -/
def StochasticModel.strategyGiven {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) (e : Early) (ω : Ω) :
    FiniteDistribution Strategy :=
  FiniteKernel.bind (m.a e ω) fun a =>
  FiniteKernel.bind (m.d e ω) fun d =>
  FiniteKernel.bind (m.b e ω 0) fun b0 =>
  FiniteKernel.bind (m.b e ω 1) fun b1 =>
  FiniteKernel.bind (m.c e ω 0) fun c0 =>
  FiniteKernel.bind (m.c e ω 1) fun c1 =>
    FiniteKernel.pure { a := a, d := d, b0 := b0, b1 := b1, c0 := c0, c1 := c1 }

/-- Distribution over deterministic local response tables obtained by refining
the finite stochastic hidden state. -/
def StochasticModel.toStrategies {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) (e : Early) : FiniteDistribution Strategy :=
  FiniteKernel.bind (m.hidden e) (m.strategyGiven e)

/-- Determinization into the response-table model used by the signaling theorem. -/
def StochasticModel.determinize {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) : Model :=
  Model.fromStrategies m.toStrategies

structure VisibleOutcome where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  deriving DecidableEq, Fintype

def Strategy.visible (s : Strategy) (y z : Bool) : VisibleOutcome where
  a := s.a
  b := if y then s.b1 else s.b0
  c := if z then s.c1 else s.c0
  d := s.d

/-- Probability of one selected visible tuple under a distribution over full
response tables. -/
def selectedMass (q : FiniteDistribution Strategy) (y z : Bool)
    (v : VisibleOutcome) : ℝ :=
  ∑ s, if s.visible y z = v then q.mass s else 0

/-- The original factorized conditional-local probability, before deterministic
refinement. -/
def StochasticModel.factorizedProbability {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) (e : Early) (y z : Bool)
    (v : VisibleOutcome) : ℝ :=
  ∑ ω, (m.hidden e).mass ω *
    (m.a e ω).mass v.a *
    (m.d e ω).mass v.d *
    (m.b e ω (boolSetting y)).mass v.b *
    (m.c e ω (boolSetting z)).mass v.c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Determinization preserves every selected conditional-local joint
probability. The unchosen B/C potential responses sum to one. -/
theorem StochasticModel.selected_probability {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) (e : Early) (y z : Bool) (v : VisibleOutcome) :
    selectedMass (m.toStrategies e) y z v =
      m.factorizedProbability e y z v := by
  classical
  rcases v with ⟨va, vb, vc, vd⟩
  cases y <;> cases z <;>
    simp [selectedMass, Strategy.visible, StochasticModel.toStrategies,
      StochasticModel.strategyGiven, StochasticModel.factorizedProbability,
      FiniteKernel.bind, FiniteKernel.pure, boolSetting, Fintype.sum_bool,
      (m.a e _).total, (m.d e _).total,
      (m.b e _ 0).total, (m.b e _ 1).total,
      (m.c e _ 0).total, (m.c e _ 1).total] <;>
    ring

/-- A deterministic strategy mixture is a special stochastic conditional-local
model, using point response kernels. -/
def StochasticModel.ofStrategies (q : Early → FiniteDistribution Strategy) :
    StochasticModel Strategy where
  hidden := q
  a _ s := FiniteKernel.pure s.a
  d _ s := FiniteKernel.pure s.d
  b _ s y := FiniteKernel.pure (if y = 0 then s.b0 else s.b1)
  c _ s z := FiniteKernel.pure (if z = 0 then s.c0 else s.c1)

private theorem StochasticModel.strategyGiven_ofStrategies_mass
    (q : Early → FiniteDistribution Strategy) (e : Early) (s t : Strategy) :
    ((StochasticModel.ofStrategies q).strategyGiven e s).mass t =
      if t = s then 1 else 0 := by
  rcases s with ⟨a, d, b0, b1, c0, c1⟩
  cases b1 <;> cases c0 <;> cases c1 <;>
    simp [StochasticModel.strategyGiven, StochasticModel.ofStrategies,
      FiniteKernel.pure]

theorem StochasticModel.toStrategies_ofStrategies
    (q : Early → FiniteDistribution Strategy) (e : Early) (s : Strategy) :
    ((StochasticModel.ofStrategies q).toStrategies e).mass s = (q e).mass s := by
  change (∑ x, (q e).mass x *
    ((StochasticModel.ofStrategies q).strategyGiven e x).mass s) = (q e).mass s
  simp_rw [StochasticModel.strategyGiven_ofStrategies_mass]
  simp

/-- Determinizing the stochastic embedding of a deterministic strategy mixture
returns the same response-table weights. -/
theorem StochasticModel.determinize_ofStrategies_weight
    (q : Early → FiniteDistribution Strategy) (j : Atom) :
    ((StochasticModel.ofStrategies q).determinize).weight j =
      (Model.fromStrategies q).weight j := by
  unfold StochasticModel.determinize Model.fromStrategies Model.ofAtoms atomWeights
  simp_rw [StochasticModel.toStrategies_ofStrategies]

theorem StochasticModel.determinize_ofStrategies_observational
    (q : Early → FiniteDistribution Strategy) :
    ObservationallyEquivalent
      ((StochasticModel.ofStrategies q).determinize).behavior
      (Model.fromStrategies q).behavior := by
  intro s o
  unfold Model.behavior
  simp_rw [StochasticModel.determinize_ofStrategies_weight]

/-- Every packed `Model` has a stochastic conditional-local representative and
the round trip preserves all observable probabilities. Together with
`StochasticModel.determinize`, this gives both directions of the finite
representation equivalence used by the forced-signaling theorem. -/
theorem Model.stochastic_roundtrip (m : Model) :
    ObservationallyEquivalent
      ((StochasticModel.ofStrategies m.toStrategies).determinize).behavior
      m.behavior := by
  intro s o
  calc
    ((StochasticModel.ofStrategies m.toStrategies).determinize).behavior.prob s o =
        (Model.fromStrategies m.toStrategies).behavior.prob s o :=
      StochasticModel.determinize_ofStrategies_observational m.toStrategies s o
    _ = m.behavior.prob s o := m.fromStrategies_toStrategies s o

end
end OntologySeparation.HiddenInfluence
