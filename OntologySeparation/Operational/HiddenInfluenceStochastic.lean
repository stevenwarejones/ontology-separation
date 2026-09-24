import OntologySeparation.Operational.HiddenInfluenceStrategies
import OntologySeparation.Operational.HiddenInfluenceCausality

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
    if atomEquiv k = j then m.weight (atomEquiv k) else 0) = m.weight j
  have h := atomEquiv.sum_comp
    (fun j' : Atom => if j' = j then m.weight j' else 0)
  simpa using h

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


/-- Pack a selected late-setting pair into the operational late context. -/
def lateFromBool (y z : Bool) : Late :=
  ⟨2 * y.toNat + z.toNat, by
    have hy := Bool.toNat_le y
    have hz := Bool.toNat_le z
    omega⟩

/-- Pack the four visible Boolean outcomes into the operational output order
`abcd`. -/
def VisibleOutcome.toOutcome (v : VisibleOutcome) : Outcome :=
  ⟨8 * v.a.toNat + 4 * v.b.toNat + 2 * v.c.toNat + v.d.toNat, by
    have ha := Bool.toNat_le v.a
    have hb := Bool.toNat_le v.b
    have hc := Bool.toNat_le v.c
    have hd := Bool.toNat_le v.d
    omega⟩


/-- Decode every operational late setting back to the Boolean pair used by the
stochastic kernels. -/
def lateToBool (l : Late) : Bool × Bool :=
  (decide (l.val / 2 = 1), decide (l.val % 2 = 1))

/-- The Boolean late-setting encoding covers every operational late setting. -/
theorem lateFromBool_lateToBool (l : Late) :
    lateFromBool (lateToBool l).1 (lateToBool l).2 = l := by
  apply Fin.ext
  fin_cases l <;> decide

theorem lateFromBool_surjective : Function.Surjective (fun p : Bool × Bool =>
    lateFromBool p.1 p.2) := by
  intro l
  exact ⟨lateToBool l, lateFromBool_lateToBool l⟩

/-- Decode every packed operational output to its four visible Boolean bits. -/
def outcomeToVisible (o : Outcome) : VisibleOutcome where
  a := decide (o.val / 8 = 1)
  b := decide (o.val / 4 % 2 = 1)
  c := decide (o.val / 2 % 2 = 1)
  d := decide (o.val % 2 = 1)

/-- The visible-outcome encoding covers every operational output. -/
theorem VisibleOutcome.toOutcome_outcomeToVisible (o : Outcome) :
    (outcomeToVisible o).toOutcome = o := by
  apply Fin.ext
  fin_cases o <;> decide

theorem VisibleOutcome.toOutcome_surjective :
    Function.Surjective VisibleOutcome.toOutcome := by
  intro o
  exact ⟨outcomeToVisible o, VisibleOutcome.toOutcome_outcomeToVisible o⟩


theorem outcomeToVisible_toOutcome (v : VisibleOutcome) :
    outcomeToVisible v.toOutcome = v := by
  rcases v with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def visibleOutcomeEquiv : VisibleOutcome ≃ Outcome where
  toFun := VisibleOutcome.toOutcome
  invFun := outcomeToVisible
  left_inv := outcomeToVisible_toOutcome
  right_inv := VisibleOutcome.toOutcome_outcomeToVisible

theorem VisibleOutcome.toOutcome_injective :
    Function.Injective VisibleOutcome.toOutcome :=
  visibleOutcomeEquiv.injective


@[simp] theorem VisibleOutcome.toOutcome_eq_iff (v w : VisibleOutcome) :
    v.toOutcome = w.toOutcome ↔ v = w :=
  VisibleOutcome.toOutcome_injective.eq_iff

theorem strategy_visible_output (e : Early) (s : Strategy) (y z : Bool) :
    output (strategyAtom e s) (lateFromBool y z) = (s.visible y z).toOutcome := by
  apply Fin.ext
  simpa [lateFromBool, Strategy.visible, VisibleOutcome.toOutcome] using
    strategy_output e s y z

theorem Model.fromStrategies_weight_strategyAtom
    (q : Early → FiniteDistribution Strategy) (e : Early) (s : Strategy) :
    (Model.fromStrategies q).weight (strategyAtom e s) = (q e).mass s := by
  change (∑ k : Early × Strategy,
    if atomEquiv k = atomEquiv (e,s) then (q k.1).mass k.2 else 0) = (q e).mass s
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The named deterministic strategy probability is exactly the corresponding
packed `Model.behavior` probability. This is the bridge from the strategy-level
determinization argument to the observable behavior consumed by Theorem 2. -/
theorem Model.fromStrategies_prob_eq_selectedMass
    (q : Early → FiniteDistribution Strategy)
    (e : Early) (y z : Bool) (v : VisibleOutcome) :
    (Model.fromStrategies q).behavior.prob
        (e, lateFromBool y z) v.toOutcome =
      selectedMass (q e) y z v := by
  classical
  change (∑ j : Atom,
    if early j = e ∧ output j (lateFromBool y z) = v.toOutcome
    then (Model.fromStrategies q).weight j else 0) =
      ∑ s, if s.visible y z = v then (q e).mass s else 0
  rw [← atomEquiv.sum_comp]
  simp only [atomEquiv, Fintype.sum_prod_type, strategy_early,
    strategy_visible_output, Model.fromStrategies_weight_strategyAtom,
    VisibleOutcome.toOutcome_eq_iff]
  rw [Finset.sum_eq_single e]
  · simp [strategy_early, strategy_visible_output,
      Model.fromStrategies_weight_strategyAtom]
  · intro e' _ hne
    apply Finset.sum_eq_zero
    intro s _
    simp [strategy_early, hne]
  · simp

/-- The observable behavior associated with a stochastic conditional-local
model is its deterministic refinement. The theorem below shows this definition
is extensionally equal to the original factorized stochastic probabilities. -/
noncomputable def StochasticModel.behavior {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) : Behavior interface :=
  m.determinize.behavior

/-- Recipient total variation is preserved exactly by determinization. -/
theorem StochasticModel.tv_eq_determinize
    {Ω : Type} [Fintype Ω] (m : StochasticModel Ω) (c : Context) :
    tv m.behavior c = tv m.determinize.behavior c := rfl

/-- Every signaling budget statement is preserved by determinization. -/
theorem StochasticModel.within_iff_determinize
    {Ω : Type} [Fintype Ω] (m : StochasticModel Ω) (delta : ℝ) :
    Within m.behavior delta ↔ Within m.determinize.behavior delta := Iff.rfl

/-- The maximum recipient signaling strength is preserved exactly by
determinization. -/
noncomputable def StochasticModel.signaling {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) : ℝ :=
  m.determinize.signaling

@[simp] theorem StochasticModel.signaling_eq_determinize
    {Ω : Type} [Fintype Ω] (m : StochasticModel Ω) :
    m.signaling = m.determinize.signaling := rfl

theorem selectedMass_bind {α : Type} [Fintype α]
    (d : FiniteDistribution α) (k : α → FiniteDistribution Strategy)
    (y z : Bool) (v : VisibleOutcome) :
    selectedMass (FiniteKernel.bind d k) y z v =
      ∑ x, d.mass x * selectedMass (k x) y z v := by
  classical
  unfold selectedMass
  simp_rw [FiniteKernel.bind_mass]
  calc
    (∑ s : Strategy,
        if s.visible y z = v then ∑ x, d.mass x * (k x).mass s else 0) =
      ∑ s : Strategy, ∑ x,
        if s.visible y z = v then d.mass x * (k x).mass s else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : s.visible y z = v <;> simp [h]
    _ = ∑ x, ∑ s : Strategy,
        if s.visible y z = v then d.mass x * (k x).mass s else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x, d.mass x *
        ∑ s : Strategy, if s.visible y z = v then (k x).mass s else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : s.visible y z = v <;> simp [h]

@[simp] theorem selectedMass_pure (s : Strategy) (y z : Bool) (v : VisibleOutcome) :
    selectedMass (FiniteKernel.pure s) y z v =
      if s.visible y z = v then 1 else 0 := by
  classical
  unfold selectedMass
  rw [Finset.sum_eq_single s]
  · simp [FiniteKernel.pure]
  · intro t _ hts
    simp [FiniteKernel.pure, hts]
  · simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem StochasticModel.selectedMass_strategyGiven
    {Ω : Type} [Fintype Ω] (m : StochasticModel Ω)
    (e : Early) (ω : Ω) (y z : Bool) (v : VisibleOutcome) :
    selectedMass (m.strategyGiven e ω) y z v =
      (m.a e ω).mass v.a *
      (m.d e ω).mass v.d *
      (m.b e ω (boolSetting y)).mass v.b *
      (m.c e ω (boolSetting z)).mass v.c := by
  classical
  rcases v with ⟨va,vb,vc,vd⟩
  have hb0sum : (m.b e ω 0).mass false + (m.b e ω 0).mass true = 1 := by
    simpa [Fintype.sum_bool] using (m.b e ω 0).total
  have hb1sum : (m.b e ω 1).mass false + (m.b e ω 1).mass true = 1 := by
    simpa [Fintype.sum_bool] using (m.b e ω 1).total
  have hc0sum : (m.c e ω 0).mass false + (m.c e ω 0).mass true = 1 := by
    simpa [Fintype.sum_bool] using (m.c e ω 0).total
  have hc1sum : (m.c e ω 1).mass false + (m.c e ω 1).mass true = 1 := by
    simpa [Fintype.sum_bool] using (m.c e ω 1).total
  have hb0 : (m.b e ω 0).mass true = 1 - (m.b e ω 0).mass false := by linarith
  have hb1 : (m.b e ω 1).mass true = 1 - (m.b e ω 1).mass false := by linarith
  have hc0 : (m.c e ω 0).mass true = 1 - (m.c e ω 0).mass false := by linarith
  have hc1 : (m.c e ω 1).mass true = 1 - (m.c e ω 1).mass false := by linarith
  unfold StochasticModel.strategyGiven
  rw [selectedMass_bind]
  simp_rw [selectedMass_bind]
  simp_rw [selectedMass_pure]
  cases y <;> cases z <;>
    cases va <;> cases vb <;> cases vc <;> cases vd <;>
    simp [Strategy.visible, boolSetting, Fintype.sum_bool, hb0, hb1, hc0, hc1] <;>
    ring

/-- Determinization preserves every selected conditional-local joint
probability. The unchosen B/C potential responses sum to one. -/
theorem StochasticModel.selected_probability {Ω : Type} [Fintype Ω]
    (m : StochasticModel Ω) (e : Early) (y z : Bool) (v : VisibleOutcome) :
    selectedMass (m.toStrategies e) y z v =
      m.factorizedProbability e y z v := by
  unfold StochasticModel.toStrategies StochasticModel.factorizedProbability
  rw [selectedMass_bind]
  simp_rw [m.selectedMass_strategyGiven]
  apply Finset.sum_congr rfl
  intro ω _
  ring_nf
/-- The stochastic factorized joint probability and the packed observable
behavior agree for every early context, late setting and full outcome. -/
theorem StochasticModel.behavior_prob_eq_factorized
    {Ω : Type} [Fintype Ω] (m : StochasticModel Ω)
    (e : Early) (y z : Bool) (v : VisibleOutcome) :
    m.behavior.prob (e, lateFromBool y z) v.toOutcome =
      m.factorizedProbability e y z v := by
  rw [StochasticModel.behavior, StochasticModel.determinize,
    Model.fromStrategies_prob_eq_selectedMass, m.selected_probability]

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
  cases a <;> cases d <;> cases b0 <;> cases b1 <;> cases c0 <;> cases c1 <;>
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


/-- The stochastic representative of an existing packed model returns exactly
the same hidden-response weights after determinization. -/
theorem Model.stochastic_roundtrip_weight (m : Model) (j : Atom) :
    ((StochasticModel.ofStrategies m.toStrategies).determinize).weight j =
      m.weight j := by
  rw [StochasticModel.determinize_ofStrategies_weight]
  exact m.fromStrategies_toStrategies_weight j

/-- The explicit stochastic representative preserves every recipient TV. -/
theorem Model.stochastic_roundtrip_tv (m : Model) (c : Context) :
    tv ((StochasticModel.ofStrategies m.toStrategies).behavior) c =
      tv m.behavior c := by
  unfold StochasticModel.behavior tv difference marginal mean
  simp only [Model.behavior]
  simp_rw [m.stochastic_roundtrip_weight]

/-- The explicit stochastic representative preserves the overall signaling
strength used by the forced-signaling theorem. -/
theorem Model.stochastic_roundtrip_signaling (m : Model) :
    (StochasticModel.ofStrategies m.toStrategies).signaling = m.signaling := by
  have htv (c : Context) :
      tv ((StochasticModel.ofStrategies m.toStrategies).determinize).behavior c =
        tv m.behavior c := by
    change tv (StochasticModel.ofStrategies m.toStrategies).behavior c = tv m.behavior c
    exact m.stochastic_roundtrip_tv c
  unfold StochasticModel.signaling Model.signaling
  apply le_antisymm
  · apply Finset.sup'_le
    intro c hc
    rw [htv c]
    exact Finset.le_sup' (tv m.behavior) hc
  · apply Finset.sup'_le
    intro c hc
    rw [← htv c]
    exact Finset.le_sup'
      (tv ((StochasticModel.ofStrategies m.toStrategies).determinize).behavior) hc

end
end OntologySeparation.HiddenInfluence
