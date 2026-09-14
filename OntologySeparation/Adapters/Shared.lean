import OntologySeparation.Experiments.LocalFriendliness
import OntologySeparation.Experiments.Bell
import OntologySeparation.Core.Extensions

/-! Shared setting restrictions and missing cross-model correlation adapters. -/
namespace OntologySeparation.Shared
noncomputable section

/-- No-signaling directly on normalized public probabilities, at any setting count. -/
def NoSignaling {n : Nat} (p : Behavior (RealQuantum.interface n)) : Prop :=
  (∀ x y y' a, (∑ b : Bool, p.prob (x,y) (a,b)) = ∑ b : Bool, p.prob (x,y') (a,b)) ∧
  (∀ x x' y b, (∑ a : Bool, p.prob (x,y) (a,b)) = ∑ a : Bool, p.prob (x',y) (a,b))

theorem singlet_marginal (a b : RealQuantum.Basis) (s : Bool) :
    (∑ t : Bool, RealQuantum.probability a b s t) = 1/2 := by
  have h := a.unit
  have k := b.unit
  have hk : (a.c^2+a.s^2)*(b.c^2+b.s^2) = 1 := by rw [h,k]; norm_num
  cases s <;> simp [RealQuantum.probability, RealQuantum.Basis.vector] <;> nlinarith [hk]

theorem singlet_marginal_b (a b : RealQuantum.Basis) (t : Bool) :
    (∑ s : Bool, RealQuantum.probability a b s t) = 1/2 := by
  have hk : (a.c^2+a.s^2)*(b.c^2+b.s^2) = 1 := by rw [a.unit,b.unit]; norm_num
  cases t <;> simp [RealQuantum.probability, RealQuantum.Basis.vector] <;> nlinarith [hk]

theorem singlet_noSignaling {n : Nat} (a b : Fin n → RealQuantum.Basis) :
    NoSignaling (RealQuantum.behavior a b) := by
  constructor
  · intro x y y' s
    change (∑ t : Bool, RealQuantum.probability (a x) (b y) s t) = _
    rw [singlet_marginal]
    exact (singlet_marginal _ _ _).symm
  · intro x x' y t
    change (∑ s : Bool, RealQuantum.probability (a x) (b y) s t) = _
    rw [singlet_marginal_b]
    exact (singlet_marginal_b _ _ _).symm

/-- LF need not obey CHSH on the two settings other than asking the friend. -/
def inner (p : Behavior LF.interface) : Behavior Bell.interface :=
  p.restrict (Fin 2 × Fin 2) (fun xy => (⟨xy.1.val+1, by omega⟩, ⟨xy.2.val+1, by omega⟩))

theorem inner_score (q : LF.Component) : Bell.score (inner q.behavior) = LF.innerCHSH q := by
  simp [Bell.score, Bell.correlator, inner, Behavior.restrict,
    LF.Component.behavior, LF.Component.prob, LF.Component.a, LF.Component.b,
    LF.Component.e, LF.innerCHSH, LF.sign, QIT.Bell.CHSH.outcomeSign,
    Fintype.sum_prod_type]
  ring

theorem lf_inner_PR : Bell.score (inner LF.prComponent.behavior) = 4 := by
  rw [inner_score, LF.prComponent_innerCHSH]

theorem lf_noSignaling (q : LF.Component) : NoSignaling q.behavior := by
  constructor
  · intro x y y' s
    exact (q.marginal_alice x y s).trans (q.marginal_alice x y' s).symm
  · intro x x' y t
    exact (q.marginal_bob x y t).trans (q.marginal_bob x' y t).symm

/-- No-signaling identifies the moment marginals across remote settings. -/
theorem marginalA_independent {n : Nat} (p : Behavior (RealQuantum.interface n))
    (h : NoSignaling p) (x y y' : Fin n) :
    RealQuantum.marginalA p x y = RealQuantum.marginalA p x y' := by
  have hf := h.1 x y y' false
  have ht := h.1 x y y' true
  simp at hf ht
  simp [RealQuantum.marginalA, Fintype.sum_prod_type, RealQuantum.sign]
  linarith

theorem marginalB_independent {n : Nat} (p : Behavior (RealQuantum.interface n))
    (h : NoSignaling p) (x x' y : Fin n) :
    RealQuantum.marginalB p x y = RealQuantum.marginalB p x' y := by
  have hf := h.2 x x' y false
  have ht := h.2 x x' y true
  simp at hf ht
  simp [RealQuantum.marginalB, Fintype.sum_prod_type, RealQuantum.sign]
  linarith

theorem moment_positive (p : Behavior LF.interface) (h : NoSignaling p)
    (x y : Fin 3) (a b : Bool) :
    0 ≤ 1 + RealQuantum.sign a * RealQuantum.marginalA p x 0 +
      RealQuantum.sign b * RealQuantum.marginalB p 0 y +
      RealQuantum.sign a * RealQuantum.sign b * RealQuantum.correlator p x y := by
  rw [marginalA_independent p h x 0 y, marginalB_independent p h 0 x y]
  have hn := p.normalized (x,y)
  have hp := p.nonneg (x,y) (a,b)
  simp [Fintype.sum_prod_type] at hn
  cases a <;> cases b <;>
    simp [RealQuantum.sign, RealQuantum.marginalA, RealQuantum.marginalB,
      RealQuantum.correlator, Fintype.sum_prod_type] at * <;> linarith

/-- Exact no-signaling ceiling. The eight positivity terms are a rational dual
certificate, checked by Lean; an optimizer is not part of the trusted proof. -/
theorem LF_noSignaling_bound (p : Behavior LF.interface) (h : NoSignaling p) :
    RealQuantum.genuineLF p ≤ 10 := by
  have p0 := moment_positive p h 0 0 true true
  have p1 := moment_positive p h 0 1 false false
  have p2 := moment_positive p h 1 0 false false
  have p3 := moment_positive p h 1 1 false true
  have p4 := moment_positive p h 1 1 true false
  have p5 := moment_positive p h 1 2 true true
  have p6 := moment_positive p h 2 1 true true
  have p7 := moment_positive p h 2 2 false false
  simp only [RealQuantum.sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul,
    mul_one, mul_neg, neg_neg] at *
  unfold RealQuantum.genuineLF
  linarith

def nsExtreme : Behavior LF.interface where
  prob xy ab := (1 + RealQuantum.sign ab.1 * RealQuantum.sign ab.2 *
    (if xy.1.val = 1 ∧ xy.2.val = 1 then 1 else -1)) / 4
  nonneg xy ab := by
    obtain ⟨x,y⟩ := xy
    obtain ⟨a,b⟩ := ab
    split_ifs <;> cases a <;> cases b <;> norm_num [RealQuantum.sign]
  normalized xy := by
    simp [Fintype.sum_prod_type, RealQuantum.sign] <;> split_ifs <;> norm_num

theorem nsExtreme_noSignaling : NoSignaling nsExtreme := by
  constructor
  · intro x y y' a
    cases a <;> simp [nsExtreme, RealQuantum.sign] <;> split_ifs <;> norm_num
  · intro x x' y b
    cases b <;> simp [nsExtreme, RealQuantum.sign] <;> split_ifs <;> norm_num

theorem nsExtreme_score : RealQuantum.genuineLF nsExtreme = 10 := by
  norm_num [RealQuantum.genuineLF, RealQuantum.marginalA, RealQuantum.marginalB,
    RealQuantum.correlator, nsExtreme, RealQuantum.sign, Fintype.sum_prod_type]

theorem LF_ns_sharp :
    (∀ p : Behavior LF.interface, NoSignaling p → RealQuantum.genuineLF p ≤ 10) ∧
    NoSignaling nsExtreme ∧ RealQuantum.genuineLF nsExtreme = 10 :=
  ⟨LF_noSignaling_bound, nsExtreme_noSignaling, nsExtreme_score⟩

/-- Three-setting deterministic local response table, embedded into LF. -/
def deterministic (a b : Fin 3 → Bool) : LF.Component where
  charlie := a 0
  debbie := b 0
  alice x := LF.sign (a ⟨x.val+1, by omega⟩)
  bob y := LF.sign (b ⟨y.val+1, by omega⟩)
  corr x y := LF.sign (a ⟨x.val+1, by omega⟩) * LF.sign (b ⟨y.val+1, by omega⟩)
  positive := by
    intro x y s t
    cases ha : a ⟨x.val+1, by omega⟩ <;> cases hb : b ⟨y.val+1, by omega⟩ <;>
      cases s <;> cases t <;> norm_num [LF.sign]

/-- Local finite mixtures at three settings; the same finite-response semantics
as the two-setting Bell class, with an explicitly expanded setting domain. -/
structure LocalThree (ι : Type) [Fintype ι] where
  weights : FiniteDistribution ι
  alice : ι → Fin 3 → Bool
  bob : ι → Fin 3 → Bool

def LocalThree.toLF {ι : Type} [Fintype ι] (m : LocalThree ι) : LF.Model ι where
  weight := m.weights.mass
  nonneg := m.weights.nonneg
  normalized := m.weights.total
  component i := deterministic (m.alice i) (m.bob i)

theorem local_three_LF_bound {ι : Type} [Fintype ι] (m : LocalThree ι) :
    RealQuantum.genuineLF m.toLF.behavior ≤ 6 := by
  rw [LF.model_score_bridge]
  exact m.toLF.score_le_six

/-- Any binary correlator lies between -1 and 1, without assuming no-signaling. -/
theorem correlator_bounds {n : Nat} (p : Behavior (RealQuantum.interface n)) (x y : Fin n) :
    -1 ≤ RealQuantum.correlator p x y ∧ RealQuantum.correlator p x y ≤ 1 := by
  have h := p.normalized (x,y)
  have h00 := p.nonneg (x,y) (false,false)
  have h01 := p.nonneg (x,y) (false,true)
  have h10 := p.nonneg (x,y) (true,false)
  have h11 := p.nonneg (x,y) (true,true)
  simp [Fintype.sum_prod_type] at h
  simp [RealQuantum.correlator, RealQuantum.sign, Fintype.sum_prod_type]
  constructor <;> linarith

theorem marginalA_bounds {n : Nat} (p : Behavior (RealQuantum.interface n)) (x y : Fin n) :
    -1 ≤ RealQuantum.marginalA p x y ∧ RealQuantum.marginalA p x y ≤ 1 := by
  have h := p.normalized (x,y)
  have h00 := p.nonneg (x,y) (false,false)
  have h01 := p.nonneg (x,y) (false,true)
  have h10 := p.nonneg (x,y) (true,false)
  have h11 := p.nonneg (x,y) (true,true)
  simp [Fintype.sum_prod_type] at h
  simp [RealQuantum.marginalA, RealQuantum.sign, Fintype.sum_prod_type]
  constructor <;> linarith

theorem marginalB_bounds {n : Nat} (p : Behavior (RealQuantum.interface n)) (x y : Fin n) :
    -1 ≤ RealQuantum.marginalB p x y ∧ RealQuantum.marginalB p x y ≤ 1 := by
  have h := p.normalized (x,y)
  have h00 := p.nonneg (x,y) (false,false)
  have h01 := p.nonneg (x,y) (false,true)
  have h10 := p.nonneg (x,y) (true,false)
  have h11 := p.nonneg (x,y) (true,true)
  simp [Fintype.sum_prod_type] at h
  simp [RealQuantum.marginalB, RealQuantum.sign, Fintype.sum_prod_type]
  constructor <;> linarith

/-- Conservative algebraic ceiling, valid even for signaling behavior. Not tight. -/
theorem LF_algebraic_bound (p : Behavior LF.interface) : RealQuantum.genuineLF p ≤ 14 := by
  have a0 := marginalA_bounds p 0 0
  have a1 := marginalA_bounds p 1 0
  have b0 := marginalB_bounds p 0 0
  have b1 := marginalB_bounds p 0 1
  have e00 := correlator_bounds p 0 0
  have e01 := correlator_bounds p 0 1
  have e10 := correlator_bounds p 1 0
  have e11 := correlator_bounds p 1 1
  have e12 := correlator_bounds p 1 2
  have e21 := correlator_bounds p 2 1
  have e22 := correlator_bounds p 2 2
  unfold RealQuantum.genuineLF
  linarith

/-- P03: an epsilon-contaminated LF model has G <= 6+8 epsilon. -/
theorem LF_contamination (good bad : Behavior LF.interface) (hg : LF.theory good)
    (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    (1-epsilon)*RealQuantum.genuineLF good + epsilon*RealQuantum.genuineLF bad ≤
      6+8*epsilon := by
  have g : RealQuantum.genuineLF good ≤ 6 := LF.genuineBound.valid good hg
  have b := LF_algebraic_bound bad
  have g' := mul_le_mul_of_nonneg_left g (show 0 ≤ 1-epsilon by linarith)
  have b' := mul_le_mul_of_nonneg_left b h0
  nlinarith

theorem LF_contamination_required (good bad : Behavior LF.interface) (hg : LF.theory good)
    (epsilon observed : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1)
    (hobs : observed = (1-epsilon)*RealQuantum.genuineLF good +
      epsilon*RealQuantum.genuineLF bad) : (observed-6)/8 ≤ epsilon := by
  have h := LF_contamination good bad hg epsilon h0 h1
  rw [← hobs] at h
  linarith

/-- The contamination statistic is the score of the actual mixed probability table. -/
theorem LF_mix_score (p q : Behavior LF.interface) (v : ℝ)
    (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    RealQuantum.genuineLF (p.mix q v h0 h1) =
      v * RealQuantum.genuineLF p + (1-v) * RealQuantum.genuineLF q := by
  simp [RealQuantum.genuineLF, RealQuantum.marginalA, RealQuantum.marginalB,
    RealQuantum.correlator, Behavior.mix, Fintype.sum_prod_type, RealQuantum.sign]
  ring

/-- If the bad sector is also no-signaling the contamination ceiling improves to 10. -/
theorem LF_NS_contamination (good bad : Behavior LF.interface) (hg : LF.theory good)
    (hb : NoSignaling bad) (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    (1-epsilon)*RealQuantum.genuineLF good + epsilon*RealQuantum.genuineLF bad ≤
      6+4*epsilon := by
  have g : RealQuantum.genuineLF good ≤ 6 := LF.genuineBound.valid good hg
  have b := LF_noSignaling_bound bad hb
  have g' := mul_le_mul_of_nonneg_left g (show 0 ≤ 1-epsilon by linarith)
  have b' := mul_le_mul_of_nonneg_left b h0
  nlinarith

def saturatingModel : LF.Model Unit where
  weight _ := 1
  nonneg _ := by norm_num
  normalized := by simp
  component _ := deterministic (fun _ => false) (fun _ => true)

theorem saturating_is_LF : LF.theory saturatingModel.behavior :=
  ⟨Unit, inferInstance, saturatingModel, rfl⟩

theorem saturating_score : RealQuantum.genuineLF saturatingModel.behavior = 6 := by
  rw [LF.model_score_bridge]
  norm_num [LF.Model.score, saturatingModel, LF.componentScore, deterministic, LF.sign]

/-- The upper contamination bound is attained by an explicit normalized mixture
for every allowed epsilon. This is a sharp bound for this contamination model. -/
theorem LF_NS_contamination_attained (epsilon : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1) :
    RealQuantum.genuineLF (nsExtreme.mix saturatingModel.behavior epsilon h0 h1) =
      6+4*epsilon := by
  rw [LF_mix_score, nsExtreme_score, saturating_score]
  ring

theorem LF_NS_fraction_required (good bad : Behavior LF.interface) (hg : LF.theory good)
    (hb : NoSignaling bad) (epsilon observed : ℝ) (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1)
    (hobs : observed = (1-epsilon)*RealQuantum.genuineLF good +
      epsilon*RealQuantum.genuineLF bad) : (observed-6)/4 ≤ epsilon := by
  have h := LF_NS_contamination good bad hg hb epsilon h0 h1
  rw [← hobs] at h
  linarith

end
end OntologySeparation.Shared
