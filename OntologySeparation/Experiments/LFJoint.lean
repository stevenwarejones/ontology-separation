import OntologySeparation.Experiments.LFAssumptionAtlas

/-! Finite joint-event formulation of Bong et al.'s LF assumptions.
Settings 0,1,2 encode paper settings 1,2,3. Records and outcomes are binary.
Locality is stated without division; under NSD it is equivalent to equality
of conditional marginals on every positive-mass record pair. -/
namespace OntologySeparation.LFJoint
noncomputable section
open scoped BigOperators
abbrev Record := Bool × Bool
abbrev Setting := LF.interface.Setting
abbrev Outcome := LF.interface.Outcome

/-- AOE joint table P(abcd|xy), normalized at each chosen setting pair.
This assigns no joint values to alternative, unperformed Wigner measurements. -/
structure Table where
  prob : Setting → Record → Outcome → ℝ
  nonneg : ∀ s r o, 0 ≤ prob s r o
  normalized : ∀ s, ∑ r, ∑ o, prob s r o = 1

def Table.mass (j : Table) (s : Setting) (r : Record) : ℝ := ∑ o, j.prob s r o

def Table.behavior (j : Table) : Behavior LF.interface where
  prob s o := ∑ r, j.prob s r o
  nonneg s o := Finset.sum_nonneg fun r _ => j.nonneg s r o
  normalized s := by rw [Finset.sum_comm]; exact j.normalized s

def IndependentRecords (j : Table) : Prop := ∀ s t r, j.mass s r = j.mass t r

def Readable (j : Table) : Prop :=
  (∀ r y, (∑ b, j.prob (0,y) r (r.1,b)) = j.mass (0,y) r) ∧
  (∀ r x, (∑ a, j.prob (x,0) r (a,r.2)) = j.mass (x,0) r)

/-- Joint marginal equalities; combine with IndependentRecords for conditional locality. -/
def Local (j : Table) : Prop :=
  (∀ r x y y' a, (∑ b, j.prob (x,y) r (a,b)) = ∑ b, j.prob (x,y') r (a,b)) ∧
  (∀ r x x' y b, (∑ a, j.prob (x,y) r (a,b)) = ∑ a, j.prob (x',y) r (a,b))

def Admissible (j : Table) : Prop := Readable j ∧ Local j ∧ IndependentRecords j

theorem mass_nonneg (j : Table) (s : Setting) (r : Record) : 0 ≤ j.mass s r :=
  Finset.sum_nonneg fun o _ => j.nonneg s r o

theorem prob_eq_zero_of_mass_zero (j : Table) (s : Setting) (r : Record)
    (h : j.mass s r = 0) (o : Outcome) : j.prob s r o = 0 := by
  have hb : j.prob s r o ≤ j.mass s r :=
    Finset.single_le_sum (fun o _ => j.nonneg s r o) (Finset.mem_univ o)
  have hn := j.nonneg s r o
  linarith

/-- A normalized response on an impossible record pair; its precise choice is unobservable. -/
def fallback (r : Record) : Behavior LF.interface where
  prob _ o := if o = r then 1 else 0
  nonneg _ _ := by split <;> norm_num
  normalized _ := by simp

/-- Ordinary conditional probabilities on positive mass, otherwise a readable local fallback. -/
def conditional (j : Table) (hi : IndependentRecords j) (r : Record) : Behavior LF.interface where
  prob s o := if j.mass (0,0) r = 0 then (fallback r).prob s o
    else j.prob s r o / j.mass (0,0) r
  nonneg s o := by
    split
    · exact (fallback r).nonneg s o
    · exact div_nonneg (j.nonneg s r o) (mass_nonneg j _ _)
  normalized s := by
    split_ifs with h
    · exact (fallback r).normalized s
    · rw [← Finset.sum_div]
      change j.mass s r / j.mass (0,0) r = 1
      rw [hi s (0,0) r, div_self h]

theorem conditional_reconstruct (j : Table) (hi : IndependentRecords j)
    (s : Setting) (r : Record) (o : Outcome) :
    j.mass (0,0) r * (conditional j hi r).prob s o = j.prob s r o := by
  by_cases h : j.mass (0,0) r = 0
  · rw [h, zero_mul]
    exact (prob_eq_zero_of_mass_zero j s r ((hi s (0,0) r).trans h) o).symm
  · simp only [conditional, h, ↓reduceIte]
    exact mul_div_cancel₀ _ h

def toOperational (j : Table) (hi : IndependentRecords j) : FriendRecords.Model Record where
  preparation _ := ⟨j.mass (0,0), mass_nonneg j (0,0), j.normalized (0,0)⟩
  response := conditional j hi
  charlie := Prod.fst
  debbie := Prod.snd

theorem toOperational_independent (j : Table) (hi : IndependentRecords j) :
    FriendRecords.IndependentPreparation (toOperational j hi) := by intro s t r; rfl

theorem toOperational_readable (j : Table) (hi : IndependentRecords j) (hr : Readable j) :
    FriendRecords.ReadableRecords (toOperational j hi) := by
  constructor
  · intro r y
    change (∑ b, (conditional j hi r).prob (0,y) (r.1,b)) = 1
    by_cases h : j.mass (0,0) r = 0
    · rcases r with ⟨c,d⟩
      cases c <;> cases d <;> simp [conditional, h, fallback]
    · simp only [conditional, h, ↓reduceIte, ← Finset.sum_div]
      rw [hr.1, hi (0,y) (0,0) r, div_self h]
  · intro r x
    change (∑ a, (conditional j hi r).prob (x,0) (a,r.2)) = 1
    by_cases h : j.mass (0,0) r = 0
    · rcases r with ⟨c,d⟩
      cases c <;> cases d <;> simp [conditional, h, fallback]
    · simp only [conditional, h, ↓reduceIte, ← Finset.sum_div]
      rw [hr.2, hi (x,0) (0,0) r, div_self h]

theorem toOperational_local (j : Table) (hi : IndependentRecords j) (hl : Local j) :
    FriendRecords.ConditionalLocality (toOperational j hi) := by
  intro r
  constructor
  · intro x y y' a
    change (∑ b, (conditional j hi r).prob (x,y) (a,b)) = _
    by_cases h : j.mass (0,0) r = 0
    · simp [toOperational, conditional, h, fallback]
    · simp only [toOperational, conditional, h, ↓reduceIte, ← Finset.sum_div]
      rw [hl.1]
  · intro x x' y b
    change (∑ a, (conditional j hi r).prob (x,y) (a,b)) = _
    by_cases h : j.mass (0,0) r = 0
    · simp [toOperational, conditional, h, fallback]
    · simp only [toOperational, conditional, h, ↓reduceIte, ← Finset.sum_div]
      rw [hl.2]

theorem toOperational_behavior (j : Table) (hi : IndependentRecords j) :
    (toOperational j hi).behavior = j.behavior := by
  have he : (toOperational j hi).behavior.prob = j.behavior.prob := by
    funext s o
    change (∑ r : Record, j.mass (0,0) r * (conditional j hi r).prob s o) = ∑ r : Record, j.prob s r o
    exact Finset.sum_congr rfl fun r _ => conditional_reconstruct j hi s r o
  cases ha : (toOperational j hi).behavior
  cases hb : j.behavior
  simp only [ha, hb] at he
  cases he
  rfl


/-- On possible records the response is exactly ordinary conditioning. -/
theorem conditional_probability (j : Table) (hi : IndependentRecords j)
    (r : Record) (s : Setting) (o : Outcome) (h : j.mass s r ≠ 0) :
    (conditional j hi r).prob s o = j.prob s r o / j.mass s r := by
  have hn : j.mass (0,0) r ≠ 0 := by rwa [← hi s (0,0) r]
  simp only [conditional, hn, ↓reduceIte, hi s (0,0) r]

/-- The division-free locality law is exactly locality of normalized responses.
The canonical response is local even on impossible records. -/
theorem local_iff_conditional (j : Table) (hi : IndependentRecords j) :
    Local j ↔ FriendRecords.ConditionalLocality (toOperational j hi) := by
  constructor
  · exact toOperational_local j hi
  · intro hl
    have ha (r : Record) (x y : Fin 3) (a : Bool) :
        (∑ b, j.prob (x,y) r (a,b)) =
          j.mass (0,0) r * ∑ b, (conditional j hi r).prob (x,y) (a,b) := by
      rw [Finset.mul_sum]
      simp_rw [conditional_reconstruct]
    have hb (r : Record) (x y : Fin 3) (b : Bool) :
        (∑ a, j.prob (x,y) r (a,b)) =
          j.mass (0,0) r * ∑ a, (conditional j hi r).prob (x,y) (a,b) := by
      rw [Finset.mul_sum]
      simp_rw [conditional_reconstruct]
    constructor
    · intro r x y y' a
      rw [ha, ha]
      exact congrArg (fun z => j.mass (0,0) r * z) ((hl r).1 x y y' a)
    · intro r x x' y b
      rw [hb, hb]
      exact congrArg (fun z => j.mass (0,0) r * z) ((hl r).2 x x' y b)

variable {Λ : Type} [Fintype Λ]

/-- Coarse-grain the latent states into the actual observed record pair. -/
def fromOperational (m : FriendRecords.Model Λ) : Table where
  prob s r o := ∑ l, if (m.charlie l, m.debbie l) = r then
    (m.preparation s).mass l * (m.response l).prob s o else 0
  nonneg s r o := Finset.sum_nonneg fun l _ => by
    split
    · exact mul_nonneg ((m.preparation s).nonneg l) ((m.response l).nonneg s o)
    · exact le_rfl
  normalized s := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ o : Outcome, ∑ l : Λ, (m.preparation s).mass l * (m.response l).prob s o := by
        apply Finset.sum_congr rfl
        intro o _
        rw [Finset.sum_comm]
        simp [eq_comm]
      _ = 1 := m.behavior.normalized s

theorem fromOperational_mass (m : FriendRecords.Model Λ) (s : Setting) (r : Record) :
    (fromOperational m).mass s r =
      ∑ l, if (m.charlie l, m.debbie l) = r then (m.preparation s).mass l else 0 := by
  unfold Table.mass fromOperational
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs with h
  · simp [← Finset.mul_sum, (m.response l).normalized]
  · simp

theorem fromOperational_independent (m : FriendRecords.Model Λ)
    (hi : FriendRecords.IndependentPreparation m) : IndependentRecords (fromOperational m) := by
  intro s t r
  simp_rw [fromOperational_mass, hi s t]

theorem fromOperational_readable (m : FriendRecords.Model Λ)
    (hr : FriendRecords.ReadableRecords m) : Readable (fromOperational m) := by
  constructor
  · intro r y
    rw [fromOperational_mass]
    change (∑ b, ∑ l, _) = _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : (m.charlie l, m.debbie l) = r
    · subst r
      simp only [↓reduceIte, ← Finset.mul_sum, hr.1, mul_one]
    · simp [h]
  · intro r x
    rw [fromOperational_mass]
    change (∑ a, ∑ l, _) = _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : (m.charlie l, m.debbie l) = r
    · subst r
      simp only [↓reduceIte, ← Finset.mul_sum, hr.2, mul_one]
    · simp [h]

theorem fromOperational_local (m : FriendRecords.Model Λ)
    (hl : FriendRecords.ConditionalLocality m)
    (hi : FriendRecords.IndependentPreparation m) : Local (fromOperational m) := by
  constructor
  · intro r x y y' a
    change (∑ b, ∑ l, _) = ∑ b, ∑ l, _
    rw [Finset.sum_comm, Finset.sum_comm (f := fun b l =>
      if (m.charlie l, m.debbie l) = r then
        (m.preparation (x,y')).mass l * (m.response l).prob (x,y') (a,b) else 0)]
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : (m.charlie l, m.debbie l) = r
    · simp only [h, ↓reduceIte, ← Finset.mul_sum]
      rw [hi (x,y) (x,y') l, (hl l).1 x y y' a]
    · simp [h]
  · intro r x x' y b
    change (∑ a, ∑ l, _) = ∑ a, ∑ l, _
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a l =>
      if (m.charlie l, m.debbie l) = r then
        (m.preparation (x',y)).mass l * (m.response l).prob (x',y) (a,b) else 0)]
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : (m.charlie l, m.debbie l) = r
    · simp only [h, ↓reduceIte, ← Finset.mul_sum]
      rw [hi (x,y) (x',y) l, (hl l).2 x x' y b]
    · simp [h]

theorem fromOperational_behavior (m : FriendRecords.Model Λ) :
    (fromOperational m).behavior = m.behavior := by
  have he : (fromOperational m).behavior.prob = m.behavior.prob := by
    funext s o
    change (∑ r : Record, ∑ l : Λ, if (m.charlie l, m.debbie l) = r then
      (m.preparation s).mass l * (m.response l).prob s o else 0) = _
    rw [Finset.sum_comm]
    simp [eq_comm, FriendRecords.Model.behavior]
  cases ha : (fromOperational m).behavior
  cases hb : m.behavior
  simp only [ha, hb] at he
  cases he
  rfl

/-- Precisely the observable behaviors admitting this joint-event extension. -/
def theory (p : Behavior LF.interface) : Prop := ∃ j : Table, Admissible j ∧ j.behavior = p

theorem joint_iff_operational (p : Behavior LF.interface) :
    theory p ↔ LFAssumptionAtlas.OperationalLF p := by
  constructor
  · rintro ⟨j, ⟨hr, hl, hi⟩, hp⟩
    exact ⟨Record, inferInstance, toOperational j hi, toOperational_readable j hi hr,
      toOperational_local j hi hl, toOperational_independent j hi,
      (toOperational_behavior j hi).trans hp⟩
  · rintro ⟨Λ, inst, m, hr, hl, hi, hp⟩
    letI := inst
    exact ⟨fromOperational m, ⟨fromOperational_readable m hr,
      fromOperational_local m hl hi, fromOperational_independent m hi⟩,
      (fromOperational_behavior m).trans hp⟩

theorem joint_iff_lf (p : Behavior LF.interface) : theory p ↔ LF.theory p :=
  (joint_iff_operational p).trans (LFAssumptionAtlas.operational_iff_lf p)

theorem bound (j : Table) (h : Admissible j) : RealQuantum.genuineLF j.behavior ≤ 6 := by
  rw [← toOperational_behavior j h.2.2]
  exact FriendRecords.bound (toOperational j h.2.2) (toOperational_readable j h.2.2 h.1)
    (toOperational_local j h.2.2 h.2.1) (toOperational_independent j h.2.2)

theorem quantum_excluded : ¬ theory RealQuantum.lfBehavior := by
  intro h
  exact LF.quantumSeparation.excludes ((joint_iff_lf _).mp h)

end
end OntologySeparation.LFJoint
