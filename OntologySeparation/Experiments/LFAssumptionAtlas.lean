import OntologySeparation.Operational.FriendRecords

/-! Exact correspondence for the repository's finite 3×3, binary-outcome LF
encoding. This is not a completeness theorem for all facets or observer models.
The reverse construction checks that the conditional-box encoding adds no
extra restriction to the three operational laws used by FriendRecords. -/
namespace OntologySeparation.LFAssumptionAtlas
noncomputable section
open FriendRecords

variable {Λ : Type} [Fintype Λ]

/-- Realize an LF mixture as setting-independent preparation of readable records
and normalized conditional response tables. -/
def operational (m : LF.Model Λ) : FriendRecords.Model Λ where
  preparation _ := ⟨m.weight, m.nonneg, m.normalized⟩
  response l := (m.component l).behavior
  charlie l := (m.component l).charlie
  debbie l := (m.component l).debbie

theorem operational_independent (m : LF.Model Λ) :
    IndependentPreparation (operational m) := by
  intro s t l
  rfl

theorem operational_readable (m : LF.Model Λ) :
    ReadableRecords (operational m) := by
  constructor
  · intro l y
    exact (m.component l).read_charlie y
  · intro l x
    exact (m.component l).read_debbie x

theorem operational_local (m : LF.Model Λ) :
    ConditionalLocality (operational m) := by
  intro l
  constructor
  · intro x y y' a
    change (∑ b, (m.component l).prob (x,y) (a,b)) =
      ∑ b, (m.component l).prob (x,y') (a,b)
    rw [LF.Component.marginal_alice, LF.Component.marginal_alice]
  · intro x x' y b
    change (∑ a, (m.component l).prob (x,y) (a,b)) =
      ∑ a, (m.component l).prob (x',y) (a,b)
    rw [LF.Component.marginal_bob, LF.Component.marginal_bob]

theorem operational_behavior (m : LF.Model Λ) :
    (operational m).behavior = m.behavior := by
  rfl

/-- Exactly the finite operational class satisfying the three named laws.
No outcome independence or joint assignment of alternative Wigner outcomes. -/
def OperationalLF (p : Behavior LF.interface) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (m : FriendRecords.Model Λ),
    ReadableRecords m ∧ ConditionalLocality m ∧ IndependentPreparation m ∧ m.behavior = p

/-- Both inclusions, not merely a sufficient encoding for the LF bound. -/
theorem operational_iff_lf (p : Behavior LF.interface) :
    OperationalLF p ↔ LF.theory p := by
  constructor
  · rintro ⟨Λ, inst, m, hr, hl, hi, hp⟩
    letI := inst
    exact ⟨Λ, inst, m.toLF hl, (probability_preserved m hr hl hi).trans hp⟩
  · rintro ⟨Λ, inst, m, hp⟩
    letI := inst
    exact ⟨Λ, inst, operational m, operational_readable m,
      operational_local m, operational_independent m, (operational_behavior m).trans hp⟩

/-- A nonempty, normalized countermodel to the purported implication
“the three LF laws imply outcome independence.” The inner PR box is not quantum. -/
def prMixture : LF.Model Unit where
  weight _ := 1
  nonneg _ := by norm_num
  normalized := by simp
  component _ := LF.prComponent

def prOperational : FriendRecords.Model Unit := operational prMixture

theorem pr_not_outcomeIndependent : ¬ OutcomeIndependent prOperational := by
  intro h
  have hcell := h () 1 1 false false
  norm_num [prOperational, operational, prMixture, LF.Component.behavior,
    LF.Component.prob, LF.Component.a, LF.Component.b, LF.Component.e,
    LF.prComponent, LF.sign] at hcell

/-- A constructive non-implication, with all retained premises checked. -/
theorem outcome_independence_not_required :
    ∃ m : FriendRecords.Model Unit,
      ReadableRecords m ∧ ConditionalLocality m ∧ IndependentPreparation m ∧
        ¬ OutcomeIndependent m :=
  ⟨prOperational, operational_readable prMixture, operational_local prMixture,
    operational_independent prMixture, pr_not_outcomeIndependent⟩

/-- Existing quantum witness excludes precisely this operational class. -/
theorem quantum_excludes_operational : ¬ OperationalLF RealQuantum.lfBehavior := by
  intro h
  exact LF.quantumSeparation.excludes ((operational_iff_lf _).mp h)

end
end OntologySeparation.LFAssumptionAtlas
