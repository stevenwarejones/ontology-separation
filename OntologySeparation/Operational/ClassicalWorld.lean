import OntologySeparation.Operational.Countermodels

/-! Historically excluded Bell-local law package. Statistical rejection by measured
data is documented separately from mathematical exclusion of a singlet table. -/
namespace OntologySeparation.ClassicalWorld
noncomputable section
structure Model (Λ : Type) [Fintype Λ] where
  preparation : FiniteDistribution Λ
  alice : Λ → Fin 2 → Bool
  bob : Λ → Fin 2 → Bool
variable {Λ : Type} [Fintype Λ]
def Model.operational (m : Model Λ) : OperationalBell.Model Λ where
  preparation := fun _ => m.preparation
  response l := Countermodels.deterministic (fun s => (m.alice l s.1, m.bob l s.2))
theorem screened (m : Model Λ) : OperationalBell.OutcomeIndependent m.operational :=
  fun _ x y a b => Countermodels.deterministic_screening _ x y a b
theorem independent (m : Model Λ) : OperationalBell.MeasurementIndependent m.operational := by
  intro s t l; rfl
theorem localResponses (m : Model Λ) : OperationalBell.ParameterIndependent m.operational := by
  intro l
  constructor
  · intro x y y' a
    cases ha : m.alice l x <;> cases hb : m.bob l y <;> cases hc : m.bob l y' <;> cases a <;>
      simp [Model.operational, Countermodels.deterministic, Channel.deterministic, ha, hb, hc]
  · intro x x' y b
    cases ha : m.alice l x <;> cases hb : m.alice l x' <;> cases hc : m.bob l y <;> cases b <;>
      simp [Model.operational, Countermodels.deterministic, Channel.deterministic, ha, hb, hc]
theorem chsh_bound (m : Model Λ) : Bell.score m.operational.behavior ≤ 2 :=
  OperationalBell.chsh_bound m.operational (screened m) (localResponses m) (independent m)
theorem cannot_reproduce_singlet (m : Model Λ) : m.operational.behavior ≠ Bell.singletBehavior := by
  intro h
  have hb := chsh_bound m
  rw [h, Bell.singlet_score] at hb
  norm_num at hb
def constantWorld : Model Unit := ⟨Countermodels.unitPrior, fun _ _ => false, fun _ _ => false⟩
theorem constant_score : Bell.score constantWorld.operational.behavior = 2 := by
  norm_num [Bell.score, Bell.correlator, constantWorld, Model.operational,
    OperationalBell.Model.behavior, Countermodels.unitPrior, Countermodels.deterministic,
    Channel.deterministic, QIT.Bell.CHSH.outcomeSign, Fintype.sum_prod_type]
end
end OntologySeparation.ClassicalWorld
