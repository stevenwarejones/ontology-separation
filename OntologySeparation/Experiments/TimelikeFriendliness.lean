import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Core.Extensions
import OntologySeparation.Operational.Bell
import OntologySeparation.Experiments.Bell

/-! Correlator-level reproduction of the factorized consequence used in the
Causal Time-Symmetric Friendliness theorem of Mukherjee--Hance (2026).

The paper's AOE + ATS + NRC + SPE assumptions imply a decomposition conditioned
on pseudo-events (c,d).  This file formalizes the resulting binary correlator
class and its CHSH bound.  It does not yet claim a paper-faithful encoding of the
four assumptions separately. -/
namespace OntologySeparation.TimelikeFriendliness
noncomputable section

/-- Conditional expectation values for one pseudo-event pair. -/
structure Response where
  alice : Fin 2 → ℝ
  bob : Fin 2 → ℝ
  alice_bounds : ∀ x, -1 ≤ alice x ∧ alice x ≤ 1
  bob_bounds : ∀ y, -1 ≤ bob y ∧ bob y ≤ 1

/-- A finite distribution over pseudo-event pairs together with screened local
response means.  The hidden type is kept generic because only its finite mixture
structure is used in the CHSH argument. -/
structure Model (Λ : Type) [Fintype Λ] where
  hidden : FiniteDistribution Λ
  response : Λ → Response

variable {Λ : Type} [Fintype Λ]

def correlator (m : Model Λ) (x y : Fin 2) : ℝ :=
  m.hidden.mean (fun l => (m.response l).alice x * (m.response l).bob y)

def score (m : Model Λ) : ℝ :=
  correlator m 0 0 + correlator m 0 1 + correlator m 1 0 - correlator m 1 1

theorem response_chsh_le_two (r : Response) :
    r.alice 0 * r.bob 0 + r.alice 0 * r.bob 1 +
      r.alice 1 * r.bob 0 - r.alice 1 * r.bob 1 ≤ 2 := by
  exact OperationalBell.product_chsh_bound _ _ _ _
    (r.alice_bounds 0) (r.alice_bounds 1) (r.bob_bounds 0) (r.bob_bounds 1)

theorem score_as_mean (m : Model Λ) :
    score m =
      m.hidden.mean (fun l =>
        (m.response l).alice 0 * (m.response l).bob 0 +
        (m.response l).alice 0 * (m.response l).bob 1 +
        (m.response l).alice 1 * (m.response l).bob 0 -
        (m.response l).alice 1 * (m.response l).bob 1) := by
  unfold score correlator FiniteDistribution.mean
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The paper's factorized pseudo-event consequence obeys CHSH <= 2. -/
theorem factorized_chsh_bound (m : Model Λ) : score m ≤ 2 := by
  rw [score_as_mean]
  exact m.hidden.mean_le _ 2 (fun l => response_chsh_le_two (m.response l))

/-- The repository's exact rational singlet witness lies strictly beyond the
factorized timelike class at the observable CHSH-score level. -/
theorem singlet_score_violates_factorized :
    2 < Bell.score Bell.singletBehavior := by
  rw [Bell.singlet_score]
  norm_num

/-- A concrete nonempty factorized model saturating the classical ceiling. -/
def unitModel : Model Unit where
  hidden := {
    mass := fun _ => 1
    nonneg := by intro _; norm_num
    total := by simp
  }
  response := fun _ => {
    alice := fun _ => 1
    bob := fun _ => 1
    alice_bounds := by intro _; norm_num
    bob_bounds := by intro _; norm_num
  }

theorem unitModel_score : score unitModel = 2 := by
  norm_num [score, correlator, FiniteDistribution.mean, unitModel]

end
end OntologySeparation.TimelikeFriendliness
