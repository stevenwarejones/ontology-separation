import OntologySeparation.Recipes
open OntologySeparation OntologySeparation.Recipes

-- These assertions cover physical conventions and noncommuting operation order.
example : probability (Law.dephasing 1 2) ⟨.plus, [.expose], .x⟩ = 3/4 := by recipe_check
example : probability (Law.dephasing 1 2) ⟨.plus, [.expose, .expose], .x⟩ = 5/8 := by recipe_check
example : probability (Law.dephasing 1 2) ⟨.plus, [.hadamard, .expose], .z⟩ = 1 := by recipe_check
example : probability (Law.dephasing 1 2) ⟨.plus, [.expose, .hadamard], .z⟩ = 3/4 := by recipe_check
example : probability (Law.dephasing 0 1) ⟨.plus, [.phaseFlip, .hadamard], .z⟩ = 0 := by recipe_check
example : probability (Law.dephasing 0 1) ⟨.plus, [.hadamard, .phaseFlip], .z⟩ = 1 := by recipe_check
example : probability (Law.dephasing 1 1) ⟨.zero, [], .z⟩ = 1 := by recipe_check
example : probability (Law.dephasing 1 1) ⟨.zero, [], .x⟩ = 1/2 := by recipe_check
example : probability (Law.dephasing 0 1) ⟨.plus, [.dephase (Rate.fraction 1 1)], .x⟩ = 1/2 := by recipe_check
example : probability (Law.dephasing 1 1) ⟨.plus, [.dephase (Rate.fraction 1 1)], .x⟩ = 1/2 := by recipe_check
-- The generated equality is about the actual real-valued normalized experiment.
example : (interpret (Law.dephasing 1 4) ⟨.plus, [.expose, .expose], .x⟩).prob () true = 25/32 := by
  rw [probability_correct]
  recipe_check
example (m : Law) (r : Recipe) : 0 ≤ probability m r ∧ probability m r ≤ 1 := probability_bounds m r
example : True := by
  fail_if_success
    have wrong : probability (Law.dephasing 1 2) ⟨.plus, [.expose], .x⟩ = 1 := by recipe_check
  trivial
