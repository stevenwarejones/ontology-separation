import Mathlib.Algebra.Star.CHSH

/-! Re-export mathlib's ordered-star-algebra CHSH bounds without extra physical axioms.
The quantum upper bound here is an operator statement. The concrete singlet
witness in Experiments/Bell is a separate operational construction. -/
namespace OntologySeparation

/-- Existing general operator upper bound; √2 cubed equals 2√2. -/
theorem quantum_operator_bound {R : Type} [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (a₀ a₁ b₀ b₁ : R) (h : IsCHSHTuple a₀ a₁ b₀ b₁) :
    a₀*b₀ + a₀*b₁ + a₁*b₀ - a₁*b₁ ≤ (Real.sqrt 2)^3 • (1 : R) :=
  tsirelson_inequality a₀ a₁ b₀ b₁ h

end OntologySeparation
