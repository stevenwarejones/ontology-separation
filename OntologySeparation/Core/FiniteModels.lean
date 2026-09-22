import OntologySeparation.Core.Extensions

/-! Checked membership and exclusion in an explicitly supplied finite convex model
class. A solver can propose the data; the kernel checks every generator/entry. -/
namespace OntologySeparation.FiniteModels
noncomputable section
variable {G : Type} [Fintype G] {E : Interface}

/-- A convex combination of normalized behaviors is itself normalized. -/
def mixture (generators : G → Behavior E) (weights : FiniteDistribution G) : Behavior E where
  prob s o := ∑ g, weights.mass g * (generators g).prob s o
  nonneg s o := Finset.sum_nonneg fun g _ =>
    mul_nonneg (weights.nonneg g) ((generators g).nonneg s o)
  normalized s := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Behavior.normalized, mul_one]
    exact weights.total

/-- Compatibility means reproducing the entire behavior, not one chosen score. -/
def Compatible (generators : G → Behavior E) (target : Behavior E) : Prop :=
  ∃ weights : FiniteDistribution G, ObservationallyEquivalent (mixture generators weights) target

structure Membership (generators : G → Behavior E) (target : Behavior E) where
  weights : FiniteDistribution G
  reproduces : ∀ s o, (mixture generators weights).prob s o = target.prob s o

theorem Membership.compatible {generators : G → Behavior E} {target : Behavior E}
    (w : Membership generators target) : Compatible generators target := ⟨w.weights, w.reproduces⟩

/-- Any listed generator realizes the class; a bound need not be vacuous. -/
def generatorMembership [DecidableEq G] (generators : G → Behavior E) (chosen : G) :
    Membership generators (generators chosen) where
  weights := {
    mass := fun g => if g = chosen then 1 else 0
    nonneg := by intro g; split_ifs <;> norm_num
    total := by simp }
  reproduces s o := by simp [mixture]

variable [Fintype E.Setting]

/-- An arbitrary linear statistic with coefficients indexed by setting and outcome. -/
def score (coefficients : E.Setting → E.Outcome → ℝ) (p : Behavior E) : ℝ :=
  ∑ s, ∑ o, coefficients s o * p.prob s o

theorem score_mixture (c : E.Setting → E.Outcome → ℝ) (generators : G → Behavior E)
    (weights : FiniteDistribution G) :
    score c (mixture generators weights) = weights.mean (fun g => score c (generators g)) := by
  unfold score mixture FiniteDistribution.mean
  simp only
  simp_rw [Finset.mul_sum]
  calc
    (∑ s, ∑ o, ∑ g, c s o * (weights.mass g * (generators g).prob s o)) =
        ∑ s, ∑ o, ∑ g, weights.mass g * (c s o * (generators g).prob s o) := by
      congr 1; funext s; congr 1; funext o; congr 1; funext g; ring
    _ = ∑ s, ∑ g, ∑ o, weights.mass g * (c s o * (generators g).prob s o) := by
      congr 1; funext s; exact Finset.sum_comm
    _ = ∑ g, ∑ s, ∑ o, weights.mass g * (c s o * (generators g).prob s o) :=
      Finset.sum_comm

theorem compatible_bound (c : E.Setting → E.Outcome → ℝ) (generators : G → Behavior E)
    (ceiling : ℝ) (valid : ∀ g, score c (generators g) ≤ ceiling)
    (target : Behavior E) (h : Compatible generators target) : score c target ≤ ceiling := by
  rcases h with ⟨w, hw⟩
  have hs : score c target = score c (mixture generators w) := by
    unfold score
    congr 1; funext s; congr 1; funext o; rw [hw s o]
  rw [hs, score_mixture]
  exact w.mean_le _ _ valid

/-- Every generator is checked. Strict violation is needed to exclude the target. -/
structure Exclusion (generators : G → Behavior E) (target : Behavior E) where
  coefficients : E.Setting → E.Outcome → ℝ
  ceiling : ℝ
  valid : ∀ g, score coefficients (generators g) ≤ ceiling
  violation : ceiling < score coefficients target

theorem Exclusion.excludes {generators : G → Behavior E} {target : Behavior E}
    (w : Exclusion generators target) : ¬ Compatible generators target := by
  intro h
  exact (not_lt_of_ge (compatible_bound w.coefficients generators w.ceiling w.valid target h))
    w.violation

/-- The two certificate kinds cannot certify contradictory conclusions. -/
theorem no_conflicting_certificates {generators : G → Behavior E} {target : Behavior E}
    (inside : Membership generators target) (outside : Exclusion generators target) : False :=
  outside.excludes inside.compatible
end
end OntologySeparation.FiniteModels
