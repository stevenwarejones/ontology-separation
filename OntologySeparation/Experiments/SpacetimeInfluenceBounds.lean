import OntologySeparation.Experiments.SpacetimeInfluence
import Mathlib.Algebra.Star.Basic

namespace OntologySeparation.SpacetimeInfluence
noncomputable section

/-- Algebraic nonselective-operation bridge. Completeness and commutation fix
the receiver effect even for correlated quantum states. Positivity, locality of
the operators and continuum microcausality are not derived by this identity. -/
theorem local_operation_fixes_effect {R I : Type} [Ring R] [StarRing R] [Fintype I]
    (K : I → R) (E : R) (hcomplete : ∑ i, star (K i) * K i = 1)
    (hcommute : ∀ i, E * K i = K i * E) :
    (∑ i, star (K i) * E * K i) = E := by
  calc
    (∑ i, star (K i) * E * K i) = ∑ i, (star (K i) * K i) * E := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, hcommute i, ← mul_assoc]
    _ = E := by rw [← Finset.sum_mul, hcomplete, one_mul]

/-- Exact mean of the signed match score under a fair fresh setting. -/
theorem fair_score_mean (p0 p1 : ℝ) :
    (1/2 : ℝ)*(1-2*p0) + (1/2 : ℝ)*(2*p1-1) = p1-p0 := by ring

theorem biased_score_mean (p0 p1 pi : ℝ) :
    (1-pi)*(1-2*p0)+pi*(2*p1-1) =
      (p1-p0)+(2*pi-1)*(p1+p0-1) := by ring

/-- A coupling supplies an operational probability budget, not a time in seconds. -/
theorem coupling_gap (d : FiniteDistribution (Bool × Bool)) :
    |(d.mass (true,true) + d.mass (true,false)) -
      (d.mass (true,true) + d.mass (false,true))| ≤
      d.mass (true,false) + d.mass (false,true) := by
  have h0 := d.nonneg (true,false)
  have h1 := d.nonneg (false,true)
  apply abs_le.mpr
  constructor <;> linarith

/-- Two separately calibrated couplings around one null receiver law. -/
theorem calibrated_gap (p0 p1 q e0 e1 : ℝ)
    (h0 : |p0-q| ≤ e0) (h1 : |p1-q| ≤ e1) : |p1-p0| ≤ e0+e1 := by
  obtain ⟨ha,hb⟩ := abs_le.mp h0
  obtain ⟨hc,hd⟩ := abs_le.mp h1
  apply abs_le.mpr
  constructor <;> linarith

/-- If both setting-specific good laws equal q, unequal contamination fractions
cost at most max(e0,e1), sharper than the general two-coupling bound. -/
theorem contamination_gap (q r0 r1 e0 e1 : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr00 : 0 ≤ r0) (hr01 : r0 ≤ 1)
    (hr10 : 0 ≤ r1) (hr11 : r1 ≤ 1) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) :
    |((1-e1)*q+e1*r1)-((1-e0)*q+e0*r0)| ≤ max e0 e1 := by
  have h0 := le_max_left e0 e1
  have h1 := le_max_right e0 e1
  have hq := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr h0)
  have hq' := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr h1)
  have hq0' := mul_nonneg hq0 (sub_nonneg.mpr h0)
  have hq1' := mul_nonneg hq0 (sub_nonneg.mpr h1)
  have h00 := mul_nonneg he0 hr00
  have h01 := mul_nonneg he0 (sub_nonneg.mpr hr01)
  have h10 := mul_nonneg he1 hr10
  have h11 := mul_nonneg he1 (sub_nonneg.mpr hr11)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- An event indicator integrated against the existing finite distribution. -/
def eventMass {Ω : Type} [Fintype Ω] (d : FiniteDistribution Ω) (e : Ω → Bool) : ℝ :=
  ∑ w, d.mass w * (if e w then 1 else 0)

/-- No independence of failures is needed. Apply to timing, leakage and record
errors, or to confidence-interval and calibration failures. -/
theorem three_event_bound {Ω : Type} [Fintype Ω] (d : FiniteDistribution Ω)
    (bad f0 f1 f2 : Ω → Bool)
    (h : ∀ w, bad w = true → f0 w = true ∨ f1 w = true ∨ f2 w = true) :
    eventMass d bad ≤ eventMass d f0 + eventMass d f1 + eventMass d f2 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  have hn := d.nonneg w
  have hh := h w
  cases hb : bad w <;> cases h0 : f0 w <;> cases h1 : f1 w <;> cases h2 : f2 w <;>
    simp_all <;> linarith

/-- A finite-shot risk transfer: any rejection that requires a confidence or
calibration failure inherits their sum of risks. This is not a binomial theorem. -/
theorem rejection_risk {Ω : Type} [Fintype Ω] (d : FiniteDistribution Ω)
    (reject fail0 fail1 failCal : Ω → Bool) (a0 a1 ac : ℝ)
    (himp : ∀ w, reject w = true →
      fail0 w = true ∨ fail1 w = true ∨ failCal w = true)
    (h0 : eventMass d fail0 ≤ a0) (h1 : eventMass d fail1 ≤ a1)
    (hc : eventMass d failCal ≤ ac) : eventMass d reject ≤ a0+a1+ac := by
  have h := three_event_bound d reject fail0 fail1 failCal himp
  linarith

/-- Difference interval on simultaneous marginal coverage. -/
theorem difference_interval (p0 p1 l0 u0 l1 u1 : ℝ)
    (h0 : l0 ≤ p0 ∧ p0 ≤ u0) (h1 : l1 ≤ p1 ∧ p1 ≤ u1) :
    l1-u0 ≤ p1-p0 ∧ p1-p0 ≤ u1-l0 := by constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

/-- Absolute-value upper bound, including an inconclusive or null result. -/
theorem absolute_interval_upper (d l u : ℝ) (h : l ≤ d ∧ d ≤ u) :
    |d| ≤ max (-l) u := by
  apply abs_le.mpr
  constructor
  · have hm := le_max_left (-l) u; linarith [h.1]
  · exact h.2.trans (le_max_right _ _)

theorem strict_interval_exclusion (d l u budget : ℝ)
    (h : l ≤ d ∧ d ≤ u) (hn : |d| ≤ budget)
    (hr : budget < l ∨ u < -budget) : False := by
  obtain ⟨ha,hb⟩ := abs_le.mp hn
  rcases hr with hr | hr <;> linarith [h.1,h.2]

/-- Every pair in the uncertain time supports is spacelike when the conservative
distance bound exceeds c times their maximum possible time difference. -/
theorem spacelike_of_budget (c d dmin a0 a1 b0 b1 ta tb : ℝ)
    (hc : 0 ≤ c) (hd : dmin ≤ d) (ha : a0 ≤ ta ∧ ta ≤ a1)
    (hb : b0 ≤ tb ∧ tb ≤ b1)
    (hbudget : c * max (b1-a0) (a1-b0) < dmin) : c * |tb-ta| < d := by
  have htime : |tb-ta| ≤ max (b1-a0) (a1-b0) := by
    apply abs_le.mpr
    constructor
    · have h := le_max_right (b1-a0) (a1-b0); linarith [ha.2,hb.1]
    · have h := le_max_left (b1-a0) (a1-b0); linarith [ha.1,hb.2]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left htime hc) (hbudget.trans_le hd)

/-- A record is strictly earlier throughout both uncertainty intervals. -/
theorem earlier_record (recordLatest choiceEarliest recordTime choiceTime : ℝ)
    (hr : recordTime ≤ recordLatest) (hc : choiceEarliest ≤ choiceTime)
    (hgap : recordLatest < choiceEarliest) : recordTime < choiceTime :=
  lt_of_le_of_lt hr (lt_of_lt_of_le hgap hc)

end
end OntologySeparation.SpacetimeInfluence
