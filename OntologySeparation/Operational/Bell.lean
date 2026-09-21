import OntologySeparation.Adapters.Shared
import OntologySeparation.Core.Certified

/-! The legacy realism slot specializes to outcome independence here. It is not
an identification of philosophical realism with one probability equation. -/
namespace OntologySeparation.OperationalBell
noncomputable section
structure Model (Λ : Type) [Fintype Λ] where
  preparation : Bell.interface.Setting → FiniteDistribution Λ
  response : Λ → Behavior Bell.interface
variable {Λ : Type} [Fintype Λ]
def Model.behavior (m : Model Λ) : Behavior Bell.interface where
  prob s o := ∑ l, (m.preparation s).mass l * (m.response l).prob s o
  nonneg s o := Finset.sum_nonneg fun l _ =>
    mul_nonneg ((m.preparation s).nonneg l) ((m.response l).nonneg s o)
  normalized s := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [show ∀ l, ∑ o, (m.response l).prob s o = 1 from
      fun l => (m.response l).normalized s, mul_one]
    exact (m.preparation s).total
/-- P(lambda|x,y) is independent of the selected settings. -/
def MeasurementIndependent (m : Model Λ) : Prop :=
  ∀ s t l, (m.preparation s).mass l = (m.preparation t).mass l
/-- Conditional parameter independence, stronger than observed no-signaling. -/
def ParameterIndependent (m : Model Λ) : Prop := ∀ l, Shared.NoSignaling (m.response l)
/-- Conditional joint response factorizes into its local marginals. -/
def OutcomeIndependent (m : Model Λ) : Prop := ∀ l x y a b,
  (m.response l).prob (x,y) (a,b) =
    (∑ b', (m.response l).prob (x,y) (a,b')) *
    (∑ a', (m.response l).prob (x,y) (a',b))
/-- The public behavior admits a setting-independent finite mixture of local
counterfactual assignments. This need not be the supplied hidden-state representation. -/
def JointCounterfactuals (m : Model Λ) : Prop := Bell.localTheory m.behavior

def vocabulary : Vocabulary (Model Λ) where
  realism := OutcomeIndependent
  globalTruth := JointCounterfactuals
  locality := ParameterIndependent
  measurementIndependent := MeasurementIndependent
def screeningOffProfile : AssumptionProfile := ⟨.require, .unspecified, .require, .require⟩

theorem product_chsh_bound (a b c d : ℝ)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) (hd : -1 ≤ d ∧ d ≤ 1) :
    a*c + a*d + b*c - b*d ≤ 2 := by
  have h1 : a*(c+d) ≤ |c+d| := by
    rcases le_total 0 (c+d) with h | h
    · rw [abs_of_nonneg h]; nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) h]
    · rw [abs_of_nonpos h]; nlinarith [mul_nonneg (by linarith : 0 ≤ a+1) (neg_nonneg.mpr h)]
  have h2 : b*(c-d) ≤ |c-d| := by
    rcases le_total 0 (c-d) with h | h
    · rw [abs_of_nonneg h]; nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) h]
    · rw [abs_of_nonpos h]; nlinarith [mul_nonneg (by linarith : 0 ≤ b+1) (neg_nonneg.mpr h)]
  have h3 : |c+d| + |c-d| ≤ 2 := by
    rcases le_total 0 (c+d) with h | h <;> rcases le_total 0 (c-d) with k | k
    · rw [abs_of_nonneg h, abs_of_nonneg k]; linarith [hc.2]
    · rw [abs_of_nonneg h, abs_of_nonpos k]; linarith [hd.2]
    · rw [abs_of_nonpos h, abs_of_nonneg k]; linarith [hd.1]
    · rw [abs_of_nonpos h, abs_of_nonpos k]; linarith [hc.1]
  nlinarith

theorem response_correlator (m : Model Λ) (ho : OutcomeIndependent m)
    (hp : ParameterIndependent m) (l : Λ) (x y : Fin 2) :
    Bell.correlator (m.response l) x y =
      RealQuantum.marginalA (m.response l) x 0 * RealQuantum.marginalB (m.response l) 0 y := by
  rw [Shared.marginalA_independent _ (hp l) x 0 y, Shared.marginalB_independent _ (hp l) 0 x y]
  have h00 := ho l x y false false
  have h01 := ho l x y false true
  have h10 := ho l x y true false
  have h11 := ho l x y true true
  simp at h00 h01 h10 h11
  simp [Bell.correlator, RealQuantum.marginalA, RealQuantum.marginalB,
    QIT.Bell.CHSH.outcomeSign, RealQuantum.sign, Fintype.sum_prod_type]
  nlinarith only [h00, h01, h10, h11]

theorem response_bound (m : Model Λ) (ho : OutcomeIndependent m)
    (hp : ParameterIndependent m) (l : Λ) : Bell.score (m.response l) ≤ 2 := by
  unfold Bell.score
  rw [response_correlator m ho hp, response_correlator m ho hp,
    response_correlator m ho hp, response_correlator m ho hp]
  exact product_chsh_bound _ _ _ _ (Shared.marginalA_bounds _ 0 0)
    (Shared.marginalA_bounds _ 1 0) (Shared.marginalB_bounds _ 0 0) (Shared.marginalB_bounds _ 0 1)

theorem score_mixture (m : Model Λ) (hi : MeasurementIndependent m) :
    Bell.score m.behavior = ∑ l, (m.preparation (0,0)).mass l * Bell.score (m.response l) := by
  have hc (x y : Fin 2) : Bell.correlator m.behavior x y =
      ∑ l, (m.preparation (0,0)).mass l * Bell.correlator (m.response l) x y := by
    unfold Bell.correlator Model.behavior
    simp_rw [hi (x,y) (0,0), Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro o _
    ring
  unfold Bell.score
  simp_rw [hc, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem chsh_bound (m : Model Λ) (ho : OutcomeIndependent m)
    (hp : ParameterIndependent m) (hi : MeasurementIndependent m) : Bell.score m.behavior ≤ 2 := by
  rw [score_mixture m hi]
  exact (m.preparation (0,0)).mean_le _ 2 (response_bound m ho hp)
def theory : Theory Bell.interface := profileTheory (vocabulary (Λ := Λ)) screeningOffProfile Model.behavior
def bound : Bound (theory (Λ := Λ)) Bell.score where
  ceiling := 2
  valid p h := by
    obtain ⟨m, hm, rfl⟩ := h
    exact chsh_bound m hm.1 hm.2.2.1 hm.2.2.2
def question : Question := ⟨Bell.interface, Bell.score⟩
def certified : ProfileBound question (vocabulary (Λ := Λ)) screeningOffProfile Model.behavior where
  target := theory
  bridge := ⟨fun m h => ⟨m, h, rfl⟩⟩
  bound := bound
/-- A second route: a common distribution of all local assignments. -/
def jointProfile : AssumptionProfile := ⟨.unspecified, .require, .unspecified, .unspecified⟩
def jointCertified : ProfileBound question (vocabulary (Λ := Λ)) jointProfile Model.behavior where
  target := Bell.localTheory
  bridge := ⟨fun _ h => h.2.1⟩
  bound := Bell.localBound
theorem joint_bound (m : Model Λ) (h : JointCounterfactuals m) : Bell.score m.behavior ≤ 2 :=
  Bell.localBound.valid _ h
theorem singlet_excludes :
    ¬ profileTheory (vocabulary (Λ := Λ)) screeningOffProfile Model.behavior Bell.singletBehavior := by
  apply certified.excludes
  change (2 : ℝ) < Bell.score Bell.singletBehavior
  rw [Bell.singlet_score]
  norm_num
end
end OntologySeparation.OperationalBell
