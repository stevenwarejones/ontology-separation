import OntologySeparation.Adapters.Shared
import OntologySeparation.Core.Certified

/-! Three independently selected laws on arbitrary conditional response tables.
No joint assignment to alternative Wigner outcomes is assumed. -/
namespace OntologySeparation.FriendRecords
noncomputable section
structure Model (Λ : Type) [Fintype Λ] where
  preparation : LF.interface.Setting → FiniteDistribution Λ
  response : Λ → Behavior LF.interface
  charlie : Λ → Bool
  debbie : Λ → Bool
variable {Λ : Type} [Fintype Λ]
def Model.behavior (m : Model Λ) : Behavior LF.interface where
  prob s o := ∑ l, (m.preparation s).mass l * (m.response l).prob s o
  nonneg s o := Finset.sum_nonneg fun l _ =>
    mul_nonneg ((m.preparation s).nonneg l) ((m.response l).nonneg s o)
  normalized s := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [show ∀ l, ∑ o, (m.response l).prob s o = 1 from
      fun l => (m.response l).normalized s, mul_one]
    exact (m.preparation s).total
def IndependentPreparation (m : Model Λ) : Prop :=
  ∀ s t l, (m.preparation s).mass l = (m.preparation t).mass l
/-- Asking a friend returns its fixed record at every remote setting. -/
def ReadableRecords (m : Model Λ) : Prop :=
  (∀ l y, ∑ b, (m.response l).prob (0,y) (m.charlie l,b) = 1) ∧
  (∀ l x, ∑ a, (m.response l).prob (x,0) (a,m.debbie l) = 1)
def ConditionalLocality (m : Model Λ) : Prop := ∀ l, Shared.NoSignaling (m.response l)
/-- Optional screening-off law; not required in the LF profile. -/
def OutcomeIndependent (m : Model Λ) : Prop := ∀ l x y a b,
  (m.response l).prob (x,y) (a,b) =
    (∑ b', (m.response l).prob (x,y) (a,b')) * (∑ a', (m.response l).prob (x,y) (a',b))
def vocabulary : Vocabulary (Model Λ) where
  realism := OutcomeIndependent
  globalTruth := ReadableRecords
  locality := ConditionalLocality
  measurementIndependent := IndependentPreparation
def profile : AssumptionProfile := ⟨.unspecified, .require, .require, .require⟩

theorem moment_identity (p : Behavior LF.interface) (h : Shared.NoSignaling p)
    (x y : Fin 3) (a b : Bool) :
    p.prob (x,y) (a,b) =
      (1 + RealQuantum.sign a * RealQuantum.marginalA p x 0 +
        RealQuantum.sign b * RealQuantum.marginalB p 0 y +
        RealQuantum.sign a * RealQuantum.sign b * RealQuantum.correlator p x y)/4 := by
  rw [Shared.marginalA_independent p h x 0 y, Shared.marginalB_independent p h 0 x y]
  have hn := p.normalized (x,y)
  simp [Fintype.sum_prod_type] at hn
  cases a <;> cases b <;>
    simp [RealQuantum.sign, RealQuantum.marginalA, RealQuantum.marginalB,
      RealQuantum.correlator, Fintype.sum_prod_type] <;> linarith

theorem record_momentA (m : Model Λ) (hr : ReadableRecords m) (l : Λ) :
    RealQuantum.marginalA (m.response l) 0 0 = LF.sign (m.charlie l) := by
  have h := hr.1 l 0
  have hn := (m.response l).normalized (0,0)
  cases hc : m.charlie l <;>
    simp [RealQuantum.marginalA, RealQuantum.sign, LF.sign, Fintype.sum_prod_type, hc] at * <;> linarith

theorem record_momentB (m : Model Λ) (hr : ReadableRecords m) (l : Λ) :
    RealQuantum.marginalB (m.response l) 0 0 = LF.sign (m.debbie l) := by
  have h := hr.2 l 0
  have hn := (m.response l).normalized (0,0)
  cases hd : m.debbie l <;>
    simp [RealQuantum.marginalB, RealQuantum.sign, LF.sign, Fintype.sum_prod_type, hd] at * <;> linarith

theorem record_corrA (m : Model Λ) (hr : ReadableRecords m)
    (hl : ConditionalLocality m) (l : Λ) (y : Fin 3) :
    RealQuantum.correlator (m.response l) 0 y =
      LF.sign (m.charlie l) * RealQuantum.marginalB (m.response l) 0 y := by
  have ha := record_momentA m hr l
  have h1 := Shared.moment_positive (m.response l) (hl l) 0 y false false
  have h2 := Shared.moment_positive (m.response l) (hl l) 0 y false true
  have h3 := Shared.moment_positive (m.response l) (hl l) 0 y true false
  have h4 := Shared.moment_positive (m.response l) (hl l) 0 y true true
  cases hc : m.charlie l <;> simp [LF.sign, RealQuantum.sign, hc] at * <;> linarith

theorem record_corrB (m : Model Λ) (hr : ReadableRecords m)
    (hl : ConditionalLocality m) (l : Λ) (x : Fin 3) :
    RealQuantum.correlator (m.response l) x 0 =
      RealQuantum.marginalA (m.response l) x 0 * LF.sign (m.debbie l) := by
  have hb := record_momentB m hr l
  have h1 := Shared.moment_positive (m.response l) (hl l) x 0 false false
  have h2 := Shared.moment_positive (m.response l) (hl l) x 0 false true
  have h3 := Shared.moment_positive (m.response l) (hl l) x 0 true false
  have h4 := Shared.moment_positive (m.response l) (hl l) x 0 true true
  cases hd : m.debbie l <;> simp [LF.sign, RealQuantum.sign, hd] at * <;> linarith

def component (m : Model Λ) (hl : ConditionalLocality m) (l : Λ) : LF.Component where
  charlie := m.charlie l
  debbie := m.debbie l
  alice x := RealQuantum.marginalA (m.response l) ⟨x.val+1, by omega⟩ 0
  bob y := RealQuantum.marginalB (m.response l) 0 ⟨y.val+1, by omega⟩
  corr x y := RealQuantum.correlator (m.response l) ⟨x.val+1, by omega⟩ ⟨y.val+1, by omega⟩
  positive x y a b := by
    simpa [LF.sign, RealQuantum.sign] using
      Shared.moment_positive (m.response l) (hl l) ⟨x.val+1, by omega⟩ ⟨y.val+1, by omega⟩ a b

theorem component_probability (m : Model Λ) (hr : ReadableRecords m)
    (hl : ConditionalLocality m) (l : Λ) (s : LF.interface.Setting) (o : Bool × Bool) :
    (component m hl l).prob s o = (m.response l).prob s o := by
  have ha (x : Fin 3) : (component m hl l).a x = RealQuantum.marginalA (m.response l) x 0 := by
    fin_cases x <;> simp [LF.Component.a, component, record_momentA m hr l]
  have hb (y : Fin 3) : (component m hl l).b y = RealQuantum.marginalB (m.response l) 0 y := by
    fin_cases y <;> simp [LF.Component.b, component, record_momentB m hr l]
  have he (x y : Fin 3) : (component m hl l).e x y = RealQuantum.correlator (m.response l) x y := by
    fin_cases x <;> fin_cases y <;>
      simp [LF.Component.e, LF.Component.a, LF.Component.b, component, record_corrA m hr hl l,
        record_corrB m hr hl l, record_momentB m hr l]
  rw [moment_identity (m.response l) (hl l) s.1 s.2 o.1 o.2]
  simp only [LF.Component.prob, ha, hb, he, LF.sign, RealQuantum.sign]

def Model.toLF (m : Model Λ) (hl : ConditionalLocality m) : LF.Model Λ where
  weight := (m.preparation (0,0)).mass
  nonneg := (m.preparation (0,0)).nonneg
  normalized := (m.preparation (0,0)).total
  component := component m hl

theorem probability_preserved (m : Model Λ) (hr : ReadableRecords m)
    (hl : ConditionalLocality m) (hi : IndependentPreparation m) : (m.toLF hl).behavior = m.behavior := by
  have he : (m.toLF hl).behavior.prob = m.behavior.prob := by
    funext s o
    simp only [LF.Model.behavior, Model.toLF, Model.behavior]
    simp_rw [component_probability m hr hl, hi s (0,0)]
  cases ha : (m.toLF hl).behavior
  cases hb : m.behavior
  simp only [ha, hb] at he
  cases he
  rfl

def bridge : ProfileBridge (Model Λ) vocabulary profile Model.behavior LF.theory where
  sound m h := ⟨Λ, inferInstance, m.toLF h.2.2.1, probability_preserved m h.2.1 h.2.2.1 h.2.2.2⟩
def question : Question := ⟨LF.interface, RealQuantum.genuineLF⟩
def certified : ProfileBound question (vocabulary (Λ := Λ)) profile Model.behavior :=
  ⟨LF.theory, bridge, LF.genuineBound⟩
theorem bound (m : Model Λ) (hr : ReadableRecords m)
    (hl : ConditionalLocality m) (hi : IndependentPreparation m) : RealQuantum.genuineLF m.behavior ≤ 6 :=
  certified.valid m ⟨trivial, hr, hl, hi⟩
theorem singlet_excludes : ¬ profileTheory (vocabulary (Λ := Λ)) profile Model.behavior RealQuantum.lfBehavior :=
  bridge.excludes _ LF.quantumSeparation.excludes
end
end OntologySeparation.FriendRecords
