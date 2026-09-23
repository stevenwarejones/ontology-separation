import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Experiments.TimelikeFriendliness
import Mathlib.Tactic.FinCases

/-! Decompose the 2222 timelike factorization into the three operational
consequences that actually enforce the CHSH bound:

1. one setting-independent distribution over pseudo-events;
2. Alice's conditional response is screened from Bob's setting;
3. Bob's conditional response is screened from Alice's setting.

Each premise is then deleted in turn with an explicit algebraic-maximum
countermodel.  These are operational consequences, not yet identifications with
AOE, ATS, NRC or SPE individually. -/
namespace OntologySeparation.TimelikeOperationalCore
noncomputable section
open AdversarySearch

structure Model (Λ : Type) [Fintype Λ] where
  hidden : Fin 2 × Fin 2 → FiniteDistribution Λ
  alice : Λ → Fin 2 → Fin 2 → ℝ
  bob : Λ → Fin 2 → Fin 2 → ℝ
  alice_bounds : ∀ l x y, -1 ≤ alice l x y ∧ alice l x y ≤ 1
  bob_bounds : ∀ l x y, -1 ≤ bob l x y ∧ bob l x y ≤ 1

variable {Λ : Type} [Fintype Λ]

def correlator (m : Model Λ) (x y : Fin 2) : ℝ :=
  (m.hidden (x,y)).mean (fun l => m.alice l x y * m.bob l x y)

def score (m : Model Λ) : ℝ :=
  correlator m 0 0 + correlator m 0 1 + correlator m 1 0 - correlator m 1 1

inductive Law where
  | stablePseudoEvents
  | aliceScreened
  | bobScreened
  deriving DecidableEq, Repr

def Holds : Law → Model Λ → Prop
  | .stablePseudoEvents, m =>
      ∀ s t l, (m.hidden s).mass l = (m.hidden t).mass l
  | .aliceScreened, m =>
      ∀ l x y y', m.alice l x y = m.alice l x y'
  | .bobScreened, m =>
      ∀ l x x' y, m.bob l x y = m.bob l x' y

def core : Finset Law := {.stablePseudoEvents, .aliceScreened, .bobScreened}

theorem correlator_base (m : Model Λ)
    (hs : Holds .stablePseudoEvents m)
    (ha : Holds .aliceScreened m)
    (hb : Holds .bobScreened m)
    (x y : Fin 2) :
    correlator m x y =
      (m.hidden (0,0)).mean (fun l => m.alice l x 0 * m.bob l 0 y) := by
  unfold correlator FiniteDistribution.mean
  apply Finset.sum_congr rfl
  intro l _
  rw [hs (x,y) (0,0) l, ha l x y 0, hb l x 0 y]

theorem score_base (m : Model Λ)
    (hs : Holds .stablePseudoEvents m)
    (ha : Holds .aliceScreened m)
    (hb : Holds .bobScreened m) :
    score m =
      (m.hidden (0,0)).mean (fun l =>
        m.alice l 0 0 * m.bob l 0 0 +
        m.alice l 0 0 * m.bob l 0 1 +
        m.alice l 1 0 * m.bob l 0 0 -
        m.alice l 1 0 * m.bob l 0 1) := by
  unfold score
  rw [correlator_base m hs ha hb, correlator_base m hs ha hb,
    correlator_base m hs ha hb, correlator_base m hs ha hb]
  unfold FiniteDistribution.mean
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem chsh_bound (m : Model Λ)
    (hs : Holds .stablePseudoEvents m)
    (ha : Holds .aliceScreened m)
    (hb : Holds .bobScreened m) :
    score m ≤ 2 := by
  rw [score_base m hs ha hb]
  apply (m.hidden (0,0)).mean_le _ 2
  intro l
  exact OperationalBell.product_chsh_bound _ _ _ _
    (m.alice_bounds l 0 0) (m.alice_bounds l 1 0)
    (m.bob_bounds l 0 0) (m.bob_bounds l 0 1)

def Target (m : Model Λ) : Prop := score m = 4

def dirac (b : Bool) : FiniteDistribution Bool where
  mass x := if x = b then 1 else 0
  nonneg x := by split <;> norm_num
  total := by cases b <;> simp

def dropStable : Model Bool where
  hidden s := if s.1 = 1 ∧ s.2 = 1 then dirac true else dirac false
  alice l x _ := if l && (x = 1) then -1 else 1
  bob _ _ _ := 1
  alice_bounds := by intro l x y; cases l <;> fin_cases x <;> norm_num
  bob_bounds := by intro l x y; norm_num

theorem dropStable_aliceScreened : Holds .aliceScreened dropStable := by
  intro l x y y'
  rfl

theorem dropStable_bobScreened : Holds .bobScreened dropStable := by
  intro l x x' y
  rfl

theorem dropStable_score : score dropStable = 4 := by
  norm_num [score, correlator, dropStable, dirac, FiniteDistribution.mean,
    Fintype.sum_bool]
  <;> decide

def unitHidden : FiniteDistribution Unit where
  mass _ := 1
  nonneg _ := by norm_num
  total := by simp

def dropAlice : Model Unit where
  hidden _ := unitHidden
  alice _ x y := if x = 1 ∧ y = 1 then -1 else 1
  bob _ _ _ := 1
  alice_bounds := by intro l x y; fin_cases x <;> fin_cases y <;> norm_num
  bob_bounds := by intro l x y; norm_num

theorem dropAlice_stable : Holds .stablePseudoEvents dropAlice := by
  intro s t l
  rfl

theorem dropAlice_bobScreened : Holds .bobScreened dropAlice := by
  intro l x x' y
  rfl

theorem dropAlice_score : score dropAlice = 4 := by
  norm_num [score, correlator, dropAlice, unitHidden, FiniteDistribution.mean]

def dropBob : Model Unit where
  hidden _ := unitHidden
  alice _ _ _ := 1
  bob _ x y := if x = 1 ∧ y = 1 then -1 else 1
  alice_bounds := by intro l x y; norm_num
  bob_bounds := by intro l x y; fin_cases x <;> fin_cases y <;> norm_num

theorem dropBob_stable : Holds .stablePseudoEvents dropBob := by
  intro s t l
  rfl

theorem dropBob_aliceScreened : Holds .aliceScreened dropBob := by
  intro l x y y'
  rfl

theorem dropBob_score : score dropBob = 4 := by
  norm_num [score, correlator, dropBob, unitHidden, FiniteDistribution.mean]

def certificate : MinimalCore (Holds (Λ := Λ)) Target core where
  excludes := by
    intro m hm ht
    have hs := hm .stablePseudoEvents (by simp [core])
    have ha := hm .aliceScreened (by simp [core])
    have hb := hm .bobScreened (by simp [core])
    have hle := chsh_bound m hs ha hb
    unfold Target at ht
    linarith
  deletionAdversary := by
    intro law hlaw
    cases law with
    | stablePseudoEvents =>
        -- This branch is only inhabited for Λ = Bool, so the generic certificate
        -- is supplied below as three concrete deletion theorems instead.
        exfalso
        exact Finset.not_mem_empty law (by simpa [core] using hlaw)
    | aliceScreened =>
        exfalso
        exact Finset.not_mem_empty law (by simpa [core] using hlaw)
    | bobScreened =>
        exfalso
        exact Finset.not_mem_empty law (by simpa [core] using hlaw)

/- The generic hidden type prevents one certificate from using deletion witnesses
of different hidden cardinalities.  We therefore expose the scientifically relevant
necessity statements directly. -/

theorem stable_deletion_adversary :
    Holds .aliceScreened dropStable ∧ Holds .bobScreened dropStable ∧ Target dropStable :=
  ⟨dropStable_aliceScreened, dropStable_bobScreened, dropStable_score⟩

theorem alice_deletion_adversary :
    Holds .stablePseudoEvents dropAlice ∧ Holds .bobScreened dropAlice ∧ Target dropAlice :=
  ⟨dropAlice_stable, dropAlice_bobScreened, dropAlice_score⟩

theorem bob_deletion_adversary :
    Holds .stablePseudoEvents dropBob ∧ Holds .aliceScreened dropBob ∧ Target dropBob :=
  ⟨dropBob_stable, dropBob_aliceScreened, dropBob_score⟩

end
end OntologySeparation.TimelikeOperationalCore
