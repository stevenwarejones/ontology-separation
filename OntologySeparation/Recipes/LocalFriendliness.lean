import OntologySeparation.Operational.FriendProtocol
import OntologySeparation.Operational.FriendRecords

/-! A fixed four-register friend experiment. Record noise acts after coherent
premeasurement and before each laboratory's read-or-reverse choice. -/
namespace OntologySeparation.LocalFriendlinessRecipe
open TwoQubit

structure Law where
  charlie : Recipes.Rate
  debbie : Recipes.Rate

def Law.coherent : Law := ⟨.of 0, .of 0⟩
def Law.recordDephasing (charlieNumerator debbieNumerator denominator : Nat)
    (positive : 0 < denominator := by decide)
    (charlieBound : charlieNumerator ≤ denominator := by decide)
    (debbieBound : debbieNumerator ≤ denominator := by decide) : Law :=
  ⟨Recipes.Rate.fraction charlieNumerator denominator positive charlieBound,
   Recipes.Rate.fraction debbieNumerator denominator positive debbieBound⟩

/-- Setting zero always reads the friend's record; alternatives reverse the copy. -/
structure Alternatives where
  first : Basis
  second : Basis

def Alternatives.choice (s : Alternatives) (x : Fin 3) : FriendProtocol.Choice :=
  if x.val = 0 then .readRecord else if x.val = 1 then .reverse s.first else .reverse s.second

structure Recipe where
  source : Pure
  alice : Alternatives
  bob : Alternatives

/-- Exact compressed representation of the record channel. The physical identity
recordZ_encoded identifies each ensemble branch with Z on the corresponding record. -/
def recorded (law : Law) (r : Recipe) : State :=
  ((State.pure r.source).dephase .alice law.charlie).dephase .bob law.debbie

/-- The four-register experiment, with all unreported registers summed out. -/
def physicalProbability (law : Law) (r : Recipe) (xy : Fin 3 × Fin 3) (ab : Bool × Bool) : ℚ :=
  FriendProtocol.probability (recorded law r) (r.alice.choice xy.1) (r.bob.choice xy.2) ab.1 ab.2

/-- Fast exact evaluator; equality to the explicit record protocol is proved below. -/
def probability (law : Law) (r : Recipe) (xy : Fin 3 × Fin 3) (ab : Bool × Bool) : ℚ :=
  (readout (recorded law r) (r.alice.choice xy.1).basis (r.bob.choice xy.2).basis).probability ab

theorem probability_correct (law : Law) (r : Recipe) (xy : Fin 3 × Fin 3) (ab : Bool × Bool) :
    physicalProbability law r xy ab = probability law r xy ab :=
  FriendProtocol.probability_bridge _ _ _ _ _

noncomputable def interpret (law : Law) (r : Recipe) : Behavior LF.interface where
  prob xy ab := (physicalProbability law r xy ab : ℝ)
  nonneg xy ab := by
    rw [probability_correct]
    exact_mod_cast (readout (recorded law r) (r.alice.choice xy.1).basis (r.bob.choice xy.2).basis).nonneg ab
  normalized xy := by
    simp_rw [probability_correct]
    have h := (readout (recorded law r) (r.alice.choice xy.1).basis (r.bob.choice xy.2).basis).normalized
    simpa only [probability, Fintype.sum_prod_type, Fintype.sum_bool, Rat.cast_add, Rat.cast_one] using
      congrArg (fun q : ℚ => (q : ℝ)) h

theorem no_signaling (law : Law) (r : Recipe) : Shared.NoSignaling (interpret law r) := by
  constructor
  · intro x y y' a
    simp only [interpret, probability_correct, probability, readout]
    have h := State.alice_marginal ((recorded law r).gate (.readBasis .alice (r.alice.choice x).basis))
    have he := (h (r.bob.choice y).basis a).trans (h (r.bob.choice y').basis a).symm
    simpa only [Fintype.sum_bool, Rat.cast_add] using congrArg (fun q : ℚ => (q : ℝ)) he
  · intro x x' y b
    simp only [interpret, probability_correct, probability, readout, State.read_commute (recorded law r)]
    have h := State.bob_marginal ((recorded law r).gate (.readBasis .bob (r.bob.choice y).basis))
    have he := (h (r.alice.choice x).basis b).trans (h (r.alice.choice x').basis b).symm
    simpa only [Fintype.sum_bool, Rat.cast_add] using congrArg (fun q : ℚ => (q : ℝ)) he

def sign (b : Bool) : ℚ := if b then -1 else 1
def marginalA (m : Law) (r : Recipe) (x y : Fin 3) : ℚ :=
  ∑ o : Bool × Bool, sign o.1 * probability m r (x,y) o
def marginalB (m : Law) (r : Recipe) (x y : Fin 3) : ℚ :=
  ∑ o : Bool × Bool, sign o.2 * probability m r (x,y) o
def correlation (m : Law) (r : Recipe) (x y : Fin 3) : ℚ :=
  ∑ o : Bool × Bool, sign o.1 * sign o.2 * probability m r (x,y) o

def score (m : Law) (r : Recipe) : ℚ :=
  -marginalA m r 0 0 - marginalA m r 1 0 - marginalB m r 0 0 - marginalB m r 0 1
  -correlation m r 0 0 - 2*correlation m r 0 1 - 2*correlation m r 1 0
  +2*correlation m r 1 1 - correlation m r 1 2 - correlation m r 2 1 - correlation m r 2 2

theorem score_correct (law : Law) (r : Recipe) :
    RealQuantum.genuineLF (interpret law r) = (score law r : ℝ) := by
  simp [RealQuantum.genuineLF, RealQuantum.marginalA, RealQuantum.marginalB,
    RealQuantum.correlator, interpret, probability_correct, score, marginalA, marginalB,
    correlation, sign, RealQuantum.sign, Fintype.sum_prod_type]

theorem excludes_LF (law : Law) (r : Recipe) (violation : 6 < score law r) :
    ¬ LF.theory (interpret law r) := by
  intro h
  have hb := LF.genuineBound.valid _ h
  change RealQuantum.genuineLF (interpret law r) ≤ 6 at hb
  rw [score_correct] at hb
  have hv : (6 : ℝ) < (score law r : ℝ) := by exact_mod_cast violation
  exact (not_lt_of_ge hb) hv

theorem excludes_profile {Λ : Type} [Fintype Λ] (law : Law) (r : Recipe)
    (violation : 6 < score law r) :
    ¬ profileTheory (FriendRecords.vocabulary (Λ := Λ)) FriendRecords.profile
      FriendRecords.Model.behavior (interpret law r) :=
  FriendRecords.bridge.excludes _ (excludes_LF law r violation)

noncomputable def scenario : Scenario Law Recipe := ⟨FriendRecords.question, interpret⟩
def predictions : Scenario.ExactPredictions scenario := ⟨score, score_correct⟩

/-- Singlet rotated into the two friends' local Z frames; Bob's original friend
basis is (4,-3). The unnormalized source has squared norm 50. -/
def reference : Recipe :=
  { source := .of (-3) 4 (-4) (-3)
    alice := ⟨.of 3 (-4), .z⟩
    bob := ⟨.of 4 3, .of 84 13⟩ }

def Law.label (m : Law) : String := s!"Record Z-dephasing: Charlie p={m.charlie.value}, Debbie p={m.debbie.value}"
def Recipe.label (r : Recipe) : String :=
  s!"source ray({r.source.vector.a},{r.source.vector.b},{r.source.vector.c},{r.source.vector.d}); setting 0: read record; reverse/read A1={r.alice.first.label}, A2={r.alice.second.label}, B1={r.bob.first.label}, B2={r.bob.second.label}"
def compare (title : String) (laws : List Law) (recipes : List Recipe)
    (hm : laws ≠ [] := by simp) (hp : recipes ≠ [] := by simp) : Scenario.Comparison scenario where
  title := title
  description := "Genuine three-setting LF score G (ceiling 6 for the LF assumption class). Two systems and two coherent qubit records: copy in Z, apply record noise, then read the record (setting 0) or reverse its copy and measure the system (settings 1,2). Unreported registers are summed out, without postselection. Exact real-amplitude model predictions, not laboratory results or claims about conscious observers. Above 6 excludes the conjunction of absolute readable records, conditional locality and independent preparation; below 6 does not prove that conjunction."
  models := laws.map fun m => (m.label,m)
  protocols := recipes.map fun r => (r.label,r)
  models_nonempty := by simpa using hm
  protocols_nonempty := by simpa using hp
  predictions := predictions

macro "lf_check" : tactic =>
  `(tactic| norm_num [score, marginalA, marginalB, correlation, sign, probability, recorded,
    Alternatives.choice, FriendProtocol.Choice.basis, reference, readout,
    State.dephase, State.gate, State.probability, Pure.probability, Pure.gate, Pure.of,
    Gate.apply, Amplitudes.entry, Amplitudes.normSq, Basis.of, Basis.z,
    Law.coherent, Law.recordDephasing, Recipes.Rate.of, Recipes.Rate.fraction,
    Fintype.sum_prod_type])

end OntologySeparation.LocalFriendlinessRecipe
