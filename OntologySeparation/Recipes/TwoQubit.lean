import OntologySeparation.Operational.TwoQubit
import OntologySeparation.Experiments.Bell

/-! Two-wire, two-setting Bell recipes with exact predictions. Gates are preparation
operations before the separated setting choices. Exposure alone depends on Law. -/
namespace OntologySeparation.TwoQubit

inductive Preparation where
  | product (alice bob : Bool)
  | bellPlus | singlet
  | custom (state : Pure)

def Preparation.state : Preparation → State
  | .product false false => .pure (.of 1 0 0 0)
  | .product false true => .pure (.of 0 1 0 0)
  | .product true false => .pure (.of 0 0 1 0)
  | .product true true => .pure (.of 0 0 0 1)
  | .bellPlus => .pure (.of 1 0 0 1)
  | .singlet => .pure (.of 0 1 (-1) 0)
  | .custom v => .pure v

structure Law where
  alice : Recipes.Rate
  bob : Recipes.Rate

def Law.ideal : Law := ⟨.of 0, .of 0⟩
/-- Local Z dephasing strengths for an exposure of the corresponding wire. -/
def Law.dephasing (aliceNumerator bobNumerator denominator : Nat)
    (positive : 0 < denominator := by decide)
    (aliceBound : aliceNumerator ≤ denominator := by decide)
    (bobBound : bobNumerator ≤ denominator := by decide) : Law :=
  ⟨Recipes.Rate.fraction aliceNumerator denominator positive aliceBound,
   Recipes.Rate.fraction bobNumerator denominator positive bobBound⟩

def Law.rate (m : Law) : Wire → Recipes.Rate
  | .alice => m.alice | .bob => m.bob

inductive Operation where
  | h (wire : Wire) | x (wire : Wire) | z (wire : Wire)
  | cnot (control : Wire) | swap
  | expose (wire : Wire)
  | dephase (wire : Wire) (rate : Recipes.Rate)

structure Settings where
  first : Basis
  second : Basis

def Settings.at (s : Settings) (i : Fin 2) : Basis := if i.val = 0 then s.first else s.second

structure Recipe where
  prepare : Preparation
  steps : List Operation := []
  alice : Settings
  bob : Settings

def Operation.apply (law : Law) : Operation → State → State
  | .h w, v => v.gate (.h w)
  | .x w, v => v.gate (.x w)
  | .z w, v => v.gate (.z w)
  | .cnot w, v => v.gate (.cnot w)
  | .swap, v => v.gate .swap
  | .expose w, v => v.dephase w (law.rate w)
  | .dephase w p, v => v.dephase w p

def run (law : Law) : List Operation → State → State
  | [], v => v
  | op :: rest, v => run law rest (op.apply law v)

def Recipe.state (law : Law) (r : Recipe) : State := run law r.steps r.prepare.state

def readout (v : State) (a b : Basis) : State :=
  (v.gate (.readBasis .alice a)).gate (.readBasis .bob b)

/-- Joint probability; false is the +1 outcome, true the -1 outcome. -/
def probability (law : Law) (r : Recipe) (xy : Fin 2 × Fin 2) (ab : Bool × Bool) : ℚ :=
  (readout (r.state law) (r.alice.at xy.1) (r.bob.at xy.2)).probability ab

/-- All recipes obey no signaling at measurement, for every supported law. -/
theorem no_signaling_alice (law : Law) (r : Recipe) (x y y' : Fin 2) (a : Bool) :
    ∑ b : Bool, probability law r (x,y) (a,b) =
      ∑ b : Bool, probability law r (x,y') (a,b) := by
  simp only [probability, readout, State.alice_marginal]

theorem no_signaling_bob (law : Law) (r : Recipe) (x x' y : Fin 2) (b : Bool) :
    ∑ a : Bool, probability law r (x,y) (a,b) =
      ∑ a : Bool, probability law r (x',y) (a,b) := by
  simp only [probability, readout, State.read_commute (r.state law), State.bob_marginal]

noncomputable def interpret (law : Law) (r : Recipe) : Behavior Bell.interface where
  prob xy ab := (probability law r xy ab : ℝ)
  nonneg xy ab := by exact_mod_cast (readout (r.state law) (r.alice.at xy.1) (r.bob.at xy.2)).nonneg ab
  normalized xy := by
    have h := (readout (r.state law) (r.alice.at xy.1) (r.bob.at xy.2)).normalized
    simpa only [probability, Fintype.sum_prod_type, Fintype.sum_bool, Rat.cast_add, Rat.cast_one] using
      congrArg (fun q : ℚ => (q : ℝ)) h

def correlation (law : Law) (r : Recipe) (x y : Fin 2) : ℚ :=
  probability law r (x,y) (false,false) - probability law r (x,y) (false,true)
    - probability law r (x,y) (true,false) + probability law r (x,y) (true,true)

def chsh (law : Law) (r : Recipe) : ℚ :=
  correlation law r 0 0 + correlation law r 0 1 + correlation law r 1 0 - correlation law r 1 1

theorem chsh_correct (law : Law) (r : Recipe) : Bell.score (interpret law r) = (chsh law r : ℝ) := by
  simp [Bell.score, Bell.correlator, interpret, chsh, correlation,
    QIT.Bell.CHSH.outcomeSign, Fintype.sum_prod_type]
  ring

/-- A checked score above two excludes the existing Bell-local model class.
This does not claim that any individual philosophical assumption is false. -/
theorem excludes_local (law : Law) (r : Recipe) (violation : 2 < chsh law r) :
    ¬ Bell.localTheory (interpret law r) := by
  intro h
  have hb := Bell.localBound.valid _ h
  change Bell.score (interpret law r) ≤ 2 at hb
  rw [chsh_correct] at hb
  have hv : (2 : ℝ) < (chsh law r : ℝ) := by exact_mod_cast violation
  exact (not_lt_of_ge hb) hv

noncomputable def scenario : Scenario Law Recipe := ⟨⟨Bell.interface, Bell.score⟩, interpret⟩
def predictions : Scenario.ExactPredictions scenario := ⟨chsh, chsh_correct⟩

def Wire.label : Wire → String | .alice => "Alice" | .bob => "Bob"
def Basis.label (q : Basis) : String := s!"basis({q.c},{q.s})"
def Preparation.label : Preparation → String
  | .product a b => s!"product |{if a then "1" else "0"}{if b then "1" else "0"}>"
  | .bellPlus => "Bell |Phi+>"
  | .singlet => "singlet |Psi->"
  | .custom v => s!"ray({v.vector.a},{v.vector.b},{v.vector.c},{v.vector.d})"
def Operation.label : Operation → String
  | .h w => s!"H({w.label})" | .x w => s!"X({w.label})" | .z w => s!"Z({w.label})"
  | .cnot w => s!"CNOT(control={w.label})" | .swap => "SWAP"
  | .expose w => s!"expose({w.label})"
  | .dephase w p => s!"dephase({w.label},p={p.value})"
def Law.label (m : Law) : String := s!"Z dephasing per exposure: Alice p={m.alice.value}, Bob p={m.bob.value}"
def Recipe.label (r : Recipe) : String :=
  String.intercalate "; " ([r.prepare.label] ++ r.steps.map Operation.label ++
    [s!"A0={r.alice.first.label}, A1={r.alice.second.label}",
     s!"B0={r.bob.first.label}, B1={r.bob.second.label}"])

def compare (title : String) (laws : List Law) (recipes : List Recipe)
    (hm : laws ≠ [] := by simp) (hp : recipes ≠ [] := by simp) : Scenario.Comparison scenario where
  title := title
  description := "Exact CHSH E00+E01+E10-E11 from normalized two-qubit Born probabilities (false=+1, true=-1). Real amplitudes and local projective measurements. Gates prepare the state before separated setting choices. Only explicit exposure steps vary with the row's local Z-dephasing law; p=1 is full dephasing. The Bell-local ceiling is 2; a larger calculated value excludes that class for this mathematical behavior, not from laboratory data."
  models := laws.map fun m => (m.label, m)
  protocols := recipes.map fun r => (r.label, r)
  models_nonempty := by simpa using hm
  protocols_nonempty := by simpa using hp
  predictions := predictions

/-- Rational settings matching the existing 1502/625 singlet witness. -/
def bellSettingsAlice : Settings := ⟨.of 4 (-3), .of 3 (-4)⟩
-- Bob's second vector is (0,1), reversing the Z outcome labels.
def bellSettingsBob : Settings := ⟨.of 4 3, .of 0 1⟩
def singletRecipe : Recipe :=
  { prepare := .singlet, alice := bellSettingsAlice, bob := bellSettingsBob }

macro "two_qubit_check" : tactic =>
  `(tactic| norm_num [chsh, correlation, probability, readout, Recipe.state, run,
    Operation.apply, Preparation.state, State.gate, State.dephase, State.probability,
    Pure.probability, Pure.gate, Pure.of, Gate.apply, Amplitudes.normSq, Amplitudes.entry,
    Settings.at, Basis.of, Basis.x, Basis.z, Law.rate, Law.ideal, Law.dephasing,
    Recipes.Rate.fraction, Recipes.Rate.of, bellSettingsAlice, bellSettingsBob,
    singletRecipe])

-- Agreement of ALL 16 probabilities, not just the final Bell number.
theorem singlet_matches_reference (xy : Fin 2 × Fin 2) (ab : Bool × Bool) :
    (interpret Law.ideal singletRecipe).prob xy ab = Bell.singletBehavior.prob xy ab := by
  obtain ⟨x,y⟩ := xy
  obtain ⟨a,b⟩ := ab
  fin_cases x <;> fin_cases y <;> cases a <;> cases b <;>
    norm_num [interpret, probability, readout, Recipe.state, run, Preparation.state,
      State.gate, State.probability, Pure.probability, Pure.gate, Pure.of,
      Gate.apply, Amplitudes.normSq, Amplitudes.entry, Settings.at, Basis.of,
      singletRecipe, bellSettingsAlice, bellSettingsBob,
      Bell.singletBehavior, RealQuantum.behavior, RealQuantum.probability,
      RealQuantum.Basis.vector, Bell.alice, Bell.bob, Bell.b43, Bell.b01,
      RealQuantum.basis35, RealQuantum.basis45]

/-- The explicit preparation circuit creates the singlet for every law.
No exposure occurs in this preparation stage. -/
theorem prepare_singlet_circuit (law : Law) :
    run law [.h .alice, .cnot .alice, .x .bob, .z .alice]
      (Preparation.product false false).state = Preparation.singlet.state := by
  simp only [run, Operation.apply, Preparation.state, State.gate]
  congr 1
  ext <;> norm_num [Pure.gate, Pure.of, Gate.apply]

end OntologySeparation.TwoQubit
