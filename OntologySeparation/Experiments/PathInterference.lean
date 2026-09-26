import OntologySeparation.Core.FiniteModels
import OntologySeparation.Core.ExperimentAccess
import Mathlib.Tactic.NormNum

/-! An exact two-path, two-phase illustration for the Wen data audit.
This is NOT a model of that apparatus or a certificate about its observations.
The amplitudes describe an ideal balanced interferometer at phases 0 and pi.
The excluded class is explicitly incoherent; a context-dependent response model
is separately exhibited with exactly the coherent probabilities. -/
namespace OntologySeparation.PathInterference
noncomputable section
open FiniteModels ExperimentAccess

abbrev interface : Interface := { Setting := Bool, Outcome := Bool }

/-- Contributions of the two routes, including both beam splitters. -/
def amplitude (phase detector route : Bool) : ℝ :=
  if route then (if detector = phase then 1 / 2 else -(1 / 2)) else 1 / 2

/-- Coherent addition before taking the square. -/
def pathProbability (phase detector : Bool) : ℝ :=
  (∑ route : Bool, amplitude phase detector route) ^ 2

/-- The same elementary transfer calculation, without an intermediate path sum. -/
def transferProbability (phase detector : Bool) : ℝ :=
  ((1 + (if detector = phase then 1 else -1)) / 2) ^ 2

theorem path_eq_transfer (s o : Bool) :
    pathProbability s o = transferProbability s o := by
  cases s <;> cases o <;>
    norm_num [pathProbability, transferProbability, amplitude, Fintype.sum_bool]

theorem path_probability (s o : Bool) :
    pathProbability s o = if o = s then 1 else 0 := by
  cases s <;> cases o <;> norm_num [pathProbability, amplitude, Fintype.sum_bool]

def coherent : Behavior interface where
  prob := pathProbability
  nonneg s o := sq_nonneg _
  normalized s := by
    cases s <;> norm_num [interface, Fintype.sum_bool, path_probability]

/-- Each separately populated route reaches either detector with probability 1/2.
The factor two conditions on that input route. -/
def routeBehavior (route : Bool) : Behavior interface where
  prob s o := 2 * amplitude s o route ^ 2
  nonneg s o := mul_nonneg (by norm_num) (sq_nonneg _)
  normalized s := by
    change (∑ o : Bool, 2 * amplitude s o route ^ 2) = 1
    cases route <;> cases s <;> norm_num [amplitude, Fintype.sum_bool]

theorem route_probability (route s o : Bool) :
    (routeBehavior route).prob s o = 1 / 2 := by
  cases route <;> cases s <;> cases o <;> norm_num [routeBehavior, amplitude]

def incoherent : Behavior interface := routeBehavior false

def bright (_ : Bool) (o : Bool) : ℝ := if o then 1 else 0

/-- Score uses one phase setting, not a sum over both complementary settings. -/
def coefficient (s o : Bool) : ℝ := if s then bright s o else 0

theorem route_score (r : Bool) : score coefficient (routeBehavior r) = 1 / 2 := by
  simp [score, interface, coefficient, bright, route_probability]

theorem coherent_score : score coefficient coherent = 1 := by
  norm_num [score, interface, coefficient, bright, coherent, Fintype.sum_bool,
    path_probability]

def incoherentExclusion : Exclusion routeBehavior coherent where
  coefficients := coefficient
  ceiling := 1 / 2
  valid r := by rw [route_score]
  violation := by rw [coherent_score]; norm_num

theorem excludes_incoherent : ¬ Compatible routeBehavior coherent :=
  incoherentExclusion.excludes

theorem incoherent_class_nonempty : Compatible routeBehavior incoherent :=
  (generatorMembership routeBehavior false).compatible

/-- An explicit deterministic response to the full setting. This is a
context-dependent simulator, not a proposed photon trajectory or noncontextual model. -/
def response (table : Bool → Bool) : Behavior interface where
  prob s o := if o = table s then 1 else 0
  nonneg s o := by split_ifs <;> norm_num
  normalized s := by
    change (∑ o : Bool, if o = table s then (1 : ℝ) else 0) = 1
    cases table s <;> simp

theorem contextual_response_matches : ObservationallyEquivalent (response id) coherent := by
  intro s o
  simp [response, coherent, path_probability]

/-- The enlarged, explicitly defined response class contains the same target. -/
def contextualMembership : Membership response coherent where
  weights := (generatorMembership response id).weights
  reproduces s o := (generatorMembership response id).reproduces s o |>.trans
    (contextual_response_matches s o)

inductive Description | pathSum | transfer | dephased

/-- false means dephased access; true retains interference. -/
def predict : Predictions Description Bool interface
  | .pathSum, p => if p then coherent else incoherent
  | .transfer, p => if p then {
      prob := transferProbability
      nonneg s o := sq_nonneg _
      normalized s := by
        change (∑ o : Bool, transferProbability s o) = 1
        simpa only [← path_eq_transfer] using coherent.normalized s } else incoherent
  | .dephased, _ => incoherent

theorem descriptions_equivalent : Equivalent predict (fun _ => True)
    .pathSum .transfer := by
  intro p _ s o
  cases p
  · rfl
  · exact path_eq_transfer s o

theorem restricted_equivalent : Equivalent predict (fun p => p = false)
    .pathSum .dephased := by
  intro p hp s o
  subst p
  rfl

def interferenceSeparator : Separator predict (fun _ => True) .pathSum .dephased where
  protocol := true
  accessible := trivial
  setting := true
  outcome := true
  gap := 1 / 2
  positive := by norm_num
  difference := by
    norm_num [predict, coherent, incoherent, path_probability, route_probability]

theorem expanded_not_equivalent : ¬ Equivalent predict (fun _ => True)
    .pathSum .dephased := interferenceSeparator.not_equivalent

end
end OntologySeparation.PathInterference
