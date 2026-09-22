import OntologySeparation.Core.FiniteModels
import OntologySeparation.Core.Claim
import OntologySeparation.Experiments.RecordAccess

/-! Two examples: a whole-table membership witness, and a model which passes a
selected score but is outside the model class. Also lift the record experiment's
point separation to every mixture of specified dephased preparations. -/
namespace OntologySeparation.ModelCompatibility
noncomputable section
open FiniteModels

abbrev interface : Interface := { Setting := Bool, Outcome := Bool }

/-- A fixed classical bit, read identically under either setting. -/
def fixed (bit : Bool) : Behavior interface where
  prob _ o := if o = bit then 1 else 0
  nonneg _ o := by split_ifs <;> norm_num
  normalized _ := by cases bit <;> norm_num [interface, Fintype.sum_bool]

/-- A fair shared bit is compatible, including both outcomes under both settings. -/
def fair : Behavior interface where
  prob _ _ := 1 / 2
  nonneg _ _ := by norm_num
  normalized _ := by
    change (∑ _ : Bool, (1/2 : ℝ)) = 1
    norm_num

def fairMembership : Membership fixed fair where
  weights := {
    mass := fun _ => 1 / 2
    nonneg := fun _ => by norm_num
    total := by norm_num [interface, Fintype.sum_bool] }
  reproduces s o := by cases o <;> norm_num [interface, mixture, fixed, fair, Fintype.sum_bool]

/-- The device reports its setting. This is a valid behavior, but not a mixture
of setting-independent fixed bits. -/
def settingEcho : Behavior interface where
  prob s o := if o = s then 1 else 0
  nonneg s o := by split_ifs <;> norm_num
  normalized s := by cases s <;> norm_num [interface, Fintype.sum_bool]

def contrast (s o : Bool) : ℝ := if o then (if s then 1 else -1) else 0

theorem fixed_contrast (bit : Bool) : score contrast (fixed bit) = 0 := by
  change (∑ s : Bool, ∑ o : Bool, contrast s o * (fixed bit).prob s o) = 0
  cases bit <;> norm_num [contrast, fixed, Fintype.sum_bool]

theorem echo_contrast : score contrast settingEcho = 1 := by
  norm_num [interface, score, contrast, settingEcho, Fintype.sum_bool]

def echoExclusion : Exclusion fixed settingEcho where
  coefficients := contrast
  ceiling := 0
  valid bit := by rw [fixed_contrast]
  violation := by rw [echo_contrast]; norm_num

theorem echo_not_compatible : ¬ Compatible fixed settingEcho := echoExclusion.excludes

/-- The opposite side of the same equality is a valid but insufficient inequality. -/
def oppositeContrast (s o : Bool) : ℝ := -contrast s o

/-- The target passes a nontrivial valid model bound but fails another one. -/
theorem passes_one_bound_but_excluded :
    (∀ bit, score oppositeContrast (fixed bit) ≤ 0) ∧
    score oppositeContrast settingEcho ≤ 0 ∧ ¬ Compatible fixed settingEcho := by
  constructor
  · intro bit
    change (∑ s : Bool, ∑ o : Bool, oppositeContrast s o * (fixed bit).prob s o) ≤ 0
    cases bit <;> norm_num [oppositeContrast, contrast, fixed, Fintype.sum_bool]
  constructor
  · norm_num [interface, score, oppositeContrast, contrast, settingEcho, Fintype.sum_bool]
  · exact echo_not_compatible

/-- Explicit proof-bearing reports use the same Claim boundary as the main matrix. -/
def fairClaim : Claim := .theoremResult (Compatible fixed fair) fairMembership.compatible
def echoClaim : Claim := .exclusion (Compatible fixed) settingEcho echo_not_compatible

/-- A class of dephased preparations. Both outcomes are counted; no postselection.
These are the |00> and |11> states, whose convex hull includes every fully dephased
state in the correlated record subspace, not every conceivable collapse model. -/
def recordBasis (bit : Bool) : QIT.PureVector RecordAccess.Registers where
  amp i := if i = (bit,bit) then 1 else 0
  trace_rankOne_eq_one := by
    cases bit <;> norm_num [interface, QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
      Fintype.sum_prod_type, Fintype.sum_bool]

abbrev recordInterface : Interface := { Setting := Unit, Outcome := RecordAccess.Registers }

def recordGenerator (bit : Bool) : Behavior recordInterface :=
  FiniteQuantum.behavior (recordBasis bit).state (fun _ => RecordAccess.recoveryTest)

def recordTarget : Behavior recordInterface :=
  FiniteQuantum.behavior RecordAccess.coherent (fun _ => RecordAccess.recoveryTest)

def recoveryCoefficient (_ : Unit) (o : RecordAccess.Registers) : ℝ :=
  if o = (false,false) then 1 else 0

theorem recovery_score (p : Behavior recordInterface) :
    score recoveryCoefficient p = p.prob () (false,false) := by
  simp [score, recoveryCoefficient]

theorem basis_success (bit : Bool) :
    (recordGenerator bit).prob () (false,false) = if bit then 16/25 else 9/25 := by
  change RecordAccess.recoveryTest.prob (recordBasis bit).state (false,false) = _
  rw [RecordAccess.recoveryTest, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  cases bit <;> norm_num [interface, recordBasis, QIT.PureVector.state, QIT.rankOneMatrix,
    Matrix.vecMulVec, RecordAccess.recoveryReadout, QIT.POVM.compressByIsometry,
    QIT.POVM.coordinate, RecordAccess.recovery, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single, Fintype.sum_prod_type, Fintype.sum_bool,
    Complex.div_re, Complex.div_im]

/-- One intervention excludes every mixture of these dephased preparations. -/
def recordClassExclusion : Exclusion recordGenerator recordTarget where
  coefficients := recoveryCoefficient
  ceiling := 16 / 25
  valid bit := by rw [recovery_score, basis_success]; cases bit <;> norm_num
  violation := by
    rw [recovery_score]
    change 16 / 25 < RecordAccess.recoveryTest.prob RecordAccess.coherent (false,false)
    rw [RecordAccess.coherent_recovery]
    norm_num

theorem coherent_excludes_dephased_class : ¬ Compatible recordGenerator recordTarget :=
  recordClassExclusion.excludes

def recordBoundClaim : Claim :=
  .realizedBound (Compatible recordGenerator) (score recoveryCoefficient) (16/25)
    (by
      intro target h
      convert compatible_bound recoveryCoefficient recordGenerator (16/25)
        recordClassExclusion.valid target h using 1; norm_num)
    (recordGenerator false) (generatorMembership recordGenerator false).compatible

def recordClassClaim : Claim :=
  .exclusion (Compatible recordGenerator) recordTarget coherent_excludes_dephased_class
end
end OntologySeparation.ModelCompatibility
