import OntologySeparation.Experiments.ForcedSignalingCompletions

/-!
Exact attaining witnesses for the completion-dependent S4 slopes.

An untrusted LP search was used only to propose the sparse rational weights below.
All weights use denominator 192. Lean checks normalization, the recipient-TV
budget, and the completed score exactly. Consequently the witnesses prove that
the analytic slopes in `ForcedSignalingCompletions` cannot be lowered.
-/

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators
noncomputable section
namespace CompletionWitness

def denominator : ℕ := 192

noncomputable def modelOfCertificate {n : ℕ}
    (atoms : Fin n → Atom) (numerator : Fin n → ℕ)
    (total : ∀ e : Early,
      (∑ k, if early (atoms k) = e then numerator k else 0) = denominator) : Model :=
  Model.ofAtoms atoms (fun k => (numerator k : ℝ) / denominator)
    (fun _ => by positivity)
    (fun e => by
      have h : (∑ k, if early (atoms k) = e then (numerator k : ℝ) else 0) =
          denominator := by exact_mod_cast total e
      have hh := congrArg (fun x : ℝ => x / denominator) h
      simpa [Finset.sum_div, ite_div, denominator] using hh)

def diffNumerator {n : ℕ} (atoms : Fin n → Atom) (numerator : Fin n → ℕ)
    (c : Context) (o : Recipient) : ℤ :=
  ∑ k, differenceCoeff c o (atoms k) * (numerator k : ℤ)

def scoreNumerator {n : ℕ} (atoms : Fin n → Atom) (numerator : Fin n → ℕ)
    (c : Completion) : ℤ :=
  ∑ k, completedScoreCoeff c (atoms k) * (numerator k : ℤ)

theorem modelOfCertificate_difference {n : ℕ}
    (atoms : Fin n → Atom) (numerator : Fin n → ℕ)
    (total) (c : Context) (o : Recipient) :
    difference (modelOfCertificate atoms numerator total).behavior c o =
      (diffNumerator atoms numerator c o : ℝ) / denominator := by
  rw [modelOfCertificate, ofAtoms_difference]
  simp [diffNumerator, denominator, Finset.sum_div, mul_div_assoc,
    Int.cast_sum, Int.cast_mul]

theorem modelOfCertificate_score {n : ℕ}
    (atoms : Fin n → Atom) (numerator : Fin n → ℕ)
    (total) (c : Completion) :
    completedScore c (modelOfCertificate atoms numerator total).behavior =
      (scoreNumerator atoms numerator c : ℝ) / denominator := by
  rw [completedScore_eq, modelOfCertificate]
  rw [atomWeights_sum]
  simp [scoreNumerator, denominator, Finset.sum_div, mul_div_assoc,
    Int.cast_sum, Int.cast_mul]

theorem modelOfCertificate_budget {n : ℕ}
    (atoms : Fin n → Atom) (numerator : Fin n → ℕ)
    (total)
    (habs : ∀ c : Context, (∑ o, |diffNumerator atoms numerator c o|) ≤ 24) :
    Within (modelOfCertificate atoms numerator total).behavior (1/16) := by
  intro c
  unfold tv
  simp_rw [modelOfCertificate_difference atoms numerator total]
  have hreal : (∑ o, |(diffNumerator atoms numerator c o : ℝ)|) ≤ 24 := by
    exact_mod_cast habs c
  have hden : (0 : ℝ) ≤ denominator := by norm_num [denominator]
  simp_rw [abs_div, abs_of_nonneg hden]
  rw [Finset.sum_div]
  norm_num [denominator] at hreal ⊢
  linarith

def p000Atoms (k : Fin 29) : Atom :=
  (#[0,17,19,44,61,63,64,65,82,111,112,124,125,136,149,151,164,165,177,185,187,192,199,216,220,225,235,244,253] : Array Atom)[k.val]
def p000Numerator (k : Fin 29) : ℕ :=
  (#[30,108,6,30,12,6,12,114,6,6,12,30,12,30,12,6,18,12,96,12,6,12,6,18,12,108,6,18,12] : Array ℕ)[k.val]

def p001Atoms (k : Fin 32) : Atom :=
  (#[0,17,19,44,61,63,65,83,111,112,113,124,125,136,149,151,164,177,185,187,193,199,213,216,220,221,225,235,244,249,252,253] : Array Atom)[k.val]
def p001Numerator (k : Fin 32) : ℕ :=
  (#[12,138,6,12,18,6,138,6,6,6,6,12,18,12,18,6,12,120,18,6,6,6,12,6,3,3,126,6,6,12,3,3] : Array ℕ)[k.val]

def p010Atoms (k : Fin 31) : Atom :=
  (#[0,17,19,44,61,63,64,65,68,82,111,120,124,125,136,140,149,151,164,165,185,187,192,199,216,220,225,228,235,244,253] : Array Atom)[k.val]
def p010Numerator (k : Fin 31) : ℕ :=
  (#[24,12,6,132,12,6,12,18,6,6,6,6,126,12,24,108,12,6,12,12,12,6,12,6,12,120,12,6,6,6,12] : Array ℕ)[k.val]

def p011Atoms (k : Fin 30) : Atom :=
  (#[0,17,19,44,61,63,64,65,68,82,111,120,124,125,136,149,151,164,177,185,187,192,199,216,220,225,228,235,244,253] : Array Atom)[k.val]
def p011Numerator (k : Fin 30) : ℕ :=
  (#[18,138,6,18,6,6,6,144,6,6,6,6,12,6,18,6,6,18,132,6,6,6,6,12,6,138,6,6,6,6] : Array ℕ)[k.val]

def p100Atoms (k : Fin 45) : Atom :=
  (#[0,17,19,38,44,61,63,64,65,72,82,83,103,110,111,116,124,125,136,140,149,151,164,165,167,184,185,187,192,193,197,199,200,213,216,220,225,235,238,242,244,246,251,252,253] : Array Atom)[k.val]
def p100Numerator (k : Fin 45) : ℕ :=
  (#[20,12,10,4,124,12,10,6,20,6,8,2,6,3,5,4,121,11,20,104,12,10,15,5,4,3,9,10,6,3,1,10,6,2,5,113,12,5,3,3,8,1,2,3,9] : Array ℕ)[k.val]

def p101Atoms (k : Fin 43) : Atom :=
  (#[0,2,17,19,44,46,61,63,65,72,82,83,103,110,111,124,125,136,138,149,151,164,166,177,185,187,193,197,199,200,202,213,215,216,220,225,233,238,242,244,251,252,253] : Array Atom)[k.val]
def p101Numerator (k : Fin 43) : ℕ :=
  (#[9,3,141,9,9,3,9,9,144,6,6,6,6,3,3,9,9,9,3,9,9,9,3,132,9,9,3,3,6,3,3,3,3,3,3,138,3,3,3,3,6,3,3] : Array ℕ)[k.val]

def p110Atoms (k : Fin 28) : Atom :=
  (#[0,17,19,44,61,63,64,65,82,111,124,125,136,140,149,151,164,165,185,187,192,199,216,220,225,235,244,253] : Array Atom)[k.val]
def p110Numerator (k : Fin 28) : ℕ :=
  (#[18,12,6,138,12,6,12,18,6,6,138,12,18,120,12,6,6,12,12,6,12,6,6,132,12,6,6,12] : Array ℕ)[k.val]

def p111Atoms (k : Fin 27) : Atom :=
  (#[0,2,17,44,46,61,64,65,82,111,124,125,136,138,140,149,164,166,185,192,197,218,220,225,233,246,253] : Array Atom)[k.val]
def p111Numerator (k : Fin 27) : ℕ :=
  (#[6,6,12,150,6,12,6,12,6,6,156,6,6,6,144,12,6,6,12,6,6,6,150,6,6,6,6] : Array ℕ)[k.val]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem p000Total : ∀ e : Early,
    (∑ k, if early (p000Atoms k) = e then p000Numerator k else 0) = denominator := by decide
private theorem p001Total : ∀ e : Early,
    (∑ k, if early (p001Atoms k) = e then p001Numerator k else 0) = denominator := by decide
private theorem p010Total : ∀ e : Early,
    (∑ k, if early (p010Atoms k) = e then p010Numerator k else 0) = denominator := by decide
private theorem p011Total : ∀ e : Early,
    (∑ k, if early (p011Atoms k) = e then p011Numerator k else 0) = denominator := by decide
private theorem p100Total : ∀ e : Early,
    (∑ k, if early (p100Atoms k) = e then p100Numerator k else 0) = denominator := by decide
private theorem p101Total : ∀ e : Early,
    (∑ k, if early (p101Atoms k) = e then p101Numerator k else 0) = denominator := by decide
private theorem p110Total : ∀ e : Early,
    (∑ k, if early (p110Atoms k) = e then p110Numerator k else 0) = denominator := by decide
private theorem p111Total : ∀ e : Early,
    (∑ k, if early (p111Atoms k) = e then p111Numerator k else 0) = denominator := by decide

noncomputable def p000Model : Model := modelOfCertificate p000Atoms p000Numerator p000Total
noncomputable def p001Model : Model := modelOfCertificate p001Atoms p001Numerator p001Total
noncomputable def p010Model : Model := modelOfCertificate p010Atoms p010Numerator p010Total
noncomputable def p011Model : Model := modelOfCertificate p011Atoms p011Numerator p011Total
noncomputable def p100Model : Model := modelOfCertificate p100Atoms p100Numerator p100Total
noncomputable def p101Model : Model := modelOfCertificate p101Atoms p101Numerator p101Total
noncomputable def p110Model : Model := modelOfCertificate p110Atoms p110Numerator p110Total
noncomputable def p111Model : Model := modelOfCertificate p111Atoms p111Numerator p111Total

private theorem p000Abs : ∀ c : Context,
    (∑ o, |diffNumerator p000Atoms p000Numerator c o|) ≤ 24 := by decide
private theorem p001Abs : ∀ c : Context,
    (∑ o, |diffNumerator p001Atoms p001Numerator c o|) ≤ 24 := by decide
private theorem p010Abs : ∀ c : Context,
    (∑ o, |diffNumerator p010Atoms p010Numerator c o|) ≤ 24 := by decide
private theorem p011Abs : ∀ c : Context,
    (∑ o, |diffNumerator p011Atoms p011Numerator c o|) ≤ 24 := by decide
private theorem p100Abs : ∀ c : Context,
    (∑ o, |diffNumerator p100Atoms p100Numerator c o|) ≤ 24 := by decide
private theorem p101Abs : ∀ c : Context,
    (∑ o, |diffNumerator p101Atoms p101Numerator c o|) ≤ 24 := by decide
private theorem p110Abs : ∀ c : Context,
    (∑ o, |diffNumerator p110Atoms p110Numerator c o|) ≤ 24 := by decide
private theorem p111Abs : ∀ c : Context,
    (∑ o, |diffNumerator p111Atoms p111Numerator c o|) ≤ 24 := by decide

theorem p000Budget : Within p000Model.behavior (1/16) :=
  modelOfCertificate_budget p000Atoms p000Numerator p000Total p000Abs
theorem p001Budget : Within p001Model.behavior (1/16) :=
  modelOfCertificate_budget p001Atoms p001Numerator p001Total p001Abs
theorem p010Budget : Within p010Model.behavior (1/16) :=
  modelOfCertificate_budget p010Atoms p010Numerator p010Total p010Abs
theorem p011Budget : Within p011Model.behavior (1/16) :=
  modelOfCertificate_budget p011Atoms p011Numerator p011Total p011Abs
theorem p100Budget : Within p100Model.behavior (1/16) :=
  modelOfCertificate_budget p100Atoms p100Numerator p100Total p100Abs
theorem p101Budget : Within p101Model.behavior (1/16) :=
  modelOfCertificate_budget p101Atoms p101Numerator p101Total p101Abs
theorem p110Budget : Within p110Model.behavior (1/16) :=
  modelOfCertificate_budget p110Atoms p110Numerator p110Total p110Abs
theorem p111Budget : Within p111Model.behavior (1/16) :=
  modelOfCertificate_budget p111Atoms p111Numerator p111Total p111Abs

def canonicalCompletion (w1 w2 x5 : Bool) : Completion :=
  { z1 := false, w1 := w1, z2 := false, w2 := w2,
    z3 := false, z4 := false, x5 := x5, y5 := false, y6 := false }

private theorem p000ScoreNum :
    scoreNumerator p000Atoms p000Numerator (canonicalCompletion false false false) = 1344 := by decide
private theorem p001ScoreNum :
    scoreNumerator p001Atoms p001Numerator (canonicalCompletion false false true) = 1296 := by decide
private theorem p010ScoreNum :
    scoreNumerator p010Atoms p010Numerator (canonicalCompletion false true false) = 1320 := by decide
private theorem p011ScoreNum :
    scoreNumerator p011Atoms p011Numerator (canonicalCompletion false true true) = 1272 := by decide
private theorem p100ScoreNum :
    scoreNumerator p100Atoms p100Numerator (canonicalCompletion true false false) = 1320 := by decide
private theorem p101ScoreNum :
    scoreNumerator p101Atoms p101Numerator (canonicalCompletion true false true) = 1272 := by decide
private theorem p110ScoreNum :
    scoreNumerator p110Atoms p110Numerator (canonicalCompletion true true false) = 1296 := by decide
private theorem p111ScoreNum :
    scoreNumerator p111Atoms p111Numerator (canonicalCompletion true true true) = 1248 := by decide

theorem p000Score :
    completedScore (canonicalCompletion false false false) p000Model.behavior = 7 := by
  rw [modelOfCertificate_score, p000ScoreNum]
  norm_num [denominator]
theorem p001Score :
    completedScore (canonicalCompletion false false true) p001Model.behavior = 27/4 := by
  rw [modelOfCertificate_score, p001ScoreNum]
  norm_num [denominator]
theorem p010Score :
    completedScore (canonicalCompletion false true false) p010Model.behavior = 55/8 := by
  rw [modelOfCertificate_score, p010ScoreNum]
  norm_num [denominator]
theorem p011Score :
    completedScore (canonicalCompletion false true true) p011Model.behavior = 53/8 := by
  rw [modelOfCertificate_score, p011ScoreNum]
  norm_num [denominator]
theorem p100Score :
    completedScore (canonicalCompletion true false false) p100Model.behavior = 55/8 := by
  rw [modelOfCertificate_score, p100ScoreNum]
  norm_num [denominator]
theorem p101Score :
    completedScore (canonicalCompletion true false true) p101Model.behavior = 53/8 := by
  rw [modelOfCertificate_score, p101ScoreNum]
  norm_num [denominator]
theorem p110Score :
    completedScore (canonicalCompletion true true false) p110Model.behavior = 27/4 := by
  rw [modelOfCertificate_score, p110ScoreNum]
  norm_num [denominator]
theorem p111Score :
    completedScore (canonicalCompletion true true true) p111Model.behavior = 13/2 := by
  rw [modelOfCertificate_score, p111ScoreNum]
  norm_num [denominator]

noncomputable def witness (c : Completion) : Model :=
  match c.w1, c.w2, c.x5 with
  | false, false, false => p000Model
  | false, false, true  => p001Model
  | false, true,  false => p010Model
  | false, true,  true  => p011Model
  | true,  false, false => p100Model
  | true,  false, true  => p101Model
  | true,  true,  false => p110Model
  | true,  true,  true  => p111Model

theorem witness_budget (c : Completion) :
    Within (witness c).behavior (1/16) := by
  rcases c with ⟨z1,w1,z2,w2,z3,z4,x5,y5,y6⟩
  cases w1 <;> cases w2 <;> cases x5 <;>
    simp [witness, p000Budget, p001Budget, p010Budget, p011Budget,
      p100Budget, p101Budget, p110Budget, p111Budget]

theorem witness_score (c : Completion) :
    completedScore c (witness c).behavior =
      6 + (c.slope : ℝ) * (1/16) := by
  rw [completedScore_late_irrelevant]
  rcases c with ⟨z1,w1,z2,w2,z3,z4,x5,y5,y6⟩
  cases w1 <;> cases w2 <;> cases x5 <;>
    simp [witness, canonicalCompletion, Completion.slope,
      p000Score, p001Score, p010Score, p011Score,
      p100Score, p101Score, p110Score, p111Score] <;> norm_num

/-- No smaller coefficient than `c.slope` can bound this completion at fixed
intercept 6 for every model and every signaling budget. -/
theorem coefficient_optimal (c : Completion) (k : ℝ)
    (h : ∀ m : Model, Within m.behavior (1/16) →
      completedScore c m.behavior ≤ 6 + k * (1/16)) :
    (c.slope : ℝ) ≤ k := by
  have hw := h (witness c) (witness_budget c)
  rw [witness_score] at hw
  linarith

/-- Each of the 512 completions has exactly the stated optimal slope. -/
theorem exact_completion_slope (c : Completion) :
    (∀ m : Model, ∀ delta : ℝ, Within m.behavior delta →
        completedScore c m.behavior ≤ 6 + (c.slope : ℝ) * delta) ∧
    (∀ k : ℝ,
      (∀ m : Model, Within m.behavior (1/16) →
        completedScore c m.behavior ≤ 6 + k * (1/16)) →
      (c.slope : ℝ) ≤ k) :=
  ⟨fun m delta h => completedScore_bound m c delta h,
    fun k h => coefficient_optimal c k h⟩

end CompletionWitness
end
end OntologySeparation.HiddenInfluence
