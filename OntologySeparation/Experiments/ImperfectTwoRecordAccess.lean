import OntologySeparation.Experiments.PartialEnvironment
import OntologySeparation.Experiments.PerfectRecordTraceout

/-!
# Two imperfect environment records

A logical branch qubit is redundantly recorded into two environment fragments.
Each record can be imperfect: branch 0 stores |0>, while branch 1 stores
r|0> + sqrt(1-r^2)|1>. The two overlaps are independent.

Observer A accesses the laboratory branch and record 1 but not record 2.
Observer B accesses the laboratory branch and record 2 but not record 1.
The coherent law is compared with branch-dephased collapse, not with full
coordinate dephasing of the record states.

The main result is an exact attainable region. If r1 and r2 are the two
record overlaps, then the optimal equal-prior discrimination distances are

  D_A = 12/25 * r2,     D_B = 12/25 * r1.

Thus the perfect-copy obstruction is the corner r1=r2=0. With independently
imperfect copies there is no additional cross-observer monogamy inequality:
every pair in [0,12/25]^2 is attained by a physical two-record source.
-/

namespace OntologySeparation.ImperfectTwoRecordAccess
noncomputable section

open scoped ComplexOrder MatrixOrder
open QuantumDiscrimination

abbrev Leakage := PartialEnvironment.Leakage
abbrev View := Bool × Bool
abbrev Registers := View × Bool

structure TwoLeakage where
  first : Leakage
  second : Leakage

def recordAmp (m : Leakage) (branch bit : Bool) : ℝ :=
  if branch then (if bit then m.orthogonal else m.overlap)
  else if bit then 0 else 1


theorem recordAmp_sq_sum (m : Leakage) (b : Bool) :
    ∑ e : Bool, recordAmp m b e ^ 2 = 1 := by
  cases b
  · norm_num [recordAmp, Fintype.sum_bool]
  · norm_num [recordAmp, Fintype.sum_bool]
    nlinarith [m.normalized]

def source (m : TwoLeakage) : QIT.PureVector Registers where
  amp i :=
    let branch := i.1.1
    let e1 := i.1.2
    let e2 := i.2
    (if branch then (4/5 : ℂ) else 3/5) *
      recordAmp m.first branch e1 * recordAmp m.second branch e2
  trace_rankOne_eq_one := by
    have hp : (m.first.overlap ^ 2 + m.first.orthogonal ^ 2) *
        (m.second.overlap ^ 2 + m.second.orthogonal ^ 2) = 1 := by
      rw [m.first.normalized, m.second.normalized]
      norm_num
    have hpc : ((m.first.overlap : ℂ)^2 + (m.first.orthogonal : ℂ)^2) *
        ((m.second.overlap : ℂ)^2 + (m.second.orthogonal : ℂ)^2) = 1 := by
      exact_mod_cast hp
    norm_num [QIT.rankOneMatrix, Matrix.vecMulVec, Matrix.trace,
      Fintype.sum_prod_type, Fintype.sum_bool, recordAmp,
      Complex.star_def, map_ofNat]
    linear_combination (16/25 : ℂ) * hpc

def coherentA (m : TwoLeakage) : QIT.State View := (source m).state.marginalA

def swapLeakage (m : TwoLeakage) : TwoLeakage where
  first := m.second
  second := m.first

/-- Same physical source with the two environment labels exchanged. -/
theorem source_swap (m : TwoLeakage) (b e1 e2 : Bool) :
    (source (swapLeakage m)).amp ((b,e2),e1) =
      (source m).amp ((b,e1),e2) := by
  cases b <;> cases e1 <;> cases e2 <;>
    simp [source, swapLeakage, recordAmp] <;> ring

/-- Observer B is represented by the same construction after swapping record
labels. The source_swap theorem proves this is only a register permutation. -/
def coherentB (m : TwoLeakage) : QIT.State View :=
  coherentA (swapLeakage m)

def branch (i : View) : Bool := i.1

/-- Branch dephasing preserves coherence inside each imperfect record state. -/
def collapsedA (m : TwoLeakage) : QIT.State View :=
  (PerfectRecordTraceout.copiedState branch (coherentA m)).marginalA

def collapsedB (m : TwoLeakage) : QIT.State View :=
  collapsedA (swapLeakage m)

theorem coherentA_entry (m : TwoLeakage) (i j : View) :
    (coherentA m).matrix i j =
      let ai : ℂ := recordAmp m.first i.1 i.2
      let aj : ℂ := recordAmp m.first j.1 j.2
      if i.1 = j.1 then
        (if i.1 then (16/25 : ℂ) else 9/25) * ai * aj
      else
        (12/25 : ℂ) * m.second.overlap * ai * aj := by
  have hn : (m.second.overlap : ℂ)^2 + (m.second.orthogonal : ℂ)^2 = 1 := by
    exact_mod_cast m.second.normalized
  rcases i with ⟨a,e⟩
  rcases j with ⟨b,f⟩
  change (∑ g : Bool, (source m).state.matrix ((a,e),g) ((b,f),g)) = _
  cases a <;> cases b
  · cases e <;> cases f <;>
      norm_num [source, recordAmp, QIT.PureVector.state, QIT.rankOneMatrix,
        Matrix.vecMulVec, Fintype.sum_bool, Complex.star_def, map_ofNat]
  · cases e <;> cases f <;>
      norm_num [source, recordAmp, QIT.PureVector.state, QIT.rankOneMatrix,
        Matrix.vecMulVec, Fintype.sum_bool, Complex.star_def, map_ofNat] <;> ring
  · cases e <;> cases f <;>
      norm_num [source, recordAmp, QIT.PureVector.state, QIT.rankOneMatrix,
        Matrix.vecMulVec, Fintype.sum_bool, Complex.star_def, map_ofNat] <;> ring
  · cases e <;> cases f <;>
      norm_num [source, recordAmp, QIT.PureVector.state, QIT.rankOneMatrix,
        Matrix.vecMulVec, Fintype.sum_bool, Complex.star_def, map_ofNat]
    · linear_combination (16/25 : ℂ) * (m.first.overlap : ℂ)^2 * hn
    · linear_combination (16/25 : ℂ) * (m.first.overlap : ℂ) *
        (m.first.orthogonal : ℂ) * hn
    · linear_combination (16/25 : ℂ) * (m.first.orthogonal : ℂ) *
        (m.first.overlap : ℂ) * hn
    · linear_combination (16/25 : ℂ) * (m.first.orthogonal : ℂ)^2 * hn

theorem collapsedA_entry (m : TwoLeakage) (i j : View) :
    (collapsedA m).matrix i j =
      if i.1 = j.1 then (coherentA m).matrix i j else 0 := by
  unfold collapsedA
  rw [PerfectRecordTraceout.marginal_entry]
  rfl

def branch0 : View → ℂ := fun i =>
  if i.1 then 0 else if i.2 then 0 else 1

def branch1 (m : TwoLeakage) : View → ℂ := fun i =>
  if i.1 then recordAmp m.first true i.2 else 0

def branchVector (m : TwoLeakage) (minus : Bool) : View → ℂ := fun i =>
  branch0 i + (if minus then - branch1 m i else branch1 m i)

def branchProjector (m : TwoLeakage) (minus : Bool) : Matrix View View ℂ :=
  (1/2 : ℂ) • QIT.rankOneMatrix (branchVector m minus)

private theorem branch1_norm (m : TwoLeakage) :
    ∑ i : View, Complex.normSq (branch1 m i) = 1 := by
  have h := m.first.normalized
  norm_num [branch1, recordAmp, Fintype.sum_prod_type, Fintype.sum_bool,
    Complex.normSq_apply]
  nlinarith

theorem projector_pos (m : TwoLeakage) (minus : Bool) :
    (branchProjector m minus).PosSemidef := by
  apply Matrix.PosSemidef.smul (QIT.rankOneMatrix_pos _)
  norm_num [Complex.nonneg_iff]


private theorem branchVector_dot (m : TwoLeakage) (minus : Bool) :
    (fun i => star (branchVector m minus i)) ⬝ᵥ branchVector m minus = 2 := by
  apply Complex.ext
  · cases minus <;>
      norm_num [dotProduct, branchVector, branch0, branch1, recordAmp,
        Fintype.sum_prod_type, Fintype.sum_bool, Complex.star_def,
        Complex.mul_re] <;>
      nlinarith [m.first.normalized]
  · cases minus <;>
      norm_num [dotProduct, branchVector, branch0, branch1, recordAmp,
        Fintype.sum_prod_type, Fintype.sum_bool, Complex.star_def,
        Complex.mul_im]

theorem projector_idempotent (m : TwoLeakage) (minus : Bool) :
    branchProjector m minus * branchProjector m minus =
      branchProjector m minus := by
  unfold branchProjector QIT.rankOneMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.vecMulVec_mul_vecMulVec, branchVector_dot]
  simp [smul_smul]

theorem projector_trace (m : TwoLeakage) (minus : Bool) :
    (branchProjector m minus).trace = 1 := by
  unfold branchProjector
  rw [Matrix.trace_smul, QIT.rankOneMatrix_trace]
  have h := branchVector_dot m minus
  rw [dotProduct_comm] at h
  rw [h]
  norm_num

def readoutA (m : TwoLeakage) : QIT.POVM Bool View where
  effects b := if b then branchProjector m false else 1 - branchProjector m false
  pos b := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hp := projector_pos m false
      have hidem : branchProjector m false * branchProjector m false =
          branchProjector m false := projector_idempotent m false
      have hh := hp.isHermitian.eq
      have he : Matrix.conjTranspose (1 - branchProjector m false) *
          (1 - branchProjector m false) = 1 - branchProjector m false := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh,
          sub_mul, mul_sub, one_mul, mul_one, hidem]
        abel
      rw [← he]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    · simpa using projector_pos m false
  sum_eq_one := by simp

def testA (m : TwoLeakage) := FiniteQuantum.measure (readoutA m)


private theorem first_norm_sq (m : TwoLeakage) :
    (m.first.overlap ^ 2 + m.first.orthogonal ^ 2) ^ 2 = 1 := by
  rw [m.first.normalized]
  norm_num

private theorem first_norm_mul_second (m : TwoLeakage) :
    m.second.overlap *
        (m.first.overlap ^ 2 + m.first.orthogonal ^ 2) =
      m.second.overlap := by
  rw [m.first.normalized]
  ring

theorem coherentA_probability (m : TwoLeakage) :
    (testA m).prob (coherentA m) true =
      1/2 + 12/25 * m.second.overlap := by
  rw [testA, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  norm_num [readoutA, Matrix.trace, Matrix.mul_apply, coherentA_entry,
    branchProjector, branchVector, branch0, branch1, recordAmp,
    QIT.rankOneMatrix, Matrix.vecMulVec,
    Fintype.sum_prod_type, Fintype.sum_bool, Complex.mul_re]
  have hsq := first_norm_sq m
  have hmul := first_norm_mul_second m
  ring_nf at hsq hmul ⊢
  nlinarith

theorem collapsedA_probability (m : TwoLeakage) :
    (testA m).prob (collapsedA m) true = 1/2 := by
  rw [testA, FiniteQuantum.measure_prob, QIT.POVM.prob_eq_trace_re]
  norm_num [readoutA, Matrix.trace, Matrix.mul_apply, collapsedA_entry,
    coherentA_entry, branchProjector, branchVector, branch0, branch1, recordAmp,
    QIT.rankOneMatrix, Matrix.vecMulVec,
    Fintype.sum_prod_type, Fintype.sum_bool, Complex.mul_re]
  have hsq := first_norm_sq m
  ring_nf at hsq ⊢
  nlinarith

theorem differenceA_matrix (m : TwoLeakage) :
    (coherentA m).matrix - (collapsedA m).matrix =
      ((12/25 * m.second.overlap : ℝ) : ℂ) •
        (branchProjector m false - branchProjector m true) := by
  ext ⟨a,e⟩ ⟨b,f⟩
  cases a <;> cases b <;> cases e <;> cases f <;>
    norm_num [Matrix.sub_apply, collapsedA_entry, coherentA_entry,
      branchProjector, branchVector, branch0, branch1, recordAmp,
      QIT.rankOneMatrix, Matrix.vecMulVec] <;>
    (try ring_nf) <;>
    simp

theorem distanceA_upper (m : TwoLeakage) :
    (coherentA m).normalizedTraceDistance (collapsedA m) ≤
      12/25 * m.second.overlap := by
  have hp (b : Bool) : QIT.traceNorm (branchProjector m b) = 1 := by
    rw [QIT.traceNorm_posSemidef_eq_trace_re _ (projector_pos m b),
      projector_trace]
    rfl
  have ht := QIT.traceNorm_add_le (branchProjector m false) (-branchProjector m true)
  rw [QIT.traceNorm_neg, hp, hp] at ht
  change 1/2 * QIT.traceNorm ((coherentA m).matrix - (collapsedA m).matrix) ≤ _
  rw [differenceA_matrix,
    QIT.traceNorm_real_smul_eq (mul_nonneg (by norm_num) m.second.nonneg)]
  rw [← sub_eq_add_neg] at ht
  nlinarith [m.second.nonneg]

theorem distanceA_exact (m : TwoLeakage) :
    (coherentA m).normalizedTraceDistance (collapsedA m) =
      12/25 * m.second.overlap := by
  apply le_antisymm (distanceA_upper m)
  have h := QuantumDiscrimination.probability_gap_le
    (coherentA m) (collapsedA m) (testA m)
  rw [coherentA_probability, collapsedA_probability] at h
  linarith

theorem distanceB_exact (m : TwoLeakage) :
    (coherentB m).normalizedTraceDistance (collapsedB m) =
      12/25 * m.first.overlap := by
  exact distanceA_exact (swapLeakage m)

def distanceA (m : TwoLeakage) : ℝ :=
  (coherentA m).normalizedTraceDistance (collapsedA m)

def distanceB (m : TwoLeakage) : ℝ :=
  (coherentB m).normalizedTraceDistance (collapsedB m)

theorem distance_pair_exact (m : TwoLeakage) :
    distanceA m = 12/25 * m.second.overlap ∧
    distanceB m = 12/25 * m.first.overlap :=
  ⟨distanceA_exact m, distanceB_exact m⟩

/-- Every point in the square [0,12/25]^2 is attained by a physical pair of
normalized imperfect record states. Therefore independent record imperfections
do not obey an additional cross-observer monogamy relation. -/
theorem attainable_square (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 12/25)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 12/25) :
    ∃ m : TwoLeakage, distanceA m = x ∧ distanceB m = y := by
  let r2 := 25/12 * x
  let r1 := 25/12 * y
  have hr20 : 0 ≤ r2 := by dsimp [r2]; positivity
  have hr21 : r2 ≤ 1 := by dsimp [r2]; linarith
  have hr10 : 0 ≤ r1 := by dsimp [r1]; positivity
  have hr11 : r1 ≤ 1 := by dsimp [r1]; linarith
  let m : TwoLeakage :=
    { first := PartialEnvironment.Leakage.ofOverlap r1 hr10 hr11
      second := PartialEnvironment.Leakage.ofOverlap r2 hr20 hr21 }
  refine ⟨m, ?_, ?_⟩
  · unfold distanceA
    rw [distanceA_exact]
    change 12/25 * r2 = x
    dsimp [r2]
    ring
  · unfold distanceB
    rw [distanceB_exact]
    change 12/25 * r1 = y
    dsimp [r1]
    ring

theorem attainable_region_iff (x y : ℝ) :
    (∃ m : TwoLeakage, distanceA m = x ∧ distanceB m = y) ↔
      0 ≤ x ∧ x ≤ 12/25 ∧ 0 ≤ y ∧ y ≤ 12/25 := by
  constructor
  · rintro ⟨m, rfl, rfl⟩
    unfold distanceA distanceB
    rw [distanceA_exact, distanceB_exact]
    constructor
    · exact mul_nonneg (by norm_num) m.second.nonneg
    constructor
    · have h := m.second.normalized
      have hn := m.second.nonneg
      have ho : m.second.overlap ≤ 1 := by
        nlinarith [sq_nonneg m.second.orthogonal]
      nlinarith
    constructor
    · exact mul_nonneg (by norm_num) m.first.nonneg
    · have h := m.first.normalized
      have hn := m.first.nonneg
      have ho : m.first.overlap ≤ 1 := by
        nlinarith [sq_nonneg m.first.orthogonal]
      nlinarith
  · rintro ⟨hx0,hx1,hy0,hy1⟩
    exact attainable_square x y hx0 hx1 hy0 hy1

/-- Perfect copies recover the earlier exact obstruction as the corner of the
continuous region. -/
theorem perfect_copy_corner :
    let z := PartialEnvironment.Leakage.ofOverlap 0 (by norm_num) (by norm_num)
    let m : TwoLeakage := { first := z, second := z }
    distanceA m = 0 ∧ distanceB m = 0 := by
  dsimp
  unfold distanceA distanceB
  rw [distanceA_exact, distanceB_exact]
  norm_num [PartialEnvironment.Leakage.ofOverlap]

end
end OntologySeparation.ImperfectTwoRecordAccess
