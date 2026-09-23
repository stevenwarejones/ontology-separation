import OntologySeparation.Certificates.LFAgencySqrtTwo

namespace OntologySeparation.LFAgencyRelaxation.SqrtTwoPhysical
noncomputable section
open LFJoint
open scoped BigOperators
open SqrtTwoCertificate

private def bitBool (n : ℕ) : Bool := if n % 2 = 0 then false else true

private def qX (q : Fin 144) : Fin 3 := ⟨q.val / 48, by omega⟩
private def qY (q : Fin 144) : Fin 3 := ⟨q.val / 16 % 3, Nat.mod_lt _ (by omega)⟩
private def qR (q : Fin 144) : Record :=
  let r := q.val / 4 % 4
  (bitBool (r / 2), bitBool r)
private def qA (q : Fin 144) : Bool := bitBool (q.val / 2)
private def qB (q : Fin 144) : Bool := bitBool q.val

private def qWeight (j : AbsoluteEventTable) (q : Fin 144) : ℝ :=
  j.prob (qX q, qY q) (qR q) (qA q, qB q)

private def uWeight (j : AbsoluteEventTable) (k : Fin 16) : ℝ :=
  if h : k.val < 8 then
    let r : Record := (bitBool (k.val / 2 / 2), bitBool (k.val / 2))
    let a := bitBool k.val
    |recordAlice j 2 0 r a - recordAlice j 2 2 r a|
  else
    let kk := k.val - 8
    let r : Record := (bitBool (kk / 2 / 2), bitBool (kk / 2))
    let b := bitBool kk
    |recordBob j 0 2 r b - recordBob j 2 2 r b|

def weights (j : AbsoluteEventTable) (c : Column) : ℝ :=
  Fin.addCases (motive := fun _ => ℝ) (qWeight j) (uWeight j) c

theorem weights_nonnegative (j : AbsoluteEventTable) (c : Column) :
    0 ≤ weights j c := by
  unfold weights
  refine Fin.addCases (m := 144) (n := 16) (fun q => ?_) (fun k => ?_) c
  · exact j.nonneg _ _
  · unfold uWeight
    split <;> positivity

private theorem public_eq (j : AbsoluteEventTable) (hp : j.behavior = sqrtTwoBehavior)
    (x y : Fin 3) (a b : Bool) :
    (∑ r : Record, j.prob (x,y) r (a,b)) = sqrtTwoBehavior.prob (x,y) (a,b) := by
  have h := congrArg (fun p : Behavior LF.interface => p.prob (x,y) (a,b)) hp
  simpa [LFJoint.Table.behavior] using h

private theorem record_eq (j : AbsoluteEventTable) (hi : IndependentRecords j)
    (x y : Fin 3) (r : Record) :
    (∑ o, j.prob (x,y) r o) = ∑ o, j.prob (0,0) r o := by
  exact hi (x,y) (0,0) r

private theorem wrongA_zero (j : AbsoluteEventTable) (hr : Readable j)
    (r : Record) (y : Fin 3) (b : Bool) :
    j.prob (0,y) r (!r.1,b) = 0 := by
  have hread := hr.1 r y
  have hn0 := j.nonneg (0,y) r (!r.1,false)
  have hn1 := j.nonneg (0,y) r (!r.1,true)
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;> cases b <;>
    simp [LFJoint.Table.mass, Fintype.sum_prod_type] at hread hn0 hn1 ⊢ <;> linarith

private theorem wrongB_zero (j : AbsoluteEventTable) (hr : Readable j)
    (r : Record) (x : Fin 3) (a : Bool) :
    j.prob (x,0) r (a,!r.2) = 0 := by
  have hread := hr.2 r x
  have hn0 := j.nonneg (x,0) r (false,!r.2)
  have hn1 := j.nonneg (x,0) r (true,!r.2)
  rcases r with ⟨c,d⟩
  cases c <;> cases d <;> cases a <;>
    simp [LFJoint.Table.mass, Fintype.sum_prod_type] at hread hn0 hn1 ⊢ <;> linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem physical_objective (j : AbsoluteEventTable) :
    SqrtTwoCertificate.pairing SqrtTwoCertificate.objective (weights j) =
      2 * recordTVAlice j 2 0 2 + 2 * recordTVBob j 0 2 2 := by
  unfold SqrtTwoCertificate.pairing weights
  rw [Fin.sum_univ_add (a := 144) (b := 16)]
  norm_num [SqrtTwoCertificate.objective, uWeight, recordTVAlice, recordTVBob,
    recordAlice, recordBob, bitBool, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem physical_equations (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j) (hp : j.behavior = sqrtTwoBehavior) :
    ∀ i : EqRow, SqrtTwoCertificate.pairing (SqrtTwoCertificate.eqCoeff i) (weights j) =
      SqrtTwoCertificate.rhs i := by
  intro i
  have hpub := public_eq j hp
  have hrec := record_eq j hi
  have hwa := wrongA_zero j hr
  have hwb := wrongB_zero j hr
  fin_cases i <;>
    norm_num [SqrtTwoCertificate.pairing, weights, qWeight, uWeight,
      SqrtTwoCertificate.eqCoeff, SqrtTwoCertificate.rawEqCoeff,
      SqrtTwoCertificate.rhs, SqrtTwoCertificate.rawRhs,
      SqrtTwoCertificate.rawEq, SqrtTwoCertificate.fixedZeroIndex,
      qX, qY, qR, qA, qB, bitBool,
      Fin.sum_univ_succ] <;>
    simp_all [Fintype.sum_prod_type, LFJoint.Table.mass]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem physical_inequalities (j : AbsoluteEventTable) :
    ∀ i : IneqRow,
      SqrtTwoCertificate.pairing (SqrtTwoCertificate.ineqCoeff i) (weights j) ≤ 0 := by
  intro i
  fin_cases i <;>
    norm_num [SqrtTwoCertificate.pairing, weights, qWeight, uWeight,
      SqrtTwoCertificate.ineqCoeff, qX, qY, qR, qA, qB, bitBool,
      recordAlice, recordBob, Fin.sum_univ_succ] <;>
    apply sub_nonpos.mpr <;>
    first | exact le_abs_self _ | exact neg_le_abs _

def toFeasible (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j) (hp : j.behavior = sqrtTwoBehavior) :
    SqrtTwoCertificate.Feasible where
  weight := weights j
  nonnegative := weights_nonnegative j
  equations := physical_equations j hr hi hp
  inequalities := physical_inequalities j

theorem sum_recordTV_lower_bound (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j) (hp : j.behavior = sqrtTwoBehavior) :
    Real.sqrt 2 - 1 ≤ recordTVAlice j 2 0 2 + recordTVBob j 0 2 2 := by
  have h := SqrtTwoCertificate.bound (toFeasible j hr hi hp)
  rw [physical_objective] at h
  linarith

theorem explicit_angle_bound (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j) (hp : j.behavior = sqrtTwoBehavior) :
    sqrtTwoDelta ≤ recordTVAlice j 2 0 2 ∨
      sqrtTwoDelta ≤ recordTVBob j 0 2 2 := by
  have h := sum_recordTV_lower_bound j hr hi hp
  by_contra hn
  push_neg at hn
  unfold sqrtTwoDelta at hn
  linarith

/-- Final explicit-angle theorem stated directly for the concrete singlet
measurement bases, rather than the intermediate exact probability table. -/
theorem explicit_angle_quantum_bound (j : AbsoluteEventTable) (hr : Readable j)
    (hi : IndependentRecords j)
    (hp : j.behavior = RealQuantum.behavior explicitAlice explicitBob) :
    sqrtTwoDelta ≤ recordTVAlice j 2 0 2 ∨
      sqrtTwoDelta ≤ recordTVBob j 0 2 2 := by
  apply explicit_angle_bound j hr hi
  exact hp.trans explicit_quantum_matches

end
end OntologySeparation.LFAgencyRelaxation.SqrtTwoPhysical
