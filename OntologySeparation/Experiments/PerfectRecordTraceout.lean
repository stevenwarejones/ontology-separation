import OntologySeparation.Adapters.FiniteQuantum

/-!
# Generic perfect-record traceout

Let A be any finite accessible quantum system and let branch : A → Bool label the
two friend branches on its computational basis. Append one fresh qubit that
perfectly copies that branch label by an isometry, then make the copied qubit
inaccessible.

The reduced state on A is exactly dephased between distinct branch sectors:
matrix elements within the same branch are preserved and cross-branch coherence
is killed. Because A itself may already contain any finite collection of system,
friend, ancilla, or previously accessible record registers, this is the generic
"one inaccessible perfect copy is enough" lemma needed for arbitrary redundant
record families.
-/

namespace OntologySeparation.PerfectRecordTraceout
noncomputable section
open scoped ComplexOrder MatrixOrder

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Append a clean Bool register carrying an exact copy of a classical branch
label on the computational basis. -/
def copyIsometry (branch : A → Bool) : Matrix (A × Bool) A ℂ := fun o i =>
  if o.1 = i ∧ o.2 = branch i then 1 else 0

theorem copyIsometry_isometry (branch : A → Bool) :
    Matrix.conjTranspose (copyIsometry branch) * copyIsometry branch = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    cases hb : branch i <;>
      simp [copyIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply, hb]
  · have hji : j ≠ i := Ne.symm hij
    cases hi : branch i <;> cases hj : branch j <;>
      simp [copyIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply, hij, hji, hi, hj]

def copiedState (branch : A → Bool) (rho : QIT.State A) :
    QIT.State (A × Bool) :=
  QIT.POVM.isometryLiftState rho (copyIsometry branch)
    (copyIsometry_isometry branch)

/-- Matrix entries of the lifted state: the copied qubit is pinned to the
branch label on each side. -/
theorem copied_entry (branch : A → Bool) (rho : QIT.State A)
    (i j : A) (e f : Bool) :
    (copiedState branch rho).matrix (i,e) (j,f) =
      if e = branch i ∧ f = branch j then rho.matrix i j else 0 := by
  classical
  simp only [copiedState, QIT.POVM.isometryLiftState_matrix, copyIsometry,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases he : e = branch i
  · by_cases hf : f = branch j
    · simp only [he, hf, and_self, ↓reduceIte]
      rw [Finset.sum_eq_single j]
      · simp only [eq_self, he, hf, and_self, ↓reduceIte]
        rw [Finset.sum_eq_single i]
        · simp
        · intro x _ hxi
          have hix : i ≠ x := Ne.symm hxi
          simp [hix]
        · simp
      · intro x _ hxj
        have hjx : j ≠ x := Ne.symm hxj
        simp [hjx]
      · simp
    · simp only [he, hf, and_false, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x = j
      · subst x
        simp [hf]
      · have hjx : j ≠ x := Ne.symm hx
        simp [hjx]
  · simp only [he, false_and, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = j
    · subst x
      by_cases hfb : f = branch j
      · simp only [eq_self, hfb, and_self, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro x₁ _
        by_cases hxi : x₁ = i
        · subst x₁
          simp [he]
        · have hix : i ≠ x₁ := Ne.symm hxi
          simp [hix]
      · simp [hfb]
    · have hjx : j ≠ x := Ne.symm hx
      simp [hjx]

/-- Exact reduced-state formula after the perfect copy is lost. -/
theorem marginal_entry (branch : A → Bool) (rho : QIT.State A) (i j : A) :
    (copiedState branch rho).marginalA.matrix i j =
      if branch i = branch j then rho.matrix i j else 0 := by
  change
    (∑ e : Bool, (copiedState branch rho).matrix (i,e) (j,e)) =
      if branch i = branch j then rho.matrix i j else 0
  simp_rw [copied_entry]
  cases hi : branch i <;> cases hj : branch j <;>
    simp [hi, hj, Fintype.sum_bool]

/-- Cross-branch coherence is exactly zero after tracing one inaccessible perfect
record, independently of the dimension and internal structure of A. -/
theorem cross_branch_zero (branch : A → Bool) (rho : QIT.State A)
    (i j : A) (h : branch i ≠ branch j) :
    (copiedState branch rho).marginalA.matrix i j = 0 := by
  rw [marginal_entry]
  simp [h]

/-- Same-branch matrix elements survive unchanged. -/
theorem same_branch_preserved (branch : A → Bool) (rho : QIT.State A)
    (i j : A) (h : branch i = branch j) :
    (copiedState branch rho).marginalA.matrix i j = rho.matrix i j := by
  rw [marginal_entry]
  simp [h]

/-- If the original state has any nonzero cross-branch coherence, the accessible
state after losing the perfect copy is different from the original state. -/
theorem inaccessible_copy_changes_coherent_state
    (branch : A → Bool) (rho : QIT.State A)
    (i j : A) (hbranch : branch i ≠ branch j)
    (hcoh : rho.matrix i j ≠ 0) :
    (copiedState branch rho).marginalA ≠ rho := by
  intro h
  have hij := congrArg (fun s : QIT.State A => s.matrix i j) h
  change (copiedState branch rho).marginalA.matrix i j = rho.matrix i j at hij
  rw [cross_branch_zero branch rho i j hbranch] at hij
  exact hcoh hij.symm

end
end OntologySeparation.PerfectRecordTraceout
