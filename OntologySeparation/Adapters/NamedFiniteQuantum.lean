import OntologySeparation.Adapters.FiniteQuantum
import OntologySeparation.Core.RegisterAccess

/-! Typed two-register quantum protocols with named access footprints.

The register names control access while the quantum types control tensor order.
Local protocols are physically typed on the left factor and therefore cannot
apply a joint channel while merely claiming a local label. -/
namespace OntologySeparation.FiniteQuantum.Named
noncomputable section

variable {R A B C O : Type}
  [DecidableEq R]
  [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype O] [DecidableEq O]

/-- Names attached to the two typed tensor factors. Distinctness prevents the
same human-facing register name from silently denoting both factors. -/
structure Names (R : Type) [DecidableEq R] where
  left : R
  right : R
  distinct : left ≠ right

/-- A protocol is local by construction or joint by construction. The local
constructor accepts only tests on the left Hilbert-space factor. -/
inductive Protocol (A B C O : Type)
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    [Fintype O] where
  | localTest (test : Test A C O)
  | jointTest (test : Test (A × B) C O)

def Protocol.localOnly : Protocol A B C O → Prop
  | .localTest _ => True
  | .jointTest _ => False

def protocolRegisters (names : Names R) : Protocol A B C O → Finset R
  | .localTest _ => {names.left}
  | .jointTest _ => {names.left, names.right}

def footprint (names : Names R) :
    RegisterAccess.Footprint R (Protocol A B C O) :=
  ⟨protocolRegisters names⟩

def leftPolicy (names : Names R) : RegisterAccess.Policy R :=
  ⟨{names.left}⟩

def bothPolicy (names : Names R) : RegisterAccess.Policy R :=
  ⟨{names.left, names.right}⟩

theorem left_allowed_iff (names : Names R) (p : Protocol A B C O) :
    RegisterAccess.Allowed (footprint names) (leftPolicy names) p ↔ p.localOnly := by
  cases p <;>
    simp [RegisterAccess.Allowed, footprint, protocolRegisters, leftPolicy,
      Protocol.localOnly, Finset.subset_iff, names.distinct, Ne.symm names.distinct]

theorem both_allowed (names : Names R) (p : Protocol A B C O) :
    RegisterAccess.Allowed (footprint names) (bothPolicy names) p := by
  cases p <;>
    simp [RegisterAccess.Allowed, footprint, protocolRegisters, bothPolicy]

/-- The same typed protocol is interpreted on either the accessible marginal or
the full two-register state according to its constructor. -/
def predict (ρ : QIT.State (A × B)) :
    Protocol A B C O → Behavior { Setting := Unit, Outcome := O }
  | .localTest test => behavior ρ.marginalA (fun _ => test)
  | .jointTest test => behavior ρ (fun _ => test)

/-- Equal left marginals imply agreement for every protocol admitted by the
left-register policy. Joint protocols are rejected before quantum evaluation. -/
theorem left_equivalent (names : Names R) (ρ σ : QIT.State (A × B))
    (h : ρ.marginalA = σ.marginalA) :
    ExperimentAccess.Equivalent (predict (C := C) (O := O))
      (RegisterAccess.Allowed (footprint names) (leftPolicy names)) ρ σ := by
  intro p hp s o
  cases p with
  | localTest test =>
      exact local_behavior_eq ρ σ h (fun _ => test) s o
  | jointTest test =>
      exact False.elim ((left_allowed_iff names (.jointTest test)).mp hp)

end
end OntologySeparation.FiniteQuantum.Named
