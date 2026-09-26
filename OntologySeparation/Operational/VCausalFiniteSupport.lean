import OntologySeparation.Operational.VCausal

/-! Finitely supported hidden laws on arbitrary ambient types. No Fintype
instance is required on the ambient hidden space. This is a finite-sum result,
not a theorem for general probability measures with infinite support. -/
namespace OntologySeparation.VCausal
noncomputable section
open scoped BigOperators
open HiddenInfluence

structure SupportedProtocol (order : EarlyOrder) (Ω : Type) where
  support : Finset Ω
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  zero_off_support : ∀ ω, ω ∉ support → weight ω = 0
  total : ∑ ω ∈ support, weight ω = 1
  table : Ω → Early → Strategy
  allowed : ∀ ω, weight ω ≠ 0 → EarlyAllowed order (fun e => (table ω e).record)

def SupportedProtocol.toProtocol {order : EarlyOrder} {Ω : Type}
    (p : SupportedProtocol order Ω) : Protocol order {ω // ω ∈ p.support} where
  shared := {
    mass := fun ω => p.weight ω
    nonneg := fun ω => p.nonneg ω
    total := by simpa only [Finset.univ_eq_attach, Finset.sum_attach] using p.total }
  table ω := p.table ω
  allowed ω hω := p.allowed ω hω

/-- Restriction to the finite support preserves the entire observed law. -/
theorem SupportedProtocol.full_behavior {order : EarlyOrder} {Ω : Type}
    (p : SupportedProtocol order Ω) (e : Early) (y z : Bool) (o : VisibleOutcome) :
    p.toProtocol.toModel.behavior.prob (e,lateFromBool y z) o.toOutcome =
      ∑ ω ∈ p.support, p.weight ω *
        (if (p.table ω e).visible y z = o then 1 else 0) := by
  classical
  rw [Protocol.full_behavior]
  simp only [Protocol.run, FiniteKernel.map_mass, SupportedProtocol.toProtocol]
  simp only [Finset.univ_eq_attach, mul_ite, mul_one, mul_zero]
  exact Finset.sum_attach p.support (fun ω => if (p.table ω e).visible y z = o then p.weight ω else 0)

end
end OntologySeparation.VCausal
