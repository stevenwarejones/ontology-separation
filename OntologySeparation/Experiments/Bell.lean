import OntologySeparation.Adapters.Bell
import OntologySeparation.Models.RealQuantum

/-! An explicit rational-basis singlet violation of CHSH, using the same observable
and local class as the Lean-QIT adapter. It need not maximize the quantum value. -/
namespace OntologySeparation.Bell
noncomputable section

def b43 : RealQuantum.Basis := ⟨4/5, 3/5, by norm_num⟩
def b01 : RealQuantum.Basis := ⟨0, 1, by norm_num⟩

def alice (x : Fin 2) : RealQuantum.Basis :=
  if x.val = 0 then RealQuantum.basis45 else RealQuantum.basis35
def bob (y : Fin 2) : RealQuantum.Basis := if y.val = 0 then b43 else b01

def singletBehavior : Behavior interface := RealQuantum.behavior alice bob

theorem singlet_score : score singletBehavior = 1502 / 625 := by
  norm_num [score, correlator, singletBehavior, RealQuantum.behavior,
    RealQuantum.probability, RealQuantum.Basis.vector, alice, bob, b43, b01,
    RealQuantum.basis45, RealQuantum.basis35, QIT.Bell.CHSH.outcomeSign,
    Fintype.sum_prod_type]

def quantumSeparation : Separation localTheory (RealQuantum.singletTheory 2) score where
  bound := localBound
  witness := ⟨singletBehavior, ⟨alice, bob, rfl⟩⟩
  violation := by
    change (2 : ℝ) < score singletBehavior
    rw [singlet_score]
    norm_num

end
end OntologySeparation.Bell
