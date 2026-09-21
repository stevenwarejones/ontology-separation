import OntologySeparation.Recipes.TwoQubit
import Mathlib.Tactic.FinCases

open OntologySeparation
open OntologySeparation.TwoQubit

-- Entangled and product preparations are operationally distinct.
example : probability Law.ideal singletRecipe (0,0) (false,false) = 288/625 := by two_qubit_check
example : chsh Law.ideal singletRecipe = 1502/625 := by two_qubit_check
example : ¬ Bell.localTheory (interpret Law.ideal singletRecipe) := by
  apply excludes_local
  two_qubit_check

-- The recipe reproduces every probability of the established singlet witness.
example (xy : Fin 2 × Fin 2) (ab : Bool × Bool) :
    (interpret Law.ideal singletRecipe).prob xy ab = Bell.singletBehavior.prob xy ab :=
  singlet_matches_reference xy ab

def zz : Settings := ⟨.z, .z⟩
def entangle : Recipe :=
  { prepare := .product false false, steps := [.h .alice, .cnot .alice], alice := zz, bob := zz }
example : probability Law.ideal entangle (0,0) (false,false) = 1/2 := by
  unfold entangle zz; two_qubit_check
example : probability Law.ideal entangle (0,0) (true,true) = 1/2 := by
  unfold entangle zz; two_qubit_check
example : probability Law.ideal entangle (0,0) (false,true) = 0 := by
  unfold entangle zz; two_qubit_check
-- Swapping gate order gives a product state, not the Bell state.
example : probability Law.ideal { entangle with steps := [.cnot .alice, .h .alice] }
    (0,0) (true,true) = 0 := by unfold entangle zz; two_qubit_check
-- Bob as control is not Alice as control.
example : probability Law.ideal
    { entangle with prepare := .product false true, steps := [.cnot .bob] }
    (0,0) (true,true) = 1 := by unfold entangle zz; two_qubit_check

-- Local exposure destroys singlet coherence, not the classical populations.
def noisy : Recipe := { singletRecipe with steps := [.expose .alice] }
example : chsh (Law.dephasing 1 0 1) noisy = 14/25 := by unfold noisy; two_qubit_check
example : chsh (Law.dephasing 1 0 4) noisy = 1214/625 := by unfold noisy; two_qubit_check
example : chsh (Law.dephasing 1 0 8) noisy = 1358/625 := by unfold noisy; two_qubit_check
example : chsh (Law.dephasing 1 0 2) { noisy with steps := [.expose .alice, .expose .alice] }
    = 638/625 := by unfold noisy; two_qubit_check
example : chsh (Law.dephasing 1 1 2) { noisy with steps := [.expose .alice, .expose .bob] }
    = 638/625 := by unfold noisy; two_qubit_check


-- Bob's H and wire permutation use the declared tensor order.
example : probability Law.ideal { entangle with steps := [.h .bob] }
    (0,0) (false,true) = 1/2 := by unfold entangle zz; two_qubit_check
example : probability Law.ideal
    { entangle with prepare := .product false true, steps := [.swap] }
    (0,0) (true,false) = 1 := by unfold entangle zz; two_qubit_check
-- Custom inputs are rays, so norm need not be one. Measurement directions also normalize.
example : probability Law.ideal
    { prepare := .custom (.of 2 0 0 2), alice := zz, bob := zz }
    (0,0) (false,false) = 1/2 := by unfold zz; two_qubit_check
example : probability Law.ideal
    { prepare := .product false false,
      alice := ⟨.of 3 3, .z⟩, bob := zz }
    (0,0) (false,false) = 1/2 := by unfold zz; two_qubit_check
-- No exposure means the law does not change the circuit's prediction.
example : chsh (Law.dephasing 1 1 1) singletRecipe = 1502/625 := by two_qubit_check
