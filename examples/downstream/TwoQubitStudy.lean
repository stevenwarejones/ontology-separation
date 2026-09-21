import OntologySeparation.Recipes

namespace BellStudy
open OntologySeparation.TwoQubit

-- Alice and Bob have two local projective settings each.
-- These rational directions give CHSH = 1502/625 for an ideal singlet.
-- Only exposure uses the selected row's law. All gates precede setting choices.
def direct : Recipe := { singletRecipe with steps := [.expose .alice] }

-- Build the same singlet from |00>: H(A), CNOT(A->B), X(B), Z(A).
def circuit : Recipe :=
  { direct with
    prepare := .product false false
    steps := [.h .alice, .cnot .alice, .x .bob, .z .alice, .expose .alice] }

-- Change preparation while keeping the same measurements and exposure.
def product : Recipe := { direct with prepare := .product false true }

-- Law.dephasing takes Alice numerator, Bob numerator, common denominator.
-- p=1 is full Z dephasing; p=0 is ideal. Rates are checked before export.
def comparison := compare "BellStudy: two-qubit Bell experiment"
  [Law.ideal, Law.dephasing 1 0 8, Law.dephasing 1 0 4, Law.dephasing 1 0 1]
  [direct, circuit, product]
end BellStudy

#export_scenario BellStudy.comparison
