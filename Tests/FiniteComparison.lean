import OntologySeparation.Recipes.Separation
import Mathlib.Tactic.NativeDecide

open OntologySeparation
open OntologySeparation.Recipes
open OntologySeparation.RecipeSeparation

def finiteIdeal : Law := Law.dephasing 0 1
def finiteNoisy : Law := Law.dephasing 1 2

-- The automatic checker finds the coherence + outcome when the ideal model is left.
example : (automaticClaim finiteIdeal finiteNoisy).kind = "separation" := by
  native_decide

-- Reversing model order is still separated: normalization guarantees a positive
-- witness exists in the opposite outcome rather than treating a negative first
-- difference as agreement.
example : (automaticClaim finiteNoisy finiteIdeal).kind = "separation" := by
  native_decide

example : (automaticClaim finiteIdeal finiteIdeal).kind = "agreement" := by
  native_decide

def emptyAutomatic :=
  FiniteComparison.compare finiteEvaluator (fun _ : Probe => False) finiteIdeal finiteNoisy

example : match emptyAutomatic with
    | .empty _ => True
    | _ => False := by
  native_decide
