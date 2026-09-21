import OntologySeparation.Adapters.FiniteQuantum
import QIT.Core.Pure
import Mathlib.Tactic.NormNum

open OntologySeparation
open ExperimentAccess

example {M P : Type} {E : Interface} (predict : Predictions M P E) (a b : M) :
    Equivalent predict (fun _ => False) a b := fun _ hp => False.elim hp

example {M P : Type} {E : Interface} (predict : Predictions M P E) (a b : M)
    (h : Equivalent predict (fun _ => True) a b)
    (w : Separator predict (fun _ => True) a b) : False := w.not_equivalent h

-- A zero gap cannot be packaged as a separating experiment.
example : True := by
  fail_if_success have h : (0 : ℝ) < 0 := by norm_num
  trivial

-- A zero-effect readout cannot be complete (the missing proof is substantive).
example (bad : QIT.POVM Bool Bool) (h : ∀ o, bad.effects o = 0) : False := by
  have hc := congrArg (fun m => m false false) bad.sum_eq_one
  simp [h] at hc

noncomputable def complexInput : QIT.PureVector Bool where
  amp b := if b then 4 * Complex.I / 5 else 3 / 5
  trace_rankOne_eq_one := by
    apply Complex.ext <;> norm_num [QIT.rankOneMatrix, Matrix.vecMulVec,
      Matrix.trace, Fintype.sum_bool, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

example : (complexInput.state.matrix false false).re = 9 / 25 := by
  norm_num [complexInput, QIT.PureVector.state, QIT.rankOneMatrix, Matrix.vecMulVec,
    Complex.div_re, Complex.div_im]

example (ρ : QIT.State Bool) (t : FiniteQuantum.Test Bool Bool Bool) :
    ∑ o, t.prob ρ o = 1 := t.normalized ρ
