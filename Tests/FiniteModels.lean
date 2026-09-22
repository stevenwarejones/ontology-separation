import OntologySeparation.Experiments.ModelCompatibility

open OntologySeparation FiniteModels ModelCompatibility

example : Compatible fixed fair := fairMembership.compatible
example : ¬ Compatible fixed settingEcho := echo_not_compatible
example (w : Membership fixed settingEcho) : False := echoExclusion.excludes w.compatible

-- A target exactly on a bound is not a strict exclusion.
example : True := by
  fail_if_success have : (0 : ℝ) < 0 := by norm_num
  trivial

-- Negative weights are not allowed, even when a formal sum might fit some entries.
example (w : FiniteDistribution Bool) (h : w.mass false = -1) : False := by
  have hn := w.nonneg false
  rw [h] at hn
  linarith

example (p : Behavior binaryInterface) :
    ¬ Compatible (G := Empty) (fun g => nomatch g) p := by
  rintro ⟨w, _⟩
  have h := w.total
  simp at h

example : ¬ Compatible recordGenerator recordTarget := coherent_excludes_dephased_class

example (w : Membership fixed fair)
    (h1 : w.weights.mass true = 0) : False := by
  have h := w.reproduces false true
  norm_num [mixture, fixed, fair, Fintype.sum_bool, h1] at h
