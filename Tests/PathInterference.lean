import OntologySeparation.Experiments.PathInterference

open OntologySeparation PathInterference FiniteModels ExperimentAccess

example : Compatible routeBehavior incoherent := incoherent_class_nonempty
example : ¬ Compatible routeBehavior coherent := excludes_incoherent
example : Compatible response coherent := contextualMembership.compatible

-- Coherent and transfer descriptions agree even when interference is accessible.
example : Equivalent predict (fun _ => True) .pathSum .transfer := descriptions_equivalent

-- Removing phase-sensitive access destroys this separator.
example : Equivalent predict (fun p => p = false) .pathSum .dephased := restricted_equivalent
example (s : Separator predict (fun p => p = false) .pathSum .dephased) : False :=
  s.not_equivalent restricted_equivalent

-- Enlarging the response class invalidates a sweeping classical-model exclusion.
example (h : ¬ Compatible response coherent) : False := h contextualMembership.compatible

-- Incoherent addition has no dark port; coherent cancellation does.
example : incoherent.prob false true = 1 / 2 := route_probability false false true
example : coherent.prob false true = 0 := by
  norm_num [coherent, path_probability]

example : ¬ Equivalent predict (fun _ => True) .pathSum .dephased := expanded_not_equivalent
