import OntologySeparation.Study
import OntologySeparation.Extension

open OntologySeparation

-- The adopter facade exposes normalized behaviors and proof-bearing comparison APIs.
example {E : Interface} (p : Behavior E) (s : E.Setting) :
    ∑ o, p.prob s o = 1 := p.normalized s

example {M P : Type} {E : Interface}
    (predict : ExperimentAccess.Predictions M P E) (a : M) :
    ExperimentAccess.Equivalent predict (fun _ => True) a a :=
  ExperimentAccess.Equivalent.refl predict (fun _ => True) a

-- The extension facade exposes the general finite-quantum test type without
-- changing the trusted definition of states, channels, or POVMs.
#check FiniteQuantum.Test
#check FiniteModels.Membership
#check ExperimentAccess.Separator
