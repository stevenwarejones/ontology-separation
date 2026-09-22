import OntologySeparation.Recipes
import OntologySeparation.Recipes.Separation
import OntologySeparation.LocalFriendliness
import OntologySeparation.Core.ExperimentAccess
import OntologySeparation.Core.RegisterAccess
import OntologySeparation.Core.Comparison
import OntologySeparation.Core.ExactFinite
import OntologySeparation.Core.ExactFiniteChecker
import OntologySeparation.Core.AutomaticGrid
import OntologySeparation.Core.SeparatorSearch
import OntologySeparation.Core.FiniteModels
import OntologySeparation.Experiments.RecordAccess
import OntologySeparation.Experiments.PartialLeakage
import OntologySeparation.Experiments.PartialLeakageRobustness
import OntologySeparation.Adapters.FiniteCircuit
import OntologySeparation.Experiments.ModelCompatibility
import OntologySeparation.Reporting.Claim
import OntologySeparation.Reporting.Comparison

/-! Stable imports for adopters building supported checked studies.

This module intentionally exposes the existing recipe workflows and comparison
certificates without requiring adopters to know the internal directory layout.
It does not add a new semantics or broaden the scope of any theorem. -/
