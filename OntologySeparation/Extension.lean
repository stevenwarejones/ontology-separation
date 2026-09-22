import OntologySeparation.Core.Operational
import OntologySeparation.Core.ExperimentAccess
import OntologySeparation.Core.FiniteModels
import OntologySeparation.Core.Claim
import OntologySeparation.Reporting.Claim
import OntologySeparation.Adapters.FiniteQuantum

/-! Stable imports for extending the framework with new physical models or adapters.

Use this module when a supported recipe cannot express the intended preparation,
operation, measurement, or access policy. The imported APIs keep theory-independent
experiment access and finite-model reasoning separate from the quantum adapter. -/

