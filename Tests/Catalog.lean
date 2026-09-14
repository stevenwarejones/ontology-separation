import OntologySeparation.Catalog.Matrix
import OntologySeparation.Models.Memory

open OntologySeparation OntologySeparation.Catalog

example : scenarios.length = 14 := by decide
example : models.length = 7 := by decide
example : matrix.length = 98 := by decide
example : missingCapabilities [] b04.protocol = ["physical_memory", "coherent_reversal"] := by decide
example : missingCapabilities ["physical_memory", "coherent_reversal"] b04.protocol = [] := by decide

-- These compare interpreter outputs, not duplicated numeric metadata.
example : Memory.probability Memory.unitary Memory.echo = 1 := by
  rw [Memory.echo_probability]; norm_num [Memory.unitary]
example : Memory.probability Memory.collapse Memory.echo = 1/2 := by
  rw [Memory.echo_probability]; norm_num [Memory.collapse]
example : Memory.probability Memory.halfDephasing Memory.phaseEcho = 1/4 := by
  rw [Memory.phaseEcho_probability]; norm_num [Memory.halfDephasing]

-- Conditional extensions are explicit; none silently becomes a native prediction.
example : (matrix.filter (fun c => c.status == .requiresExtension)).length = 0 := by decide
example : extensions.length = 7 := by decide
example : (evaluate b01 ⟨"local_friendliness", "LF", "assumption class", "three settings"⟩).status = .verifiedWitness := by decide
