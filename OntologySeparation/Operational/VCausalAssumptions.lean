import OntologySeparation.Operational.VCausal

namespace OntologySeparation.VCausal
noncomputable section
open scoped BigOperators

/-- Later filtering is not covered by the preceding theorems. Independent fair
local outputs, accepted only when parity matches the input product, satisfy
all four PR-box parity constraints after selection. -/
def postselect (x z a c : Bool) : Bool := (a != c) == (x && z)

theorem postselection_parity (x z a c : Bool) :
    postselect x z a c = true ↔ (a != c) = (x && z) := by
  cases x <;> cases z <;> cases a <;> cases c <;> decide

/-- Exactly half of the four equally likely local-output pairs are retained,
for every input. Constant acceptance rate does not repair this selection. -/
theorem postselection_half : ∀ x z : Bool,
    (∑ a : Bool, ∑ c : Bool, if postselect x z a c then (1 : ℚ)/4 else 0) = 1/2 := by
  decide +kernel

/-- No fixed local response tables satisfy all of those selected parities. -/
theorem postselection_not_local : ¬ ∃ a c : Bool → Bool,
    ∀ x z, (a x != c z) = (x && z) := by
  decide +kernel

/-- A measurement-dependent shared seed can encode both actual inputs. The
response functions themselves remain local in the supplied seed and input. -/
def dependentSeed (x z : Bool) : Bool × Bool := (x,z)
def seedA (_ : Bool × Bool) (_ : Bool) : Bool := false
def seedC (seed : Bool × Bool) (_ : Bool) : Bool := seed.1 && seed.2

theorem measurement_dependence_parity (x z : Bool) :
    (seedA (dependentSeed x z) x != seedC (dependentSeed x z) z) = (x && z) := by
  cases x <;> cases z <;> decide

/-- A normalized PR-box table has no operational signal in either marginal,
yet no deterministic Bell-local table can meet its certain parity constraints.
No-signaling is therefore not a replacement for classical screening-off. -/
def nonsignalingBox (x z a c : Bool) : ℚ :=
  if (a != c) = (x && z) then 1/2 else 0

theorem nonsignalingBox_marginals : ∀ x z a c : Bool,
    (∑ c' : Bool, nonsignalingBox x z a c') = 1/2 ∧
    (∑ a' : Bool, nonsignalingBox x z a' c) = 1/2 := by
  decide +kernel

end
end OntologySeparation.VCausal
