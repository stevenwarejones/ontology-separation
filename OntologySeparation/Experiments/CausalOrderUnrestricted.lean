import OntologySeparation.Experiments.CausalOrderTwoSetting

/-! A universal adversary for scalar causal-order tables.

If a definite-order implementation is permitted an unconstrained setting-dependent
reporting map after its fixed-order dynamics, then every scalar probability table
is reproducible.  Therefore no enlargement of the current P06 scalar table can
certify indefinite causal order without additional cross-setting calibration or
instrument constraints.

This is a scope theorem, not a claim about physically calibrated causal witnesses. -/

namespace OntologySeparation.CausalOrderUnrestricted
open Research CausalOrderAdversary CausalOrderTwoSetting

/-- A deliberately broad definite-order adversary: the physical order is fixed,
while the reported scalar statistic may depend arbitrarily on setting and input. -/
structure Model where
  report : Bool → Vector → Rat

def probability (m : Model) (setting : Bool) (v : Vector) : Rat :=
  m.report setting v

/-- Any proposed scalar table has an exact definite-order representative in this
unrestricted reporting class. -/
def fromTable (q : Bool → Vector → Rat) : Model where
  report := q

theorem fromTable_exact (q : Bool → Vector → Rat) (setting : Bool) (v : Vector) :
    probability (fromTable q) setting v = q setting v := rfl

/-- Universal mimicry: no scalar table can separate itself from this broad
definite-order class. -/
theorem every_scalar_table_mimicked (q : Bool → Vector → Rat) :
    ∃ m : Model, ∀ setting v, probability m setting v = q setting v :=
  ⟨fromTable q, fromTable_exact q⟩

/-- In particular, the refined P06 two-setting coherent table is exactly mimicked. -/
def coherentAdversary : Model :=
  fromTable coherentProbability

theorem coherent_table_mimicked (setting : Bool) (v : Vector) :
    probability coherentAdversary setting v = coherentProbability setting v := rfl

theorem no_scalar_separator_against_unrestricted :
    ¬ ∃ q : Bool → Vector → Rat,
      ∀ m : Model, ∃ setting v, probability m setting v ≠ q setting v := by
  rintro ⟨q, hq⟩
  obtain ⟨setting, v, hneq⟩ := hq (fromTable q)
  exact hneq (fromTable_exact q setting v)

/-- The previous two-setting separator is therefore only a separator against its
restricted fixed-sequence comparator, never against this unrestricted class. -/
theorem two_setting_not_witness_against_unrestricted :
    ∃ m : Model, ∀ setting v,
      probability m setting v = coherentProbability setting v :=
  every_scalar_table_mimicked coherentProbability

end OntologySeparation.CausalOrderUnrestricted
