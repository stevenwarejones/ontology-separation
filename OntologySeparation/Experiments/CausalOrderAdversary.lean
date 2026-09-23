import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Experiments.Research

/-! Structured-adversary check for P06.

The existing X/Z order-interference statistic is *not* a witness of indefinite
causal order by itself. A fixed-order X-then-Z circuit produces the same scalar
probability for every input vector. This converts the catalog warning into a
checked counterexample and blocks an invalid no-go claim. -/
namespace OntologySeparation.CausalOrderAdversary
open Research

inductive Implementation where
  | coherentOrder
  | fixedXZ
  deriving DecidableEq, Repr

def probability : Implementation → Vector → Rat
  | .coherentOrder, v => orderMinus v
  | .fixedXZ, v => normSq (xGate (zGate v))

def DefiniteOrder : Implementation → Prop
  | .coherentOrder => False
  | .fixedXZ => True

theorem zGate_norm (v : Vector) : normSq (zGate v) = normSq v := by
  simp [normSq, zGate]

theorem xGate_norm (v : Vector) : normSq (xGate v) = normSq v := by
  simp [normSq, xGate]

theorem fixedXZ_probability (v : Vector) :
    probability .fixedXZ v = normSq v := by
  simp [probability, xGate_norm, zGate_norm]

/-- Exact adversary: the definite-order implementation matches the current
coherent-order statistic for every input, not merely one calibration state. -/
theorem fixed_order_mimics_current_statistic (v : Vector) :
    probability .fixedXZ v = probability .coherentOrder v := by
  rw [fixedXZ_probability]
  simp [probability, order_probability]

/-- Therefore no choice of input vector makes this one statistic a separator
between the coherent-order implementation and the stated definite-order adversary. -/
theorem no_input_separates :
    ¬ ∃ v : Vector, probability .fixedXZ v ≠ probability .coherentOrder v := by
  rintro ⟨v, h⟩
  exact h (fixed_order_mimics_current_statistic v)

/-- A constructive definite-order countermodel exists for every proposed input. -/
theorem definite_order_countermodel (v : Vector) :
    ∃ d : Implementation, DefiniteOrder d ∧
      probability d v = probability .coherentOrder v :=
  ⟨.fixedXZ, trivial, fixed_order_mimics_current_statistic v⟩

end OntologySeparation.CausalOrderAdversary
