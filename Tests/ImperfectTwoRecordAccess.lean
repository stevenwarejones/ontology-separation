import OntologySeparation.Experiments.ImperfectTwoRecordAccess

namespace Tests.ImperfectTwoRecordAccess
open OntologySeparation
open OntologySeparation.ImperfectTwoRecordAccess

example (m : TwoLeakage) :
    distanceA m = 12/25 * m.second.overlap ∧
      distanceB m = 12/25 * m.first.overlap :=
  distance_pair_exact m

example (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 12/25)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 12/25) :
    ∃ m : TwoLeakage, distanceA m = x ∧ distanceB m = y :=
  attainable_square x y hx0 hx1 hy0 hy1

example (x y : ℝ) :
    (∃ m : TwoLeakage, distanceA m = x ∧ distanceB m = y) ↔
      0 ≤ x ∧ x ≤ 12/25 ∧ 0 ≤ y ∧ y ≤ 12/25 :=
  attainable_region_iff x y

example :
    let z := PartialEnvironment.Leakage.ofOverlap 0 (by norm_num) (by norm_num)
    let m : TwoLeakage := { first := z, second := z }
    distanceA m = 0 ∧ distanceB m = 0 :=
  perfect_copy_corner

end Tests.ImperfectTwoRecordAccess
