import OntologySeparation.Operational.HiddenInfluenceStrategies
import OntologySeparation.Operational.HiddenInfluenceCausality

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators

namespace Sharp
/-- Exact rational witness found by an untrusted LP search; all properties below
are rederived from the normalized physical behavior by the Lean kernel. -/
def atoms (k : Fin 26) : Atom :=
  (#[0,2,17,44,46,61,64,65,82,110,124,125,136,138,149,164,166,185,
      192,202,216,220,225,230,244,253] : Array Atom)[k.val]
def numerator (k : Fin 26) : ℤ :=
  (#[2,1,1,2,1,1,2,1,1,1,2,1,2,1,1,2,1,1,1,1,1,1,1,1,1,1] : Array ℤ)[k.val]

set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem numerator_nonneg : ∀ k, 0 ≤ numerator k := by decide
private theorem totals : ∀ e : Early,
    (∑ k : Fin 26, if early (atoms k) = e then numerator k else 0) = 8 := by decide
private theorem score_numerator : (∑ k : Fin 26, scoreCoeff (atoms k) * numerator k) = 64 := by decide

/-- Actual signed recipient differences, in units of 1/8. -/
def diffNumerator (c : Context) (o : Recipient) : ℤ :=
  if c.val = 5 ∨ c.val = 7 then
    (#[1,-1,-1,1,0,0,0,0] : Array ℤ)[o.val]
  else if c.val = 12 then (#[0,0,-1,1,0,0,1,-1] : Array ℤ)[o.val]
  else if c.val = 14 then (#[-1,1,0,0,1,-1,0,0] : Array ℤ)[o.val]
  else 0
private theorem differences : ∀ c o,
    (∑ k : Fin 26, differenceCoeff c o (atoms k) * numerator k) = diffNumerator c o := by decide

noncomputable def model : Model := Model.ofAtoms atoms (fun k => (numerator k : ℝ) / 8)
  (fun k => div_nonneg (by exact_mod_cast numerator_nonneg k) (by norm_num))
  (fun e => by
    have h : (∑ k : Fin 26, if early (atoms k) = e then (numerator k : ℝ) else 0) = 8 := by
      exact_mod_cast totals e
    have hh := congrArg (fun x : ℝ => x / 8) h
    simpa [Finset.sum_div, ite_div] using hh)

theorem score_exact : score model.behavior = 8 := by
  rw [model, ofAtoms_score]
  have h : (∑ k : Fin 26, (scoreCoeff (atoms k) : ℝ) * numerator k) = 64 := by
    exact_mod_cast score_numerator
  convert congrArg (fun x : ℝ => x / 8) h using 1 <;>
    norm_num [Finset.sum_div, mul_div_assoc]

theorem difference_exact (c : Context) (o : Recipient) :
    difference model.behavior c o = (diffNumerator c o : ℝ) / 8 := by
  rw [model, ofAtoms_difference]
  have h : (∑ k : Fin 26, (differenceCoeff c o (atoms k) : ℝ) * numerator k) = diffNumerator c o := by
    exact_mod_cast differences c o
  simpa [Finset.sum_div, mul_div_assoc] using congrArg (fun x : ℝ => x / 8) h

theorem tv_exact (c : Context) : tv model.behavior c =
    if c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14 then 1/4 else 0 := by
  fin_cases c <;> norm_num [tv, difference_exact, diffNumerator, Fin.sum_univ_succ]

theorem budget : Within model.behavior (1/4) := by
  intro c
  rw [tv_exact]
  split <;> norm_num

theorem signaling_exact : model.signaling = 1/4 := by
  apply le_antisymm ((signaling_le_iff _ _).mpr budget)
  have h := tv_le_signaling model 5
  simpa [tv_exact] using h
end Sharp

end OntologySeparation.HiddenInfluence
