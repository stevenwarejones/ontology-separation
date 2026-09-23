import OntologySeparation.Operational.HiddenInfluence

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators
namespace LP
abbrev massColumn (j : Atom) : ForcedSignaling.Column := Fin.castAdd 128 j
abbrev slackColumn (c : Context) (o : Recipient) : ForcedSignaling.Column :=
  Fin.natAdd 256 (finProdFinEquiv (c,o))
def absRow (c : Context) (o : Recipient) (negative : Bool) : ForcedSignaling.Row :=
  ⟨16*c.val + 2*o.val + negative.toNat, by cases negative <;> simp <;> omega⟩
def tvRow (c : Context) : ForcedSignaling.Row := ⟨256+c.val, by omega⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Independent response/observable definitions reproduce the LP's coefficients. -/
theorem objective_mass : ∀ j : Atom,
    ForcedSignaling.objective (massColumn j) = scoreCoeff j := by decide

theorem objective_slack : ∀ c o, ForcedSignaling.objective (slackColumn c o) = 0 := by decide

theorem normalization_mass : ∀ e j,
    ForcedSignaling.normalization e (massColumn j) = if early j = e then 1 else 0 := by decide

theorem normalization_slack : ∀ e c o,
    ForcedSignaling.normalization e (slackColumn c o) = 0 := by decide

theorem abs_mass : ∀ c o n j,
    ForcedSignaling.constraint (absRow c o n) (massColumn j) =
      if n then -differenceCoeff c o j else differenceCoeff c o j := by decide

theorem abs_slack : ∀ c o n d r,
    ForcedSignaling.constraint (absRow c o n) (slackColumn d r) =
      if c = d ∧ o = r then -1 else 0 := by decide

theorem tv_mass : ∀ c j,
    ForcedSignaling.constraint (tvRow c) (massColumn j) = 0 := by decide

theorem tv_slack : ∀ c d r,
    ForcedSignaling.constraint (tvRow c) (slackColumn d r) =
      if c = d then 1 else 0 := by decide

end LP

end OntologySeparation.HiddenInfluence
