import OntologySeparation.Operational.HiddenInfluence

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators

def lateChoice (y z : Fin 2) : Late := ⟨2*y.val+z.val, by omega⟩
def recipientB (o : Outcome) : Recipient := ⟨4*(o.val/8)+o.val%4, by omega⟩
def recipientC (o : Outcome) : Recipient := ⟨4*(o.val/8)+2*(o.val/4%2)+o.val%2, by omega⟩

set_option maxRecDepth 100000 in
private theorem output_without_B : ∀ j z,
    recipientB (output j (lateChoice 0 z)) = recipientB (output j (lateChoice 1 z)) := by decide
set_option maxRecDepth 100000 in
private theorem output_without_C : ∀ j y,
    recipientC (output j (lateChoice y 0)) = recipientC (output j (lateChoice y 1)) := by decide

/-- Changing B's setting cannot change the joint A,C,D distribution. -/
theorem no_signaling_B (m : Model) (e : Early) (z : Fin 2) (o : Recipient) :
    marginal m.behavior e (lateChoice 0 z) recipientB o =
      marginal m.behavior e (lateChoice 1 z) recipientB o := by
  simp only [marginal, mean_eq, output_without_B]

/-- Changing C's setting cannot change the joint A,B,D distribution. -/
theorem no_signaling_C (m : Model) (e : Early) (y : Fin 2) (o : Recipient) :
    marginal m.behavior e (lateChoice y 0) recipientC o =
      marginal m.behavior e (lateChoice y 1) recipientC o := by
  simp only [marginal, mean_eq, output_without_C]

/-- Maximum early-setting recipient TV. For this model the two other senders
have exactly zero signaling, by `no_signaling_B/C`, so this is the full strength. -/
noncomputable def Model.signaling (m : Model) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (tv m.behavior)

theorem signaling_le_iff (m : Model) (delta : ℝ) :
    m.signaling ≤ delta ↔ Within m.behavior delta := by
  simp [Model.signaling, Finset.sup'_le_iff, Within]

theorem tv_le_signaling (m : Model) (c : Context) : tv m.behavior c ≤ m.signaling :=
  Finset.le_sup' (tv m.behavior) (Finset.mem_univ c)

theorem signaling_nonnegative (m : Model) : 0 ≤ m.signaling :=
  le_trans (by unfold tv; positivity) (tv_le_signaling m 0)
end OntologySeparation.HiddenInfluence
