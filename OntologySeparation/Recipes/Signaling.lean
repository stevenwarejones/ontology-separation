import OntologySeparation.Core.SharpOptimum
import OntologySeparation.Experiments.SignalingTradeoff

namespace OntologySeparation.SignalingStudy

/-- Allowed total-variation signaling, not a claim that the witness uses it all. -/
structure Study where
  budget : ℚ
  nonnegative : 0 ≤ budget

def design (budget : ℚ) (nonnegative : 0 ≤ budget := by norm_num) : Study :=
  ⟨budget, nonnegative⟩

def Study.ceiling (s : Study) : ℚ := min (6+8*s.budget) 8

def Study.usedSignaling (s : Study) : ℚ := min s.budget (1/4)

noncomputable def Study.optimum (s : Study) :
    SharpOptimum (fun m : HiddenInfluence.Model => HiddenInfluence.Within m.behavior s.budget)
      (fun m => HiddenInfluence.score m.behavior) (s.ceiling : ℝ) where
  upper m hm := by simpa [Study.ceiling] using HiddenInfluence.sharp_bound m s.budget hm
  model := HiddenInfluence.optimalModel s.budget (by exact_mod_cast s.nonnegative)
  satisfies := HiddenInfluence.optimal_budget _ _
  attains := by
    simpa [Study.ceiling] using HiddenInfluence.optimal_score (s.budget : ℝ)
      (show 0 ≤ (s.budget : ℝ) by exact_mod_cast s.nonnegative)

noncomputable def Study.boundClaim (s : Study) : Claim := s.optimum.boundClaim s.ceiling rfl
noncomputable def Study.attainmentClaim (s : Study) : Claim := s.optimum.witnessClaim s.ceiling rfl
noncomputable def Study.signalingClaim (s : Study) : Claim :=
  .exact s.optimum.model.signaling s.usedSignaling (by
    simpa [Study.optimum, Study.usedSignaling] using
      HiddenInfluence.optimal_signaling (s.budget : ℝ)
        (show 0 ≤ (s.budget : ℝ) by exact_mod_cast s.nonnegative))

end OntologySeparation.SignalingStudy
