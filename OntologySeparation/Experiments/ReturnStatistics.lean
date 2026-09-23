import OntologySeparation.Experiments.EnvironmentDiscrimination
import OntologySeparation.Statistics.FiniteShot

namespace OntologySeparation.ReturnStatistics
noncomputable section
open FiniteShot RecordEnvironment

/-- Exact prospective design for the specified return measurement. The slack is
an externally justified upper calibration allowance, not a fitted probability. -/
def design (shots : ℕ) (slack alpha : ℚ)
    (positiveShots : 0 < shots := by norm_num)
    (slackNonneg : 0 ≤ slack := by norm_num)
    (ceilingLeOne : 337/625 + slack ≤ 1 := by norm_num)
    (alphaPositive : 0 < alpha := by norm_num)
    (alphaLessOne : alpha < 1 := by norm_num)
    (adequate : (337/625 + slack)^shots ≤ alpha := by norm_num) : Plan where
  shots := shots
  positiveShots := positiveShots
  nullCeiling := 337/625 + slack
  nullNonneg := by linarith
  nullLeOne := ceilingLeOne
  alpha := alpha
  alphaPositive := alphaPositive
  alphaLessOne := alphaLessOne
  adequate := adequate

/-- The operational premise to justify experimentally for the actual block.
It refers to the proved Born probability, plus allowance, after each preceding
success. It is not inferred from the observed test block. -/
def CalibratedNull {n : ℕ} (trials : Trials n) (slack : ℝ) : Prop :=
  ∀ k, k < n → prefixMass trials (k+1) ≤
    (returnTest.prob collapsed true + slack) * prefixMass trials k

theorem calibrated_null {n : ℕ} (trials : Trials n) (slack : ℚ)
    (h : CalibratedNull trials (slack : ℝ)) :
    NullBound trials ((337/625 + slack : ℚ) : ℝ) := by
  intro k hk
  have hh := h k hk
  rw [return_collapsed] at hh
  norm_num at hh ⊢
  exact hh

/-- Recovery loss bounds the decrease of the return success probability under
coherent dynamics. It is a separate physical assumption used for power only. -/
def RecoveryGuarantee {n : ℕ} (trials : Trials n) (loss : ℝ) : Prop :=
  ∀ k, k < n → (returnTest.prob coherent true - loss) * prefixMass trials k ≤
    prefixMass trials (k+1)

theorem recovery_power {n : ℕ} (trials : Trials n) (loss : ℝ)
    (hl : loss ≤ 1) (h : RecoveryGuarantee trials loss) :
    (1-loss)^n ≤ prefixMass trials n := by
  apply power_bound trials _ (sub_nonneg.mpr hl)
  intro k hk
  simpa [return_coherent] using h k hk

/-- Physical calibration premise is retained in the exported theorem. -/
theorem calibrated_valid (shots : ℕ) (slack alpha : ℚ)
    (hn : 0 < shots) (hs : 0 ≤ slack) (hq : 337/625 + slack ≤ 1)
    (ha : 0 < alpha) (ha1 : alpha < 1) (adequate : (337/625 + slack)^shots ≤ alpha)
    (trials : Trials shots) (h : CalibratedNull trials (slack : ℝ)) :
    prefixMass trials shots ≤ (alpha : ℝ) :=
  (design shots slack alpha hn hs hq ha ha1 adequate).valid trials
    (calibrated_null trials slack h)

/-- Report a conditional power theorem, with its threshold derived from loss. -/
def powerClaim (shots : ℕ) (loss : ℚ)
    (hl0 : 0 ≤ loss := by norm_num) (hl1 : loss ≤ 1 := by norm_num) : Claim :=
  .realizedBound (fun trials : Trials shots => RecoveryGuarantee trials (loss : ℝ))
    (fun trials => 1 - prefixMass trials shots) (1 - (1-loss)^shots)
    (fun trials h => by
      have hh := recovery_power trials (loss : ℝ) (by exact_mod_cast hl1) h
      push_cast
      linarith)
    (point (fun _ : Fin shots => true))
    (by
      intro k hk
      simp [return_coherent, survives]
      exact_mod_cast hl0)
end
end OntologySeparation.ReturnStatistics
