import OntologySeparation.Experiments.ForcedSignalingCertificateModel
import OntologySeparation.Operational.HiddenInfluenceCausality

namespace OntologySeparation.ForcedSignalingPropositionWitnesses
noncomputable section
open scoped BigOperators
open HiddenInfluence
open ForcedSignalingLC4
open ForcedSignalingLC4Witness
open ForcedSignalingCertificateModel
open ForcedSignalingDirectional


namespace DirectionalA

def weightQ2 (j : Atom) : Q2 :=
  match j.val with
  | 0 => qrat (1/8)
  | 2 => q (-1/8) (1/8)
  | 6 => q (1/8) (-1/16)
  | 10 => q (1/8) (-1/16)
  | 17 => q (-1/8) (1/8)
  | 19 => qrat (1/8)
  | 21 => q (1/8) (-1/16)
  | 25 => q (1/8) (-1/16)
  | 34 => q (1/8) (-1/16)
  | 44 => qrat (1/8)
  | 46 => q (0) (1/16)
  | 49 => q (1/8) (-1/16)
  | 61 => q (0) (1/16)
  | 63 => qrat (1/8)
  | 64 => q (0) (1/16)
  | 65 => qrat (1/8)
  | 76 => q (1/8) (-1/16)
  | 82 => qrat (1/8)
  | 83 => q (-1/8) (1/8)
  | 87 => q (1/8) (-1/16)
  | 91 => q (1/8) (-1/16)
  | 102 => q (1/8) (-1/16)
  | 106 => q (1/8) (-1/16)
  | 110 => q (-1/8) (1/8)
  | 111 => qrat (1/8)
  | 113 => q (1/8) (-1/16)
  | 124 => qrat (1/8)
  | 125 => q (0) (1/16)
  | 128 => q (1/8) (-1/16)
  | 136 => q (-1/8) (1/8)
  | 138 => qrat (1/8)
  | 140 => q (1/8) (-1/16)
  | 149 => q (0) (1/16)
  | 151 => qrat (1/8)
  | 153 => q (1/8) (-1/16)
  | 160 => q (1/8) (-1/16)
  | 164 => q (-1/8) (1/8)
  | 166 => qrat (1/8)
  | 172 => q (1/8) (-1/16)
  | 177 => q (1/8) (-1/16)
  | 185 => q (-1/8) (1/8)
  | 187 => qrat (1/8)
  | 189 => q (1/8) (-1/16)
  | 192 => q (1/8) (-1/16)
  | 197 => q (0) (1/16)
  | 202 => q (0) (1/16)
  | 207 => q (1/8) (-1/16)
  | 211 => q (1/8) (-1/16)
  | 215 => q (0) (1/16)
  | 216 => q (0) (1/16)
  | 220 => q (1/8) (-1/16)
  | 225 => q (1/8) (-1/16)
  | 230 => q (0) (1/16)
  | 233 => q (0) (1/16)
  | 238 => q (1/8) (-1/16)
  | 242 => q (1/8) (-1/16)
  | 244 => q (0) (1/16)
  | 251 => q (0) (1/16)
  | 253 => q (1/8) (-1/16)
  | _ => 0

set_option maxRecDepth 100000 in
private theorem weight_allowed (j : Atom) : AllowedWeight (weightQ2 j) := by
  fin_cases j <;> simp [AllowedWeight, weightQ2]

theorem weight_nonnegative (j : Atom) : 0 ≤ Q2.toReal (weightQ2 j) :=
  allowedWeight_nonnegative (weight_allowed j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalsQ2 : ∀ e : Early,
    (∑ j : Atom, if early j = e then weightQ2 j else 0) = qrat 1 := by
  with_unfolding_all decide +kernel

noncomputable def model : Model :=
  modelOfWeight weightQ2 weight_nonnegative totalsQ2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem abd_matches_q2 :
    ∀ x y ww a b d,
      abdQ2 weightQ2 x y ww a b d = ForcedSignalingLC4.abd x y ww a b d := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem acd_matches_q2 :
    ∀ x z ww a c d,
      acdQ2 weightQ2 x z ww a c d = ForcedSignalingLC4.acd x z ww a c d := by
  with_unfolding_all decide +kernel

theorem matchesCluster : ForcedSignalingTheorem2.MatchesCluster model where
  abd x y ww a b d := by
    calc
      modelABD model x y ww a b d =
          Q2.toReal (abdQ2 weightQ2 x y ww a b d) :=
        modelABD_eq weightQ2 weight_nonnegative totalsQ2 x y ww a b d
      _ = _ := congrArg Q2.toReal (abd_matches_q2 x y ww a b d)
  acd x z ww a c d := by
    calc
      modelACD model x z ww a c d =
          Q2.toReal (acdQ2 weightQ2 x z ww a c d) :=
        modelACD_eq weightQ2 weight_nonnegative totalsQ2 x z ww a c d
      _ = _ := congrArg Q2.toReal (acd_matches_q2 x z ww a c d)

def epsilonQ2 : Q2 := q (-1/8) (1/8)
def deltaQ2 : Q2 := q (-1/2) (1/2)
noncomputable def delta : ℝ := Q2.toReal deltaQ2

theorem epsilon_nonnegative : 0 ≤ Q2.toReal epsilonQ2 := by
  simp [epsilonQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem delta_nonnegative : 0 ≤ delta := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem difference_exact (c : Context) (o : Recipient) :
    difference model.behavior c o = Q2.toReal (diffQ2 weightQ2 c o) :=
  difference_eq_toReal weightQ2 weight_nonnegative totalsQ2 c o

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_active : ∀ c o,
    if c.val = 5 ∨ c.val = 7 then
      diffQ2 weightQ2 c o = epsilonQ2 ∨ diffQ2 weightQ2 c o = -epsilonQ2
    else diffQ2 weightQ2 c o = 0 := by
  with_unfolding_all decide +kernel

private theorem abs_difference_exact (c : Context) (o : Recipient) :
    |difference model.behavior c o| =
      if c.val = 5 ∨ c.val = 7 then Q2.toReal epsilonQ2 else 0 := by
  have h := diff_active c o
  by_cases hc : c.val = 5 ∨ c.val = 7
  · simp only [hc, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [difference_exact, h, abs_of_nonneg epsilon_nonnegative]
    · rw [difference_exact, h]
      have hn : Q2.toReal (-epsilonQ2) = -Q2.toReal epsilonQ2 := by
        simp [Q2.toReal]
        ring
      rw [hn, abs_neg, abs_of_nonneg epsilon_nonnegative]
  · simp only [hc, ↓reduceIte] at h ⊢
    rw [difference_exact, h]
    simp

theorem tv_exact (c : Context) :
    tv model.behavior c =
      if c.val = 5 ∨ c.val = 7 then delta else 0 := by
  unfold tv
  simp_rw [abs_difference_exact]
  by_cases hc : c.val = 5 ∨ c.val = 7
  · simp [hc, epsilonQ2, delta, deltaQ2, Q2.toReal, q, qrat]
    ring
  · simp [hc]

theorem deltaA_exact : deltaA model = delta := by
  apply le_antisymm
  · unfold deltaA
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextA, delta_nonnegative]
  · have h := tv_le_deltaA model ⟨5, by norm_num⟩
    rw [tv_exact] at h
    norm_num [contextA] at h
    exact h

theorem deltaD_exact : deltaD model = 0 := by
  apply le_antisymm
  · unfold deltaD
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextD, delta_nonnegative]
  · exact deltaD_nonnegative model

theorem delta_value : delta = (Real.sqrt 2 - 1) / 2 := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  ring

end DirectionalA

namespace DirectionalD

def weightQ2 (j : Atom) : Q2 :=
  match j.val with
  | 0 => q (0) (1/16)
  | 2 => qrat (1/8)
  | 12 => q (1/8) (-1/16)
  | 17 => qrat (1/8)
  | 19 => q (-1/8) (1/8)
  | 23 => q (1/8) (-1/16)
  | 27 => q (1/8) (-1/16)
  | 32 => q (1/8) (-1/16)
  | 44 => q (0) (1/16)
  | 46 => qrat (1/8)
  | 55 => q (1/8) (-1/16)
  | 59 => q (1/8) (-1/16)
  | 61 => qrat (1/8)
  | 63 => q (-1/8) (1/8)
  | 64 => q (-1/8) (1/8)
  | 65 => qrat (1/8)
  | 68 => q (1/8) (-1/16)
  | 72 => q (1/8) (-1/16)
  | 82 => qrat (1/8)
  | 83 => q (-1/8) (1/8)
  | 87 => q (1/8) (-1/16)
  | 91 => q (1/8) (-1/16)
  | 102 => q (1/8) (-1/16)
  | 106 => q (1/8) (-1/16)
  | 110 => q (-1/8) (1/8)
  | 111 => qrat (1/8)
  | 113 => q (1/8) (-1/16)
  | 124 => qrat (1/8)
  | 125 => q (0) (1/16)
  | 128 => q (1/8) (-1/16)
  | 136 => q (-1/8) (1/8)
  | 138 => qrat (1/8)
  | 140 => q (1/8) (-1/16)
  | 145 => q (1/8) (-1/16)
  | 149 => q (-1/8) (1/8)
  | 151 => qrat (1/8)
  | 157 => q (1/8) (-1/16)
  | 160 => q (1/8) (-1/16)
  | 164 => q (-1/8) (1/8)
  | 166 => qrat (1/8)
  | 172 => q (1/8) (-1/16)
  | 181 => q (1/8) (-1/16)
  | 185 => q (0) (1/16)
  | 187 => qrat (1/8)
  | 192 => q (0) (1/16)
  | 199 => q (1/8) (-1/16)
  | 200 => q (1/8) (-1/16)
  | 207 => q (0) (1/16)
  | 211 => q (0) (1/16)
  | 213 => q (1/8) (-1/16)
  | 218 => q (1/8) (-1/16)
  | 220 => q (0) (1/16)
  | 225 => q (0) (1/16)
  | 228 => q (1/8) (-1/16)
  | 235 => q (1/8) (-1/16)
  | 238 => q (0) (1/16)
  | 242 => q (0) (1/16)
  | 246 => q (1/8) (-1/16)
  | 249 => q (1/8) (-1/16)
  | 253 => q (0) (1/16)
  | _ => 0

set_option maxRecDepth 100000 in
private theorem weight_allowed (j : Atom) : AllowedWeight (weightQ2 j) := by
  fin_cases j <;> simp [AllowedWeight, weightQ2]

theorem weight_nonnegative (j : Atom) : 0 ≤ Q2.toReal (weightQ2 j) :=
  allowedWeight_nonnegative (weight_allowed j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalsQ2 : ∀ e : Early,
    (∑ j : Atom, if early j = e then weightQ2 j else 0) = qrat 1 := by
  with_unfolding_all decide +kernel

noncomputable def model : Model :=
  modelOfWeight weightQ2 weight_nonnegative totalsQ2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem abd_matches_q2 :
    ∀ x y ww a b d,
      abdQ2 weightQ2 x y ww a b d = ForcedSignalingLC4.abd x y ww a b d := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem acd_matches_q2 :
    ∀ x z ww a c d,
      acdQ2 weightQ2 x z ww a c d = ForcedSignalingLC4.acd x z ww a c d := by
  with_unfolding_all decide +kernel

theorem matchesCluster : ForcedSignalingTheorem2.MatchesCluster model where
  abd x y ww a b d := by
    calc
      modelABD model x y ww a b d =
          Q2.toReal (abdQ2 weightQ2 x y ww a b d) :=
        modelABD_eq weightQ2 weight_nonnegative totalsQ2 x y ww a b d
      _ = _ := congrArg Q2.toReal (abd_matches_q2 x y ww a b d)
  acd x z ww a c d := by
    calc
      modelACD model x z ww a c d =
          Q2.toReal (acdQ2 weightQ2 x z ww a c d) :=
        modelACD_eq weightQ2 weight_nonnegative totalsQ2 x z ww a c d
      _ = _ := congrArg Q2.toReal (acd_matches_q2 x z ww a c d)

def epsilonQ2 : Q2 := q (-1/8) (1/8)
def deltaQ2 : Q2 := q (-1/2) (1/2)
noncomputable def delta : ℝ := Q2.toReal deltaQ2

theorem epsilon_nonnegative : 0 ≤ Q2.toReal epsilonQ2 := by
  simp [epsilonQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem delta_nonnegative : 0 ≤ delta := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem difference_exact (c : Context) (o : Recipient) :
    difference model.behavior c o = Q2.toReal (diffQ2 weightQ2 c o) :=
  difference_eq_toReal weightQ2 weight_nonnegative totalsQ2 c o

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_active : ∀ c o,
    if c.val = 12 ∨ c.val = 14 then
      diffQ2 weightQ2 c o = epsilonQ2 ∨ diffQ2 weightQ2 c o = -epsilonQ2
    else diffQ2 weightQ2 c o = 0 := by
  with_unfolding_all decide +kernel

private theorem abs_difference_exact (c : Context) (o : Recipient) :
    |difference model.behavior c o| =
      if c.val = 12 ∨ c.val = 14 then Q2.toReal epsilonQ2 else 0 := by
  have h := diff_active c o
  by_cases hc : c.val = 12 ∨ c.val = 14
  · simp only [hc, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [difference_exact, h, abs_of_nonneg epsilon_nonnegative]
    · rw [difference_exact, h]
      have hn : Q2.toReal (-epsilonQ2) = -Q2.toReal epsilonQ2 := by
        simp [Q2.toReal]
        ring
      rw [hn, abs_neg, abs_of_nonneg epsilon_nonnegative]
  · simp only [hc, ↓reduceIte] at h ⊢
    rw [difference_exact, h]
    simp

theorem tv_exact (c : Context) :
    tv model.behavior c =
      if c.val = 12 ∨ c.val = 14 then delta else 0 := by
  unfold tv
  simp_rw [abs_difference_exact]
  by_cases hc : c.val = 12 ∨ c.val = 14
  · simp [hc, epsilonQ2, delta, deltaQ2, Q2.toReal, q, qrat]
    ring
  · simp [hc]

theorem deltaA_exact : deltaA model = 0 := by
  apply le_antisymm
  · unfold deltaA
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextA, delta_nonnegative]
  · exact deltaA_nonnegative model

theorem deltaD_exact : deltaD model = delta := by
  apply le_antisymm
  · unfold deltaD
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextD, delta_nonnegative]
  · have h := tv_le_deltaD model ⟨4, by norm_num⟩
    rw [tv_exact] at h
    norm_num [contextD] at h
    exact h

theorem delta_value : delta = (Real.sqrt 2 - 1) / 2 := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  ring

end DirectionalD

namespace InvisibleA

def weightQ2 (j : Atom) : Q2 :=
  match j.val with
  | 0 => q (0) (1/16)
  | 2 => qrat (1/8)
  | 12 => q (1/8) (-1/16)
  | 17 => qrat (1/8)
  | 19 => q (0) (1/16)
  | 31 => q (1/8) (-1/16)
  | 36 => q (1/8) (-1/16)
  | 40 => q (1/8) (-1/16)
  | 44 => q (-1/8) (1/8)
  | 46 => qrat (1/8)
  | 55 => q (1/8) (-1/16)
  | 59 => q (1/8) (-1/16)
  | 61 => qrat (1/8)
  | 63 => q (-1/8) (1/8)
  | 64 => q (0) (1/16)
  | 65 => qrat (1/8)
  | 76 => q (1/8) (-1/16)
  | 82 => qrat (1/8)
  | 83 => q (-1/8) (1/8)
  | 87 => q (1/8) (-1/16)
  | 91 => q (1/8) (-1/16)
  | 99 => q (1/8) (-1/16)
  | 110 => qrat (1/8)
  | 111 => q (0) (1/16)
  | 116 => q (1/8) (-1/16)
  | 120 => q (1/8) (-1/16)
  | 124 => q (-1/8) (1/8)
  | 125 => qrat (1/8)
  | 128 => q (1/8) (-1/16)
  | 136 => q (-1/8) (1/8)
  | 138 => qrat (1/8)
  | 140 => q (1/8) (-1/16)
  | 149 => qrat (1/8)
  | 151 => q (0) (1/16)
  | 155 => q (1/8) (-1/16)
  | 160 => q (1/8) (-1/16)
  | 164 => q (-1/8) (1/8)
  | 166 => qrat (1/8)
  | 172 => q (1/8) (-1/16)
  | 179 => q (1/8) (-1/16)
  | 185 => qrat (1/8)
  | 187 => q (-1/8) (1/8)
  | 191 => q (1/8) (-1/16)
  | 193 => q (1/8) (-1/16)
  | 197 => q (1/8) (-1/16)
  | 199 => q (-1/8) (1/8)
  | 200 => q (-1/8) (1/8)
  | 202 => q (1/8) (-1/16)
  | 206 => q (1/8) (-1/16)
  | 210 => q (1/8) (-1/16)
  | 213 => q (0) (1/16)
  | 218 => q (0) (1/16)
  | 221 => q (1/8) (-1/16)
  | 225 => q (1/8) (-1/16)
  | 228 => q (-1/8) (1/8)
  | 230 => q (1/8) (-1/16)
  | 233 => q (1/8) (-1/16)
  | 235 => q (-1/8) (1/8)
  | 238 => q (1/8) (-1/16)
  | 242 => q (1/8) (-1/16)
  | 246 => q (0) (1/16)
  | 249 => q (0) (1/16)
  | 253 => q (1/8) (-1/16)
  | _ => 0

set_option maxRecDepth 100000 in
private theorem weight_allowed (j : Atom) : AllowedWeight (weightQ2 j) := by
  fin_cases j <;> simp [AllowedWeight, weightQ2]

theorem weight_nonnegative (j : Atom) : 0 ≤ Q2.toReal (weightQ2 j) :=
  allowedWeight_nonnegative (weight_allowed j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalsQ2 : ∀ e : Early,
    (∑ j : Atom, if early j = e then weightQ2 j else 0) = qrat 1 := by
  with_unfolding_all decide +kernel

noncomputable def model : Model :=
  modelOfWeight weightQ2 weight_nonnegative totalsQ2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem abd_matches_q2 :
    ∀ x y ww a b d,
      abdQ2 weightQ2 x y ww a b d = ForcedSignalingLC4.abd x y ww a b d := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem acd_matches_q2 :
    ∀ x z ww a c d,
      acdQ2 weightQ2 x z ww a c d = ForcedSignalingLC4.acd x z ww a c d := by
  with_unfolding_all decide +kernel

theorem matchesCluster : ForcedSignalingTheorem2.MatchesCluster model where
  abd x y ww a b d := by
    calc
      modelABD model x y ww a b d =
          Q2.toReal (abdQ2 weightQ2 x y ww a b d) :=
        modelABD_eq weightQ2 weight_nonnegative totalsQ2 x y ww a b d
      _ = _ := congrArg Q2.toReal (abd_matches_q2 x y ww a b d)
  acd x z ww a c d := by
    calc
      modelACD model x z ww a c d =
          Q2.toReal (acdQ2 weightQ2 x z ww a c d) :=
        modelACD_eq weightQ2 weight_nonnegative totalsQ2 x z ww a c d
      _ = _ := congrArg Q2.toReal (acd_matches_q2 x z ww a c d)

def epsilonQ2 : Q2 := q (-1/8) (1/8)
def deltaQ2 : Q2 := q (-1/2) (1/2)
noncomputable def delta : ℝ := Q2.toReal deltaQ2

theorem epsilon_nonnegative : 0 ≤ Q2.toReal epsilonQ2 := by
  simp [epsilonQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem delta_nonnegative : 0 ≤ delta := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem difference_exact (c : Context) (o : Recipient) :
    difference model.behavior c o = Q2.toReal (diffQ2 weightQ2 c o) :=
  difference_eq_toReal weightQ2 weight_nonnegative totalsQ2 c o

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_active : ∀ c o,
    if c.val = 5 ∨ c.val = 7 then
      diffQ2 weightQ2 c o = epsilonQ2 ∨ diffQ2 weightQ2 c o = -epsilonQ2
    else diffQ2 weightQ2 c o = 0 := by
  with_unfolding_all decide +kernel

private theorem abs_difference_exact (c : Context) (o : Recipient) :
    |difference model.behavior c o| =
      if c.val = 5 ∨ c.val = 7 then Q2.toReal epsilonQ2 else 0 := by
  have h := diff_active c o
  by_cases hc : c.val = 5 ∨ c.val = 7
  · simp only [hc, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [difference_exact, h, abs_of_nonneg epsilon_nonnegative]
    · rw [difference_exact, h]
      have hn : Q2.toReal (-epsilonQ2) = -Q2.toReal epsilonQ2 := by
        simp [Q2.toReal]
        ring
      rw [hn, abs_neg, abs_of_nonneg epsilon_nonnegative]
  · simp only [hc, ↓reduceIte] at h ⊢
    rw [difference_exact, h]
    simp

theorem tv_exact (c : Context) :
    tv model.behavior c =
      if c.val = 5 ∨ c.val = 7 then delta else 0 := by
  unfold tv
  simp_rw [abs_difference_exact]
  by_cases hc : c.val = 5 ∨ c.val = 7
  · simp [hc, epsilonQ2, delta, deltaQ2, Q2.toReal, q, qrat]
    ring
  · simp [hc]

theorem deltaA_exact : deltaA model = delta := by
  apply le_antisymm
  · unfold deltaA
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextA, delta_nonnegative]
  · have h := tv_le_deltaA model ⟨5, by norm_num⟩
    rw [tv_exact] at h
    norm_num [contextA] at h
    exact h

theorem deltaD_exact : deltaD model = 0 := by
  apply le_antisymm
  · unfold deltaD
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextD, delta_nonnegative]
  · exact deltaD_nonnegative model

theorem delta_value : delta = (Real.sqrt 2 - 1) / 2 := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem properA_q2 :
    ∀ s : Fin 6, ∀ ww y z : Bool, ∀ o : Fin 4,
      properMarginalQ2 weightQ2 (earlyOf false ww) (lateOf y z)
          (projectAProper s) o =
        properMarginalQ2 weightQ2 (earlyOf true ww) (lateOf y z)
          (projectAProper s) o := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem properD_q2 :
    ∀ s : Fin 6, ∀ x y z : Bool, ∀ o : Fin 4,
      properMarginalQ2 weightQ2 (earlyOf x false) (lateOf y z)
          (projectDProper s) o =
        properMarginalQ2 weightQ2 (earlyOf x true) (lateOf y z)
          (projectDProper s) o := by
  with_unfolding_all decide +kernel

/-- Every single- and two-party recipient marginal is blind to A's setting. -/
theorem properA_nonsignaling (s : Fin 6) (ww y z : Bool) (o : Fin 4) :
    marginal4 model.behavior (earlyOf false ww) (lateOf y z)
        (projectAProper s) o =
      marginal4 model.behavior (earlyOf true ww) (lateOf y z)
        (projectAProper s) o := by
  rw [model, marginal4_eq_toReal, marginal4_eq_toReal, properA_q2]

/-- Every single- and two-party recipient marginal is blind to D's setting. -/
theorem properD_nonsignaling (s : Fin 6) (x y z : Bool) (o : Fin 4) :
    marginal4 model.behavior (earlyOf x false) (lateOf y z)
        (projectDProper s) o =
      marginal4 model.behavior (earlyOf x true) (lateOf y z)
        (projectDProper s) o := by
  rw [model, marginal4_eq_toReal, marginal4_eq_toReal, properD_q2]

/-- B-setting changes cannot signal even to the full complementary ACD record. -/
theorem B_silent (e : Early) (z : Fin 2) (o : Recipient) :
    marginal model.behavior e (lateChoice 0 z) recipientB o =
      marginal model.behavior e (lateChoice 1 z) recipientB o :=
  no_signaling_B model e z o

/-- C-setting changes cannot signal even to the full complementary ABD record. -/
theorem C_silent (e : Early) (y : Fin 2) (o : Recipient) :
    marginal model.behavior e (lateChoice y 0) recipientC o =
      marginal model.behavior e (lateChoice y 1) recipientC o :=
  no_signaling_C model e y o

def paritySign (o : Recipient) : ℤ :=
  if (o.val / 4 + o.val / 2 % 2 + o.val % 2) % 2 = 0 then 1 else -1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parity_q2 : ∀ c o,
    diffQ2 weightQ2 c o =
      qmul (qrat (paritySign o)) (diffQ2 weightQ2 c 0) := by
  with_unfolding_all decide +kernel

/-- For A/D sender comparisons the surviving full three-party change is a pure
binary parity shift. B/C sender changes vanish entirely by B_silent/C_silent. -/
theorem triple_difference_parity (c : Context) (o : Recipient) :
    difference model.behavior c o =
      (paritySign o : ℝ) * difference model.behavior c 0 := by
  rw [difference_exact, difference_exact, parity_q2]
  simp [ForcedSignalingLC4.toReal_qmul, ForcedSignalingLC4.toReal_qrat]

end InvisibleA

namespace InvisibleD

def weightQ2 (j : Atom) : Q2 :=
  match j.val with
  | 0 => qrat (1/8)
  | 2 => q (0) (1/16)
  | 14 => q (1/8) (-1/16)
  | 17 => q (0) (1/16)
  | 19 => qrat (1/8)
  | 29 => q (1/8) (-1/16)
  | 34 => q (1/8) (-1/16)
  | 44 => qrat (1/8)
  | 46 => q (0) (1/16)
  | 53 => q (1/8) (-1/16)
  | 57 => q (1/8) (-1/16)
  | 61 => q (-1/8) (1/8)
  | 63 => qrat (1/8)
  | 64 => q (-1/8) (1/8)
  | 65 => qrat (1/8)
  | 68 => q (1/8) (-1/16)
  | 72 => q (1/8) (-1/16)
  | 82 => qrat (1/8)
  | 83 => q (-1/8) (1/8)
  | 87 => q (1/8) (-1/16)
  | 91 => q (1/8) (-1/16)
  | 102 => q (1/8) (-1/16)
  | 106 => q (1/8) (-1/16)
  | 110 => q (-1/8) (1/8)
  | 111 => qrat (1/8)
  | 113 => q (1/8) (-1/16)
  | 124 => qrat (1/8)
  | 125 => q (0) (1/16)
  | 130 => q (1/8) (-1/16)
  | 136 => qrat (1/8)
  | 138 => q (-1/8) (1/8)
  | 142 => q (1/8) (-1/16)
  | 149 => qrat (1/8)
  | 151 => q (0) (1/16)
  | 155 => q (1/8) (-1/16)
  | 162 => q (1/8) (-1/16)
  | 164 => qrat (1/8)
  | 166 => q (-1/8) (1/8)
  | 174 => q (1/8) (-1/16)
  | 179 => q (1/8) (-1/16)
  | 185 => qrat (1/8)
  | 187 => q (-1/8) (1/8)
  | 191 => q (1/8) (-1/16)
  | 193 => q (0) (1/16)
  | 197 => q (1/8) (-1/16)
  | 202 => q (1/8) (-1/16)
  | 206 => q (0) (1/16)
  | 210 => q (0) (1/16)
  | 215 => q (1/8) (-1/16)
  | 216 => q (1/8) (-1/16)
  | 221 => q (0) (1/16)
  | 224 => q (0) (1/16)
  | 230 => q (1/8) (-1/16)
  | 233 => q (1/8) (-1/16)
  | 239 => q (0) (1/16)
  | 243 => q (0) (1/16)
  | 244 => q (1/8) (-1/16)
  | 251 => q (1/8) (-1/16)
  | 252 => q (0) (1/16)
  | _ => 0

set_option maxRecDepth 100000 in
private theorem weight_allowed (j : Atom) : AllowedWeight (weightQ2 j) := by
  fin_cases j <;> simp [AllowedWeight, weightQ2]

theorem weight_nonnegative (j : Atom) : 0 ≤ Q2.toReal (weightQ2 j) :=
  allowedWeight_nonnegative (weight_allowed j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalsQ2 : ∀ e : Early,
    (∑ j : Atom, if early j = e then weightQ2 j else 0) = qrat 1 := by
  with_unfolding_all decide +kernel

noncomputable def model : Model :=
  modelOfWeight weightQ2 weight_nonnegative totalsQ2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem abd_matches_q2 :
    ∀ x y ww a b d,
      abdQ2 weightQ2 x y ww a b d = ForcedSignalingLC4.abd x y ww a b d := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem acd_matches_q2 :
    ∀ x z ww a c d,
      acdQ2 weightQ2 x z ww a c d = ForcedSignalingLC4.acd x z ww a c d := by
  with_unfolding_all decide +kernel

theorem matchesCluster : ForcedSignalingTheorem2.MatchesCluster model where
  abd x y ww a b d := by
    calc
      modelABD model x y ww a b d =
          Q2.toReal (abdQ2 weightQ2 x y ww a b d) :=
        modelABD_eq weightQ2 weight_nonnegative totalsQ2 x y ww a b d
      _ = _ := congrArg Q2.toReal (abd_matches_q2 x y ww a b d)
  acd x z ww a c d := by
    calc
      modelACD model x z ww a c d =
          Q2.toReal (acdQ2 weightQ2 x z ww a c d) :=
        modelACD_eq weightQ2 weight_nonnegative totalsQ2 x z ww a c d
      _ = _ := congrArg Q2.toReal (acd_matches_q2 x z ww a c d)

def epsilonQ2 : Q2 := q (-1/8) (1/8)
def deltaQ2 : Q2 := q (-1/2) (1/2)
noncomputable def delta : ℝ := Q2.toReal deltaQ2

theorem epsilon_nonnegative : 0 ≤ Q2.toReal epsilonQ2 := by
  simp [epsilonQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem delta_nonnegative : 0 ≤ delta := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem difference_exact (c : Context) (o : Recipient) :
    difference model.behavior c o = Q2.toReal (diffQ2 weightQ2 c o) :=
  difference_eq_toReal weightQ2 weight_nonnegative totalsQ2 c o

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_active : ∀ c o,
    if c.val = 12 ∨ c.val = 14 then
      diffQ2 weightQ2 c o = epsilonQ2 ∨ diffQ2 weightQ2 c o = -epsilonQ2
    else diffQ2 weightQ2 c o = 0 := by
  with_unfolding_all decide +kernel

private theorem abs_difference_exact (c : Context) (o : Recipient) :
    |difference model.behavior c o| =
      if c.val = 12 ∨ c.val = 14 then Q2.toReal epsilonQ2 else 0 := by
  have h := diff_active c o
  by_cases hc : c.val = 12 ∨ c.val = 14
  · simp only [hc, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [difference_exact, h, abs_of_nonneg epsilon_nonnegative]
    · rw [difference_exact, h]
      have hn : Q2.toReal (-epsilonQ2) = -Q2.toReal epsilonQ2 := by
        simp [Q2.toReal]
        ring
      rw [hn, abs_neg, abs_of_nonneg epsilon_nonnegative]
  · simp only [hc, ↓reduceIte] at h ⊢
    rw [difference_exact, h]
    simp

theorem tv_exact (c : Context) :
    tv model.behavior c =
      if c.val = 12 ∨ c.val = 14 then delta else 0 := by
  unfold tv
  simp_rw [abs_difference_exact]
  by_cases hc : c.val = 12 ∨ c.val = 14
  · simp [hc, epsilonQ2, delta, deltaQ2, Q2.toReal, q, qrat]
    ring
  · simp [hc]

theorem deltaA_exact : deltaA model = 0 := by
  apply le_antisymm
  · unfold deltaA
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextA, delta_nonnegative]
  · exact deltaA_nonnegative model

theorem deltaD_exact : deltaD model = delta := by
  apply le_antisymm
  · unfold deltaD
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextD, delta_nonnegative]
  · have h := tv_le_deltaD model ⟨4, by norm_num⟩
    rw [tv_exact] at h
    norm_num [contextD] at h
    exact h

theorem delta_value : delta = (Real.sqrt 2 - 1) / 2 := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem properA_q2 :
    ∀ s : Fin 6, ∀ ww y z : Bool, ∀ o : Fin 4,
      properMarginalQ2 weightQ2 (earlyOf false ww) (lateOf y z)
          (projectAProper s) o =
        properMarginalQ2 weightQ2 (earlyOf true ww) (lateOf y z)
          (projectAProper s) o := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem properD_q2 :
    ∀ s : Fin 6, ∀ x y z : Bool, ∀ o : Fin 4,
      properMarginalQ2 weightQ2 (earlyOf x false) (lateOf y z)
          (projectDProper s) o =
        properMarginalQ2 weightQ2 (earlyOf x true) (lateOf y z)
          (projectDProper s) o := by
  with_unfolding_all decide +kernel

/-- Every single- and two-party recipient marginal is blind to A's setting. -/
theorem properA_nonsignaling (s : Fin 6) (ww y z : Bool) (o : Fin 4) :
    marginal4 model.behavior (earlyOf false ww) (lateOf y z)
        (projectAProper s) o =
      marginal4 model.behavior (earlyOf true ww) (lateOf y z)
        (projectAProper s) o := by
  rw [model, marginal4_eq_toReal, marginal4_eq_toReal, properA_q2]

/-- Every single- and two-party recipient marginal is blind to D's setting. -/
theorem properD_nonsignaling (s : Fin 6) (x y z : Bool) (o : Fin 4) :
    marginal4 model.behavior (earlyOf x false) (lateOf y z)
        (projectDProper s) o =
      marginal4 model.behavior (earlyOf x true) (lateOf y z)
        (projectDProper s) o := by
  rw [model, marginal4_eq_toReal, marginal4_eq_toReal, properD_q2]

/-- B-setting changes cannot signal even to the full complementary ACD record. -/
theorem B_silent (e : Early) (z : Fin 2) (o : Recipient) :
    marginal model.behavior e (lateChoice 0 z) recipientB o =
      marginal model.behavior e (lateChoice 1 z) recipientB o :=
  no_signaling_B model e z o

/-- C-setting changes cannot signal even to the full complementary ABD record. -/
theorem C_silent (e : Early) (y : Fin 2) (o : Recipient) :
    marginal model.behavior e (lateChoice y 0) recipientC o =
      marginal model.behavior e (lateChoice y 1) recipientC o :=
  no_signaling_C model e y o

def paritySign (o : Recipient) : ℤ :=
  if (o.val / 4 + o.val / 2 % 2 + o.val % 2) % 2 = 0 then 1 else -1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parity_q2 : ∀ c o,
    diffQ2 weightQ2 c o =
      qmul (qrat (paritySign o)) (diffQ2 weightQ2 c 0) := by
  with_unfolding_all decide +kernel

/-- For A/D sender comparisons the surviving full three-party change is a pure
binary parity shift. B/C sender changes vanish entirely by B_silent/C_silent. -/
theorem triple_difference_parity (c : Context) (o : Recipient) :
    difference model.behavior c o =
      (paritySign o : ℝ) * difference model.behavior c 0 := by
  rw [difference_exact, difference_exact, parity_q2]
  simp [ForcedSignalingLC4.toReal_qmul, ForcedSignalingLC4.toReal_qrat]

end InvisibleD

namespace InvisibleBalanced

def weightQ2 (j : Atom) : Q2 :=
  match j.val with
  | 0 => q (-1/8) (1/8)
  | 2 => qrat (1/8)
  | 4 => q (1/8) (-1/16)
  | 8 => q (1/8) (-1/16)
  | 17 => qrat (1/8)
  | 19 => q (0) (1/16)
  | 31 => q (1/8) (-1/16)
  | 36 => q (1/8) (-1/16)
  | 40 => q (1/8) (-1/16)
  | 44 => q (-1/8) (1/8)
  | 46 => qrat (1/8)
  | 51 => q (1/8) (-1/16)
  | 61 => qrat (1/8)
  | 63 => q (0) (1/16)
  | 64 => qrat (1/8)
  | 65 => q (-1/8) (1/8)
  | 69 => q (1/8) (-1/16)
  | 73 => q (1/8) (-1/16)
  | 82 => q (-1/8) (1/8)
  | 83 => qrat (1/8)
  | 86 => q (1/8) (-1/16)
  | 90 => q (1/8) (-1/16)
  | 102 => q (1/8) (-1/16)
  | 106 => q (1/8) (-1/16)
  | 110 => q (-1/8) (1/8)
  | 111 => qrat (1/8)
  | 117 => q (1/8) (-1/16)
  | 121 => q (1/8) (-1/16)
  | 124 => qrat (1/8)
  | 125 => q (-1/8) (1/8)
  | 130 => q (1/8) (-1/16)
  | 136 => qrat (1/8)
  | 138 => q (-1/8) (1/8)
  | 142 => q (1/8) (-1/16)
  | 147 => q (1/8) (-1/16)
  | 149 => qrat (1/8)
  | 151 => q (-1/8) (1/8)
  | 159 => q (1/8) (-1/16)
  | 162 => q (1/8) (-1/16)
  | 164 => qrat (1/8)
  | 166 => q (-1/8) (1/8)
  | 174 => q (1/8) (-1/16)
  | 179 => q (1/8) (-1/16)
  | 185 => qrat (1/8)
  | 187 => q (-1/8) (1/8)
  | 191 => q (1/8) (-1/16)
  | 192 => q (1/8) (-1/16)
  | 193 => q (-1/16) (1/16)
  | 197 => qrat (1/16)
  | 202 => qrat (1/16)
  | 206 => q (-1/16) (1/16)
  | 207 => q (1/8) (-1/16)
  | 210 => q (-1/16) (1/16)
  | 211 => q (1/8) (-1/16)
  | 215 => qrat (1/16)
  | 216 => qrat (1/16)
  | 220 => q (1/8) (-1/16)
  | 221 => q (-1/16) (1/16)
  | 224 => qrat (1/16)
  | 230 => qrat (1/16)
  | 233 => qrat (1/16)
  | 239 => qrat (1/16)
  | 243 => qrat (1/16)
  | 244 => qrat (1/16)
  | 251 => qrat (1/16)
  | 252 => qrat (1/16)
  | _ => 0

set_option maxRecDepth 100000 in
private theorem weight_allowed (j : Atom) : AllowedWeight (weightQ2 j) := by
  fin_cases j <;> simp [AllowedWeight, weightQ2]

theorem weight_nonnegative (j : Atom) : 0 ≤ Q2.toReal (weightQ2 j) :=
  allowedWeight_nonnegative (weight_allowed j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem totalsQ2 : ∀ e : Early,
    (∑ j : Atom, if early j = e then weightQ2 j else 0) = qrat 1 := by
  with_unfolding_all decide +kernel

noncomputable def model : Model :=
  modelOfWeight weightQ2 weight_nonnegative totalsQ2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem abd_matches_q2 :
    ∀ x y ww a b d,
      abdQ2 weightQ2 x y ww a b d = ForcedSignalingLC4.abd x y ww a b d := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem acd_matches_q2 :
    ∀ x z ww a c d,
      acdQ2 weightQ2 x z ww a c d = ForcedSignalingLC4.acd x z ww a c d := by
  with_unfolding_all decide +kernel

theorem matchesCluster : ForcedSignalingTheorem2.MatchesCluster model where
  abd x y ww a b d := by
    calc
      modelABD model x y ww a b d =
          Q2.toReal (abdQ2 weightQ2 x y ww a b d) :=
        modelABD_eq weightQ2 weight_nonnegative totalsQ2 x y ww a b d
      _ = _ := congrArg Q2.toReal (abd_matches_q2 x y ww a b d)
  acd x z ww a c d := by
    calc
      modelACD model x z ww a c d =
          Q2.toReal (acdQ2 weightQ2 x z ww a c d) :=
        modelACD_eq weightQ2 weight_nonnegative totalsQ2 x z ww a c d
      _ = _ := congrArg Q2.toReal (acd_matches_q2 x z ww a c d)

def epsilonQ2 : Q2 := q (-1/16) (1/16)
def deltaQ2 : Q2 := q (-1/4) (1/4)
noncomputable def delta : ℝ := Q2.toReal deltaQ2

theorem epsilon_nonnegative : 0 ≤ Q2.toReal epsilonQ2 := by
  simp [epsilonQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem delta_nonnegative : 0 ≤ delta := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  nlinarith [ForcedSignalingCertificateModel.sqrtTwo_ge_one]

theorem difference_exact (c : Context) (o : Recipient) :
    difference model.behavior c o = Q2.toReal (diffQ2 weightQ2 c o) :=
  difference_eq_toReal weightQ2 weight_nonnegative totalsQ2 c o

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem diff_active : ∀ c o,
    if c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14 then
      diffQ2 weightQ2 c o = epsilonQ2 ∨ diffQ2 weightQ2 c o = -epsilonQ2
    else diffQ2 weightQ2 c o = 0 := by
  with_unfolding_all decide +kernel

private theorem abs_difference_exact (c : Context) (o : Recipient) :
    |difference model.behavior c o| =
      if c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14 then Q2.toReal epsilonQ2 else 0 := by
  have h := diff_active c o
  by_cases hc : c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14
  · simp only [hc, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [difference_exact, h, abs_of_nonneg epsilon_nonnegative]
    · rw [difference_exact, h]
      have hn : Q2.toReal (-epsilonQ2) = -Q2.toReal epsilonQ2 := by
        simp [Q2.toReal]
        ring
      rw [hn, abs_neg, abs_of_nonneg epsilon_nonnegative]
  · simp only [hc, ↓reduceIte] at h ⊢
    rw [difference_exact, h]
    simp

theorem tv_exact (c : Context) :
    tv model.behavior c =
      if c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14 then delta else 0 := by
  unfold tv
  simp_rw [abs_difference_exact]
  by_cases hc : c.val = 5 ∨ c.val = 7 ∨ c.val = 12 ∨ c.val = 14
  · simp [hc, epsilonQ2, delta, deltaQ2, Q2.toReal, q, qrat]
    ring
  · simp [hc]

theorem deltaA_exact : deltaA model = delta := by
  apply le_antisymm
  · unfold deltaA
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextA, delta_nonnegative]
  · have h := tv_le_deltaA model ⟨5, by norm_num⟩
    rw [tv_exact] at h
    norm_num [contextA] at h
    exact h

theorem deltaD_exact : deltaD model = delta := by
  apply le_antisymm
  · unfold deltaD
    apply Finset.sup'_le
    intro i _
    rw [tv_exact]
    fin_cases i <;> simp [contextD, delta_nonnegative]
  · have h := tv_le_deltaD model ⟨4, by norm_num⟩
    rw [tv_exact] at h
    norm_num [contextD] at h
    exact h

theorem delta_value : delta = (Real.sqrt 2 - 1) / 4 := by
  simp [delta, deltaQ2, Q2.toReal, q, qrat]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem properA_q2 :
    ∀ s : Fin 6, ∀ ww y z : Bool, ∀ o : Fin 4,
      properMarginalQ2 weightQ2 (earlyOf false ww) (lateOf y z)
          (projectAProper s) o =
        properMarginalQ2 weightQ2 (earlyOf true ww) (lateOf y z)
          (projectAProper s) o := by
  with_unfolding_all decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem properD_q2 :
    ∀ s : Fin 6, ∀ x y z : Bool, ∀ o : Fin 4,
      properMarginalQ2 weightQ2 (earlyOf x false) (lateOf y z)
          (projectDProper s) o =
        properMarginalQ2 weightQ2 (earlyOf x true) (lateOf y z)
          (projectDProper s) o := by
  with_unfolding_all decide +kernel

/-- Every single- and two-party recipient marginal is blind to A's setting. -/
theorem properA_nonsignaling (s : Fin 6) (ww y z : Bool) (o : Fin 4) :
    marginal4 model.behavior (earlyOf false ww) (lateOf y z)
        (projectAProper s) o =
      marginal4 model.behavior (earlyOf true ww) (lateOf y z)
        (projectAProper s) o := by
  rw [model, marginal4_eq_toReal, marginal4_eq_toReal, properA_q2]

/-- Every single- and two-party recipient marginal is blind to D's setting. -/
theorem properD_nonsignaling (s : Fin 6) (x y z : Bool) (o : Fin 4) :
    marginal4 model.behavior (earlyOf x false) (lateOf y z)
        (projectDProper s) o =
      marginal4 model.behavior (earlyOf x true) (lateOf y z)
        (projectDProper s) o := by
  rw [model, marginal4_eq_toReal, marginal4_eq_toReal, properD_q2]

/-- B-setting changes cannot signal even to the full complementary ACD record. -/
theorem B_silent (e : Early) (z : Fin 2) (o : Recipient) :
    marginal model.behavior e (lateChoice 0 z) recipientB o =
      marginal model.behavior e (lateChoice 1 z) recipientB o :=
  no_signaling_B model e z o

/-- C-setting changes cannot signal even to the full complementary ABD record. -/
theorem C_silent (e : Early) (y : Fin 2) (o : Recipient) :
    marginal model.behavior e (lateChoice y 0) recipientC o =
      marginal model.behavior e (lateChoice y 1) recipientC o :=
  no_signaling_C model e y o

def paritySign (o : Recipient) : ℤ :=
  if (o.val / 4 + o.val / 2 % 2 + o.val % 2) % 2 = 0 then 1 else -1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parity_q2 : ∀ c o,
    diffQ2 weightQ2 c o =
      qmul (qrat (paritySign o)) (diffQ2 weightQ2 c 0) := by
  with_unfolding_all decide +kernel

/-- For A/D sender comparisons the surviving full three-party change is a pure
binary parity shift. B/C sender changes vanish entirely by B_silent/C_silent. -/
theorem triple_difference_parity (c : Context) (o : Recipient) :
    difference model.behavior c o =
      (paritySign o : ℝ) * difference model.behavior c 0 := by
  rw [difference_exact, difference_exact, parity_q2]
  simp [ForcedSignalingLC4.toReal_qmul, ForcedSignalingLC4.toReal_qrat]

end InvisibleBalanced

end
end OntologySeparation.ForcedSignalingPropositionWitnesses
