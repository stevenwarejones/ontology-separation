import Mathlib

/-!
# Baumann--Brukner main-text signaling protocol bridge

This file formalizes the exact probability arithmetic behind the concrete
protocol in Sec. 3 of Baumann & Brukner, Quantum 8, 1481 (2024).

For the maximally entangled source, the friend premeasurement leaves two
relevant SF branches |00⟩ and |11⟩.  An unread Wigner measurement in the
π/8 basis induces the following exact friend-output weights on an
unnormalized real branch state x|00⟩ + y|11⟩:

  p(f=0) = 3/4 x² + 1/4 y² - 1/2 xy
  p(f=1) = 1/4 x² + 3/4 y² + 1/2 xy.

The Bob measurement choice changes the branch weights (x²,y²,xy).  We use
those Born-weight triples to derive the paper's before/after joint tables and
then derive the effective memory-flip probabilities.

This avoids importing Appendix-B Eq. B.29 for the concrete signaling example.
It is still a compact two-branch quantum calculation rather than a full
QIT channel implementation of every measurement register.
-/

namespace OntologySeparation.BaumannBruknerProtocol
noncomputable section

def sqrtTwo : ℝ := Real.sqrt 2

theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  simp [sqrtTwo]

theorem sqrtTwo_pos : 0 < sqrtTwo := by
  exact Real.sqrt_pos.2 (by norm_num)

theorem sqrtTwo_gt_one : 1 < sqrtTwo := by
  have h0 : 0 ≤ sqrtTwo := by
    exact Real.sqrt_nonneg (2 : ℝ)
  have h2 := sqrtTwo_sq
  nlinarith

theorem sqrtTwo_lt_three_halves : sqrtTwo < (3 : ℝ) / 2 := by
  have h0 := Real.sqrt_nonneg (2 : ℝ)
  have h2 := sqrtTwo_sq
  nlinarith

/-- Squared branch amplitudes and their real cross term after conditioning on
Bob's recorded outcome. -/
structure BranchData where
  x2 : ℝ
  y2 : ℝ
  xy : ℝ

/-- Friend probabilities after the unread π/8 Wigner measurement. -/
def wignerFriend0 (d : BranchData) : ℝ :=
  (3/4 : ℝ) * d.x2 + (1/4 : ℝ) * d.y2 - (1/2 : ℝ) * d.xy

def wignerFriend1 (d : BranchData) : ℝ :=
  (1/4 : ℝ) * d.x2 + (3/4 : ℝ) * d.y2 + (1/2 : ℝ) * d.xy

def wignerFriend (d : BranchData) (f : Bool) : ℝ :=
  if f then wignerFriend1 d else wignerFriend0 d

/-- Bob measures in the computational basis.  B=0 selects |11⟩SF and
B=1 selects |00⟩SF, each with total probability 1/2. -/
def computationalBranch (b : Bool) : BranchData :=
  if b then
    ⟨1/2, 0, 0⟩
  else
    ⟨0, 1/2, 0⟩

/-- Bob measures in the basis used in Sec. 3:
|B0⟩ = 1/√3 |0⟩ + √(2/3)|1⟩,
|B1⟩ = √(2/3)|0⟩ - 1/√3 |1⟩.

The entries below are the exact squared conditional branch amplitudes and
cross term, including the common source factor 1/√2. -/
def rotatedBranch (b : Bool) : BranchData :=
  if b then
    ⟨1/6, 1/3, -sqrtTwo/6⟩
  else
    ⟨1/3, 1/6, sqrtTwo/6⟩

def computationalBefore (f b : Bool) : ℝ :=
  match f, b with
  | false, false => 0
  | false, true  => 1/2
  | true,  false => 1/2
  | true,  true  => 0

def computationalAfter (f b : Bool) : ℝ :=
  match f, b with
  | false, false => 1/8
  | false, true  => 3/8
  | true,  false => 3/8
  | true,  true  => 1/8

def rotatedBefore (f b : Bool) : ℝ :=
  match f, b with
  | false, false => 1/3
  | false, true  => 1/6
  | true,  false => 1/6
  | true,  true  => 1/3

def rotatedAfter (f b : Bool) : ℝ :=
  match f, b with
  | false, false => (7 - 2*sqrtTwo)/24
  | false, true  => (5 + 2*sqrtTwo)/24
  | true,  false => (5 + 2*sqrtTwo)/24
  | true,  true  => (7 - 2*sqrtTwo)/24

/-- The computational-setting post-Wigner table follows from the π/8
two-branch dephasing formula. -/
theorem computational_after_from_wigner (f b : Bool) :
    wignerFriend (computationalBranch b) f = computationalAfter f b := by
  cases f <;> cases b <;>
    norm_num [wignerFriend, wignerFriend0, wignerFriend1,
      computationalBranch, computationalAfter]

/-- The rotated-setting post-Wigner table in Sec. 3 follows from the same
Wigner map and Bob-dependent branch cross terms. -/
theorem rotated_after_from_wigner (f b : Bool) :
    wignerFriend (rotatedBranch b) f = rotatedAfter f b := by
  cases f <;> cases b <;>
    simp [wignerFriend, wignerFriend0, wignerFriend1,
      rotatedBranch, rotatedAfter] <;> ring

/-- Apply a Bob-independent flip probability q to the friend's earlier record. -/
def flipPredict (before : Bool → Bool → ℝ) (q : ℝ) (f b : Bool) : ℝ :=
  (1-q) * before f b + q * before (!f) b

def qComputational : ℝ := 1/4
def qRotated : ℝ := 1/4 + sqrtTwo/2

/-- The computational-basis table is reproduced by q=1/4. -/
theorem computational_flip_bridge (f b : Bool) :
    flipPredict computationalBefore qComputational f b =
      computationalAfter f b := by
  cases f <;> cases b <;>
    norm_num [flipPredict, computationalBefore, computationalAfter,
      qComputational]

/-- The rotated-basis table is reproduced by q=1/4+1/√2 =
1/4+√2/2, exactly as in the paper's Sec. 3 example. -/
theorem rotated_flip_bridge (f b : Bool) :
    flipPredict rotatedBefore qRotated f b = rotatedAfter f b := by
  cases f <;> cases b <;>
    simp [flipPredict, rotatedBefore, rotatedAfter, qRotated] <;> ring

theorem qComputational_lt_half : qComputational < 1/2 := by
  norm_num [qComputational]

theorem half_lt_qRotated : 1/2 < qRotated := by
  unfold qRotated
  have h := sqrtTwo_gt_one
  linarith

theorem qRotated_lt_one : qRotated < 1 := by
  unfold qRotated
  have h := sqrtTwo_lt_three_halves
  linarith

theorem qRotated_valid : 0 ≤ qRotated ∧ qRotated ≤ 1 := by
  constructor
  · have h := sqrtTwo_pos
    unfold qRotated
    linarith
  · exact le_of_lt qRotated_lt_one

/-- Bob's two measurement choices force opposite sides of the 1/2 flip-rate
threshold in the concrete protocol. -/
theorem exact_setting_dependence :
    qComputational < 1/2 ∧ 1/2 < qRotated ∧ qRotated ≤ 1 := by
  exact ⟨qComputational_lt_half, half_lt_qRotated, le_of_lt qRotated_lt_one⟩

theorem flip_rates_differ : qComputational ≠ qRotated := by
  intro h
  have hc := qComputational_lt_half
  have hr := half_lt_qRotated
  rw [h] at hc
  linarith

end
end OntologySeparation.BaumannBruknerProtocol
