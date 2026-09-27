import OntologySeparation.Experiments.ContinuumStatistics
import Mathlib.Analysis.Fourier.ZMod

/-! Periodic nearest-neighbor dynamics on Z/NZ. The two directed shifts are
retained for N=1,2 as well. Time remains continuous. -/
namespace OntologySeparation.ContinuumFinite
noncomputable section
open AddChar
variable {N : ℕ} [NeZero N]

def fourierCharacter (j n : ZMod N) : ℂ := ZMod.stdAddChar (j*n)

def cyclicDifference (f : ZMod N → ℂ) (n : ZMod N) : ℂ :=
  2*f n-f (n+1)-f (n-1)

/-- Derive the cyclic finite-difference eigenvalue directly from the shifts. -/
theorem cyclic_character_eigenvalue (j n : ZMod N) :
    cyclicDifference (fourierCharacter j) n =
      (2-ZMod.stdAddChar j-ZMod.stdAddChar (-j))*fourierCharacter j n := by
  unfold cyclicDifference fourierCharacter
  rw [show j*(n+1) = j*n+j by ring, show j*(n-1) = j*n+(-j) by ring]
  rw [map_add_eq_mul,map_add_eq_mul]
  ring

/-- Character normalization before the N^(-1/2) Fourier scaling. -/
theorem character_norm (j n : ZMod N) : ‖fourierCharacter j n‖ = 1 := by
  simp [fourierCharacter,ZMod.stdAddChar_apply]

def normalizedFourierMode (j n : ZMod N) : ℂ :=
  (Real.sqrt (N : ℝ) : ℂ)⁻¹*fourierCharacter j n

theorem normalizedFourierMode_mass (j : ZMod N) :
    (∑ n : ZMod N, ‖normalizedFourierMode j n‖^2) = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp only [normalizedFourierMode,norm_mul,norm_inv,character_norm,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  rw [inv_pow,Real.sq_sqrt (by positivity),mul_inv_cancel₀ hn]

/-- Integer labels evaluated in the same Fourier convention as the continuum. -/
theorem character_integer_phase (j : ℤ) :
    ZMod.stdAddChar (j : ZMod N) = phase (2*Real.pi*j/N) := by
  rw [ZMod.stdAddChar_coe]
  unfold phase
  congr 1
  push_cast
  ring

theorem phase_pair (x : ℝ) : phase x+phase (-x) = ((2*Real.cos x : ℝ) : ℂ) := by
  simp only [phase,Complex.exp_mul_I,Complex.ofReal_neg,Complex.cos_neg,Complex.sin_neg,
    Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_cos]
  ring

/-- The dimensionless eigenvalue is 2(1-cos(2πj/N)), including periodic boundaries. -/
theorem cyclic_cosine_eigenvalue (j : ℤ) (n : ZMod N) :
    cyclicDifference (fourierCharacter (j : ZMod N)) n =
      ((2*(1-Real.cos (2*Real.pi*j/N)) : ℝ) : ℂ) * fourierCharacter (j : ZMod N) n := by
  rw [cyclic_character_eigenvalue,character_integer_phase]
  rw [show -(j : ZMod N) = ((-j : ℤ) : ZMod N) by simp,character_integer_phase]
  have hn : (2*Real.pi*(-j)/N : ℝ) = -(2*Real.pi*j/N) := by push_cast; ring
  rw [Int.cast_neg,hn]
  have hp := phase_pair (2*Real.pi*j/N)
  push_cast at hp ⊢
  linear_combination -fourierCharacter (j : ZMod N) n * hp

/-- Strict low-band alias exclusion. The endpoint N=2J is deliberately absent. -/
theorem no_alias (J : ℕ) (hN : 2*J < N) (a b : ℤ)
    (ha : a.natAbs ≤ J) (hb : b.natAbs ≤ J) (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b N).mp h
  have hab : (b-a).natAbs < (N : ℤ).natAbs := by
    have hle := Int.natAbs_sub_le b a
    simp only [Int.natAbs_natCast]
    omega
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hab
  omega

theorem character_star (z : ZMod N) : star (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  change star (↑(ZMod.toCircle z) : ℂ) = ↑(ZMod.toCircle (-z))
  rw [map_neg_eq_inv, _root_.Circle.coe_inv_eq_conj]
  rfl

/-- Full Fourier orthogonality, not merely normalization of each column. -/
theorem character_orthogonality (j k : ZMod N) :
    (∑ n : ZMod N, star (fourierCharacter j n)*fourierCharacter k n) =
      if j = k then (N : ℂ) else 0 := by
  have eq : ∀ n : ZMod N, star (fourierCharacter j n)*fourierCharacter k n =
      ZMod.stdAddChar ((k-j)*n) := by
    intro n
    unfold fourierCharacter
    rw [character_star,← map_add_eq_mul]
    congr 1
    ring
  simp_rw [eq]
  by_cases h : j = k
  · subst k
    simp [ZMod.card]
  · rw [if_neg h]
    exact AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar N (sub_ne_zero.mpr (Ne.symm h)))

end
end OntologySeparation.ContinuumFinite
