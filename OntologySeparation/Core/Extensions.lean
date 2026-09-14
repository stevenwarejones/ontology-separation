import OntologySeparation.Core.Operational
import Mathlib.Tactic.NormNum

/-! Shared interfaces for experiment restrictions and independent extensions.
These constructions expose missing laws; they do not supply unmentioned physics. -/
namespace OntologySeparation
noncomputable section

/-- Restrict settings, preserving every public outcome probability. -/
def Behavior.restrict {E : Interface} (p : Behavior E) (S : Type)
    (settings : S → E.Setting) : Behavior { Setting := S, Outcome := E.Outcome } where
  prob s o := p.prob (settings s) o
  nonneg s o := p.nonneg (settings s) o
  normalized s := p.normalized (settings s)

abbrev binaryInterface : Interface := { Setting := Unit, Outcome := Bool }

def coin (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : Behavior binaryInterface where
  prob _ b := if b then r else 1-r
  nonneg _ b := by cases b <;> simp <;> linarith
  normalized _ := by simp

/-- A theory of one sector puts no restriction on an independently added sector. -/
structure Extension {E F : Interface} (T : Theory E) where
  base : Behavior E
  admissible : T base
  added : Behavior F

/-- Every binary probability can occur in an independent extension of an inhabited
base theory. The explicit independence assumption is essential to this statement. -/
theorem free_binary_extension {E : Interface} {T : Theory E} (w : Witness T)
    (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ∃ e : Extension (F := binaryInterface) T,
      e.base = w.behavior ∧ e.added.prob () true = r := by
  exact ⟨⟨w.behavior, w.admissible, coin r h0 h1⟩, rfl, rfl⟩

/-- The original sector is identical in two completions with opposite predictions. -/
theorem independent_sector_underdetermined {E : Interface} {T : Theory E}
    (w : Witness T) :
    ∃ a b : Extension (F := binaryInterface) T,
      a.base = b.base ∧ a.added.prob () true = 0 ∧ b.added.prob () true = 1 := by
  exact ⟨⟨w.behavior, w.admissible, coin 0 (by norm_num) (by norm_num)⟩,
    ⟨w.behavior, w.admissible, coin 1 (by norm_num) (by norm_num)⟩, rfl, rfl, rfl⟩

/-- Finite distribution wrapper: no measure theory in the public interface. -/
structure FiniteDistribution (Ω : Type) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

def FiniteDistribution.mean {Ω : Type} [Fintype Ω] (d : FiniteDistribution Ω)
    (f : Ω → ℝ) : ℝ := ∑ x, d.mass x * f x

theorem FiniteDistribution.mean_le {Ω : Type} [Fintype Ω]
    (d : FiniteDistribution Ω) (f : Ω → ℝ) (b : ℝ) (h : ∀ x, f x ≤ b) :
    d.mean f ≤ b := by
  calc
    d.mean f ≤ ∑ x, d.mass x * b := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (h x) (d.nonneg x)
    _ = b := by rw [← Finset.sum_mul, d.total, one_mul]

end
end OntologySeparation
