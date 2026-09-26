import OntologySeparation.Operational.HiddenInfluenceStochastic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite disintegration and a setting-independent reservoir of response tables.
All probabilities are real; finiteness concerns the sample space, not weights. -/
namespace OntologySeparation.HiddenInfluence.FiniteKernel
noncomputable section
open scoped BigOperators

variable {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]

/-- Pushforward, retaining no internal information beyond the selected record. -/
def map [DecidableEq β] (d : FiniteDistribution α) (f : α → β) :
    FiniteDistribution β := bind d (fun a => pure (f a))

theorem map_mass [DecidableEq β] (d : FiniteDistribution α) (f : α → β) (b : β) :
    (map d f).mass b = ∑ a, if f a = b then d.mass a else 0 := by
  simp [map, bind, pure, mul_ite, eq_comm]

/-- A finite common seed contains an independent table for each possible record.
Its law is sampled before the actual setting or record is known. -/
def reservoir [DecidableEq ι] (d : ι → FiniteDistribution α) : FiniteDistribution (ι → α) where
  mass table := ∏ i, (d i).mass (table i)
  nonneg table := Finset.prod_nonneg fun i _ => (d i).nonneg (table i)
  total := by
    rw [← Fintype.prod_sum]
    simp_rw [(d _).total]
    simp

/-- Reading one slot of the common reservoir has exactly its specified law. -/
theorem reservoir_mean [DecidableEq ι] (d : ι → FiniteDistribution α)
    (i : ι) (f : α → ℝ) :
    (∑ table : ι → α, (reservoir d).mass table * f (table i)) =
      ∑ a, (d i).mass a * f a := by
  have h := Fintype.prod_sum (fun j a =>
    (d j).mass a * (if j = i then f a else 1))
  have hr : (∏ j, ∑ a, (d j).mass a * (if j = i then f a else 1)) =
      ∑ a, (d i).mass a * f a := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji, (d j).total]
    · simp
  rw [hr] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro table _
  simp only [reservoir, Finset.prod_mul_distrib]
  simp

def condition [DecidableEq α] [DecidableEq β] [Inhabited α]
    (d : FiniteDistribution α) (f : α → β) (b : β) : FiniteDistribution α :=
  if h : (map d f).mass b = 0 then pure default else
  { mass := fun a => if f a = b then d.mass a / (map d f).mass b else 0
    nonneg := fun a => by
      split
      · exact div_nonneg (d.nonneg a) ((map d f).nonneg b)
      · exact le_rfl
    total := by
      calc
        _ = (∑ a, if f a = b then d.mass a else 0) / (map d f).mass b := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _
          split <;> simp_all
        _ = 1 := by rw [← map_mass, div_self h] }

/-- Null fibers have zero mass, so arbitrary normalized conditionals there
 disappear when multiplied by the probability of the early event. -/
theorem condition_weight [DecidableEq α] [DecidableEq β] [Inhabited α]
    (d : FiniteDistribution α) (f : α → β) (b : β) (a : α) :
    (map d f).mass b * (condition d f b).mass a =
      if f a = b then d.mass a else 0 := by
  by_cases h : (map d f).mass b = 0
  · rw [h, zero_mul]
    by_cases ha : f a = b
    · rw [if_pos ha]
      have hle : d.mass a ≤ (map d f).mass b := by
        rw [map_mass]
        calc
          d.mass a = (if f a = b then d.mass a else 0) := by simp [ha]
          _ ≤ ∑ z, if f z = b then d.mass z else 0 :=
            Finset.single_le_sum (f := fun z => if f z = b then d.mass z else 0)
              (fun z _ => by dsimp only; split <;> simp [d.nonneg]) (Finset.mem_univ a)
      have hz := d.nonneg a
      linarith
    · simp [ha]
  · simp only [condition, dif_neg h]
    by_cases ha : f a = b
    · simp only [if_pos ha]
      field_simp
    · simp [ha]

theorem disintegrate [DecidableEq α] [DecidableEq β] [Inhabited α]
    (d : FiniteDistribution α) (f : α → β) (a : α) :
    (bind (map d f) (condition d f)).mass a = d.mass a := by
  simp_rw [bind_mass, condition_weight]
  simp


/-- Joint sampling of a seed and a finite conditional table, all before settings. -/
def joint (d : FiniteDistribution α) (k : α → FiniteDistribution β) :
    FiniteDistribution (α × β) where
  mass ab := d.mass ab.1 * (k ab.1).mass ab.2
  nonneg ab := mul_nonneg (d.nonneg ab.1) ((k ab.1).nonneg ab.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (k _).total, mul_one]
    exact d.total

theorem map_single_le [DecidableEq β] (d : FiniteDistribution α)
    (f : α → β) (a : α) : d.mass a ≤ (map d f).mass (f a) := by
  rw [map_mass]
  calc
    d.mass a = (if f a = f a then d.mass a else 0) := by simp
    _ ≤ ∑ z, if f z = f a then d.mass z else 0 :=
      Finset.single_le_sum (f := fun z => if f z = f a then d.mass z else 0)
        (fun z _ => by dsimp only; split <;> simp [d.nonneg]) (Finset.mem_univ a)

theorem condition_support [DecidableEq α] [DecidableEq β] [Inhabited α]
    (d : FiniteDistribution α) (f : α → β) (b : β) (a : α)
    (hb : (map d f).mass b ≠ 0) (ha : (condition d f b).mass a ≠ 0) : f a = b := by
  by_contra h
  simp [condition, hb, h] at ha

/-- Expectation under pushforward; used to group hidden seeds by early record. -/
theorem map_mean [DecidableEq β] (d : FiniteDistribution α)
    (f : α → β) (g : β → ℝ) :
    (∑ b, (map d f).mass b * g b) = ∑ a, d.mass a * g (f a) := by
  simp_rw [map_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

/-- Finite law of total expectation for a stochastic transition. -/
theorem bind_mean (d : FiniteDistribution α) (k : α → FiniteDistribution β)
    (f : β → ℝ) :
    (∑ b, (bind d k).mass b * f b) = ∑ a, d.mass a * ∑ b, (k a).mass b * f b := by
  simp_rw [bind_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Complete a retained record using a desired full target distribution. -/
def complete [DecidableEq α] [DecidableEq β] [Inhabited α]
    (current target : FiniteDistribution α) (record : α → β) : FiniteDistribution α :=
  bind current (fun a => condition target record (record a))

/-- Matching retained marginals suffice to extend to ANY normalized full target.
This resamples only the unretained information on positive-probability events. -/
theorem complete_eq_target [DecidableEq α] [DecidableEq β] [Inhabited α]
    (current target : FiniteDistribution α) (record : α → β)
    (h : ∀ b, (map current record).mass b = (map target record).mass b) (a : α) :
    (complete current target record).mass a = target.mass a := by
  unfold complete
  rw [bind_mass, ← map_mean current record
    (fun r => (condition target record r).mass a)]
  simp_rw [h, condition_weight]
  simp

theorem complete_preserves_record [DecidableEq α] [DecidableEq β] [Inhabited α]
    (current target : FiniteDistribution α) (record : α → β)
    (h : ∀ b, (map current record).mass b = (map target record).mass b)
    (a b : α) (ha : current.mass a ≠ 0)
    (hb : (condition target record (record a)).mass b ≠ 0) : record b = record a := by
  apply condition_support target record (record a) b _ hb
  rw [← h]
  have hh := map_single_le current record a
  exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (current.nonneg a) (Ne.symm ha)) hh)

end
end OntologySeparation.HiddenInfluence.FiniteKernel
