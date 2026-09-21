import OntologySeparation.Core.Extensions

/-! Finite classical channels. Quantum state evolution uses `Procedure` instead. -/
namespace OntologySeparation
noncomputable section
abbrev Channel (A B : Type) [Fintype B] := A → FiniteDistribution B
namespace Channel
variable {A B C D : Type} [Fintype B] [Fintype C] [Fintype D]
def deterministic (f : A → B) : Channel A B := by
  classical
  exact fun a => {
    mass := fun b => if b = f a then 1 else 0
    nonneg := by intro b; split_ifs <;> norm_num
    total := by simp }
def andThen (first : Channel A B) (second : Channel B C) : Channel A C := fun a => {
  mass := fun c => ∑ b, (first a).mass b * (second b).mass c
  nonneg := fun c => Finset.sum_nonneg fun b _ =>
    mul_nonneg ((first a).nonneg b) ((second b).nonneg c)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteDistribution.total, mul_one]
    exact (first a).total }
/-- Independent parallel composition is an explicit physical assumption. -/
def parallel (left : Channel A B) (right : Channel C D) : Channel (A × C) (B × D) :=
  fun a => {
    mass := fun b => (left a.1).mass b.1 * (right a.2).mass b.2
    nonneg := fun b => mul_nonneg ((left a.1).nonneg b.1) ((right a.2).nonneg b.2)
    total := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, FiniteDistribution.total, mul_one]
      exact (left a.1).total }
/-- Classical outcome-dependent control; not coherent quantum control. -/
def feedForward (first : Channel A B) (next : A → Channel B C) : Channel A C :=
  fun a => andThen first (next a) a

theorem andThen_assoc (f : Channel A B) (g : Channel B C) (h : Channel C D)
    (a : A) (d : D) :
    (andThen (andThen f g) h a).mass d = (andThen f (andThen g h) a).mass d := by
  simp only [andThen]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring
@[simp] theorem deterministic_andThen (f : A → B) (g : Channel B C) (a : A) (c : C) :
    (andThen (deterministic f) g a).mass c = (g (f a)).mass c := by
  classical
  simp [andThen, deterministic]
end Channel

def Channel.behavior {S Ω O : Type} [Fintype Ω] [Fintype O]
    (prepare : Channel S Ω) (readout : Channel Ω O) :
    Behavior { Setting := S, Outcome := O } where
  prob s := (Channel.andThen prepare readout s).mass
  nonneg s := (Channel.andThen prepare readout s).nonneg
  normalized s := (Channel.andThen prepare readout s).total
end
end OntologySeparation
