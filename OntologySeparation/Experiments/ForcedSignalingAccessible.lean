import OntologySeparation.Experiments.ForcedSignalingTiming
import OntologySeparation.Experiments.ForcedSignalingPinned

/-! All collectible recipient records are independent of the early sender's
setting when that sender is spatially between the later blind stations. -/
namespace OntologySeparation.ForcedSignalingAccessible
noncomputable section
open scoped BigOperators
open HiddenInfluence VCausal ForcedSignalingTiming ForcedSignalingPinned ForcedSignalingLC4Witness

def partyBit (o : VisibleOutcome) : Party → Bool
  | .A => o.a | .B => o.b | .C => o.c | .D => o.d

def setRecord (R : Finset Party) (o : VisibleOutcome) (p : Party) : Bool :=
  if p ∈ R then partyBit o p else false

private theorem record_project {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (d d' : FiniteDistribution VisibleOutcome)
    (f : VisibleOutcome → α) (h : ∀ a, recordProb d f a = recordProb d' f a)
    (g : α → β) (b : β) :
    recordProb d (g ∘ f) b = recordProb d' (g ∘ f) b := by
  have hm : ∀ a, (FiniteKernel.map d f).mass a = (FiniteKernel.map d' f).mass a := by
    intro a
    simpa [FiniteKernel.map_mass, recordProb, mul_ite] using h a
  let k : α → ℝ := fun a => if g a = b then 1 else 0
  have hd := FiniteKernel.map_mean d f k
  have hd' := FiniteKernel.map_mean d' f k
  have hh : (∑ a, (FiniteKernel.map d f).mass a * k a) =
      ∑ a, (FiniteKernel.map d' f).mass a * k a := by simp_rw [hm]
  simpa only [recordProb, Function.comp_apply, k] using hd.symm.trans (hh.trans hd')

private theorem pair_ABD (d : FiniteDistribution VisibleOutcome) (b k : Bool) :
    recordProb d (fun o => (o.b,o.d)) (b,k) = ∑ a : Bool, recordProb d abdRecord (a,b,k) := by
  unfold recordProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp only [Fintype.sum_bool, ← mul_add]
  congr 1
  cases o with | mk a b' c d' =>
    cases a <;> cases b <;> cases k <;> cases b' <;> cases d' <;> norm_num [abdRecord,acdRecord]

private theorem pair_ACD (d : FiniteDistribution VisibleOutcome) (c k : Bool) :
    recordProb d (fun o => (o.c,o.d)) (c,k) = ∑ a : Bool, recordProb d acdRecord (a,c,k) := by
  unfold recordProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp only [Fintype.sum_bool, ← mul_add]
  congr 1
  cases o with | mk a b c' d' =>
    cases a <;> cases c <;> cases k <;> cases c' <;> cases d' <;> norm_num [abdRecord,acdRecord]

private theorem pair_AB (d : FiniteDistribution VisibleOutcome) (a b : Bool) :
    recordProb d (fun o => (o.a,o.b)) (a,b) = ∑ k : Bool, recordProb d abdRecord (a,b,k) := by
  unfold recordProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp only [Fintype.sum_bool, ← mul_add]
  congr 1
  cases o with | mk a' b' c d =>
    cases a <;> cases b <;> cases a' <;> cases b' <;> cases d <;> norm_num [abdRecord,acdRecord]

private theorem pair_AC (d : FiniteDistribution VisibleOutcome) (a c : Bool) :
    recordProb d (fun o => (o.a,o.c)) (a,c) = ∑ k : Bool, recordProb d acdRecord (a,c,k) := by
  unfold recordProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp only [Fintype.sum_bool, ← mul_add]
  congr 1
  cases o with | mk a' b c' d =>
    cases a <;> cases c <;> cases a' <;> cases c' <;> cases d <;> norm_num [abdRecord,acdRecord]

private theorem abd_independent {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) (r : Triple) :
    recordProb (p.run e y z) abdRecord r = recordProb (p.run e y false) abdRecord r := by
  unfold recordProb Protocol.run
  rw [FiniteKernel.map_mean, FiniteKernel.map_mean]
  rfl
private theorem acd_independent {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (e : Early) (y z : Bool) (r : Triple) :
    recordProb (p.run e y z) acdRecord r = recordProb (p.run e false z) acdRecord r := by
  unfold recordProb Protocol.run
  rw [FiniteKernel.map_mean, FiniteKernel.map_mean]
  rfl

theorem pinned_A_subsets {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (R : Finset Party) (hR : R ⊆ {.B,.D} ∨ R ⊆ {.C,.D})
    (x y z w : Bool) (r : Party → Bool) :
    recordProb (p.run (earlyOf x w) y z) (setRecord R) r =
      recordProb (p.run (earlyOf false w) y z) (setRecord R) r := by
  rcases hR with hR | hR
  · have hf : setRecord R = (fun q : Bool × Bool => setRecord R ⟨false,q.1,false,q.2⟩) ∘
        (fun o : VisibleOutcome => (o.b,o.d)) := by
      funext o k
      by_cases hk : k ∈ R
      · have := hR hk
        cases k <;> simp_all [setRecord,partyBit]
      · simp [setRecord,hk]
    rw [hf]
    apply record_project
    rintro ⟨b,d⟩
    rw [pair_ABD,pair_ABD]
    simp_rw [abd_independent, ← protocol_ABD]
    exact pinned_BD h x y w b d
  · have hf : setRecord R = (fun q : Bool × Bool => setRecord R ⟨false,false,q.1,q.2⟩) ∘
        (fun o : VisibleOutcome => (o.c,o.d)) := by
      funext o k
      by_cases hk : k ∈ R
      · have := hR hk
        cases k <;> simp_all [setRecord,partyBit]
      · simp [setRecord,hk]
    rw [hf]
    apply record_project
    rintro ⟨c,d⟩
    rw [pair_ACD,pair_ACD]
    simp_rw [acd_independent, ← protocol_ACD]
    exact pinned_CD h x z w c d

theorem pinned_D_subsets {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (R : Finset Party) (hR : R ⊆ {.A,.B} ∨ R ⊆ {.A,.C})
    (x y z w : Bool) (r : Party → Bool) :
    recordProb (p.run (earlyOf x w) y z) (setRecord R) r =
      recordProb (p.run (earlyOf x false) y z) (setRecord R) r := by
  rcases hR with hR | hR
  · have hf : setRecord R = (fun q : Bool × Bool => setRecord R ⟨q.1,q.2,false,false⟩) ∘
        (fun o : VisibleOutcome => (o.a,o.b)) := by
      funext o k
      by_cases hk : k ∈ R
      · have := hR hk
        cases k <;> simp_all [setRecord,partyBit]
      · simp [setRecord,hk]
    rw [hf]
    apply record_project
    rintro ⟨a,b⟩
    rw [pair_AB,pair_AB]
    simp_rw [abd_independent, ← protocol_ABD]
    exact pinned_AB h x y w a b
  · have hf : setRecord R = (fun q : Bool × Bool => setRecord R ⟨q.1,false,q.2,false⟩) ∘
        (fun o : VisibleOutcome => (o.a,o.c)) := by
      funext o k
      by_cases hk : k ∈ R
      · have := hR hk
        cases k <;> simp_all [setRecord,partyBit]
      · simp [setRecord,hk]
    rw [hf]
    apply record_project
    rintro ⟨a,c⟩
    rw [pair_AC,pair_AC]
    simp_rw [acd_independent, ← protocol_ACD]
    exact pinned_AC h x z w a c

/-- Exact zero TV for every directly collectible A-recipient set, with the
segment hypothesis stated explicitly. This includes co-located early parties. -/
theorem zero_accessible_A {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (L : Layout) (R : Finset Party) (hA : Party.A ∉ R)
    (htb : (L .A).t ≤ (L .B).t) (htc : (L .A).t ≤ (L .C).t)
    (hxb : (L .B).x ≤ (L .A).x) (hxc : (L .A).x ≤ (L .C).x)
    (hc : Collectible (L .A) (R.image L)) (x y z w : Bool) :
    (1/2 : ℝ) * ∑ r : Party → Bool,
      |recordProb (p.run (earlyOf x w) y z) (setRecord R) r -
        recordProb (p.run (earlyOf false w) y z) (setRecord R) r| = 0 := by
  have hp := collectible_A_pinned_pair L R hA htb htc hxb hxc hc
  simp_rw [pinned_A_subsets p h R hp x y z w]
  simp

theorem zero_accessible_D {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (L : Layout) (R : Finset Party) (hD : Party.D ∉ R)
    (htb : (L .D).t ≤ (L .B).t) (htc : (L .D).t ≤ (L .C).t)
    (hxb : (L .B).x ≤ (L .D).x) (hxc : (L .D).x ≤ (L .C).x)
    (hc : Collectible (L .D) (R.image L)) (x y z w : Bool) :
    (1/2 : ℝ) * ∑ r : Party → Bool,
      |recordProb (p.run (earlyOf x w) y z) (setRecord R) r -
        recordProb (p.run (earlyOf x false) y z) (setRecord R) r| = 0 := by
  have hp := collectible_D_pinned_pair L R hD htb htc hxb hxc hc
  simp_rw [pinned_D_subsets p h R hp x y z w]
  simp

/-- The every-model branch needs only noncollectibility of the blind pair;
being on the segment is one sufficient geometric reason for that hypothesis. -/
theorem zero_accessible_A_of_blind_pair_not_collectible
    {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (L : Layout) (R : Finset Party) (hA : Party.A ∉ R)
    (hBC : ¬ Collectible (L .A) {L .B,L .C})
    (hc : Collectible (L .A) (R.image L)) (x y z w : Bool) :
    (1/2 : ℝ) * ∑ r : Party → Bool,
      |recordProb (p.run (earlyOf x w) y z) (setRecord R) r -
        recordProb (p.run (earlyOf false w) y z) (setRecord R) r| = 0 := by
  have hp : R ⊆ {.B,.D} ∨ R ⊆ {.C,.D} := by
    rcases recipients_A_dichotomy R hA with hR | hR | hR
    · exact Or.inl hR
    · exact Or.inr hR
    · exfalso
      apply hBC (hc.mono (by simp) ?_)
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact Finset.mem_image.mpr ⟨.B,hR (by simp),rfl⟩
      · exact Finset.mem_image.mpr ⟨.C,hR (by simp),rfl⟩
  simp_rw [pinned_A_subsets p h R hp x y z w]
  simp

theorem zero_accessible_D_of_blind_pair_not_collectible
    {order : EarlyOrder} {Ω : Type} [Fintype Ω]
    (p : Protocol order Ω) (h : ForcedSignalingTheorem2.MatchesCluster p.toModel)
    (L : Layout) (R : Finset Party) (hD : Party.D ∉ R)
    (hBC : ¬ Collectible (L .D) {L .B,L .C})
    (hc : Collectible (L .D) (R.image L)) (x y z w : Bool) :
    (1/2 : ℝ) * ∑ r : Party → Bool,
      |recordProb (p.run (earlyOf x w) y z) (setRecord R) r -
        recordProb (p.run (earlyOf x false) y z) (setRecord R) r| = 0 := by
  have hp : R ⊆ {.A,.B} ∨ R ⊆ {.A,.C} := by
    rcases recipients_D_dichotomy R hD with hR | hR | hR
    · exact Or.inl hR
    · exact Or.inr hR
    · exfalso
      apply hBC (hc.mono (by simp) ?_)
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact Finset.mem_image.mpr ⟨.B,hR (by simp),rfl⟩
      · exact Finset.mem_image.mpr ⟨.C,hR (by simp),rfl⟩
  simp_rw [pinned_D_subsets p h R hp x y z w]
  simp

end
end OntologySeparation.ForcedSignalingAccessible
