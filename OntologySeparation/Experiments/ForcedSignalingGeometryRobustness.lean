import OntologySeparation.Experiments.ForcedSignalingCollectibility

/-! Geometric robustness only: finite durations and candidate preferred frames.
The scaled Lorentz coordinates omit the common positive gamma factor, which
cancels from all homogeneous cone inequalities. No delay-cover claim is made. -/
namespace OntologySeparation.ForcedSignalingGeometryRobustness
open VCausal ForcedSignalingLayouts ForcedSignalingCollectibility

def delayed (p : Event) (dt : ℚ) : Event := ⟨p.t + dt, p.x⟩
def durationLayout (L : Layout) (dt : Party → ℚ) : Layout := fun p => delayed (L p) (dt p)

/-- A cone edge survives independent nonnegative time errors at most epsilon
when its time and cone slack dominate that error. -/
theorem precedes_duration {v ε : ℚ} {p q : Event} {dp dq : ℚ}
    (hv : 0 ≤ v) (hp : 0 ≤ dp) (hp' : dp ≤ ε) (hq : 0 ≤ dq) (hq' : dq ≤ ε)
    (ht : p.t + ε < q.t)
    (hs : |q.x - p.x| + v * ε < v * (q.t - p.t)) :
    precedes v (delayed p dp) (delayed q dq) := by
  constructor
  · change p.t + dp < q.t + dq
    linarith
  · change |q.x - p.x| < v * ((q.t + dq) - (p.t + dp))
    nlinarith

/-- The minimal example tolerates each outcome occurring independently up to
1/100 time units after its choice. This is an exact conservative margin. -/
theorem minimal_duration_lc4 (dt : Party → ℚ)
    (h0 : ∀ p, 0 ≤ dt p) (h1 : ∀ p, dt p ≤ 1/100) :
    LC4Layout (durationLayout minimal dt) 4 := by
  have ha := h0 .A; have hb := h0 .B; have hc := h0 .C; have hd := h0 .D
  have ha' := h1 .A; have hb' := h1 .B; have hc' := h1 .C; have hd' := h1 .D
  constructor <;> norm_num [durationLayout, delayed, minimal, precedes]
  all_goals repeat' first | apply And.intro | intro
  all_goals linarith

theorem minimal_duration_order (dt : Party → ℚ)
    (h0 : ∀ p, 0 ≤ dt p) (h1 : ∀ p, dt p ≤ 1/100) :
    GeometryOrder (durationLayout minimal dt) 4 .aFirst := by
  have ha := h0 .A; have hd := h0 .D
  have ha' := h1 .A; have hd' := h1 .D
  norm_num [GeometryOrder, durationLayout, delayed, minimal, precedes]
  constructor <;> linarith

/-- Choices precede outcomes at each stationary measurement site. -/
def finiteDuration (L : Layout) (dt : Party → ℚ) (h0 : ∀ p, 0 ≤ dt p) :
    MeasurementLayout where
  choice := L
  outcome := durationLayout L dt
  choice_before p := by simpa [durationLayout, delayed, lightFuture] using h0 p

/-- These stronger checks also exclude a hidden link from either late choice
into the other late outcome, and deliver early outcomes before late choices. -/
theorem minimal_duration_cross_events (dt : Party → ℚ)
    (h0 : ∀ p, 0 ≤ dt p) (h1 : ∀ p, dt p ≤ 1/100) :
    precedes 4 (delayed (minimal .A) (dt .A)) (minimal .B) ∧
    precedes 4 (delayed (minimal .A) (dt .A)) (minimal .C) ∧
    precedes 4 (delayed (minimal .D) (dt .D)) (minimal .B) ∧
    precedes 4 (delayed (minimal .D) (dt .D)) (minimal .C) ∧
    ¬ precedes 4 (minimal .B) (delayed (minimal .C) (dt .C)) ∧
    ¬ precedes 4 (minimal .C) (delayed (minimal .B) (dt .B)) := by
  have ha := h0 .A; have hb := h0 .B; have hc := h0 .C; have hd := h0 .D
  have ha' := h1 .A; have hb' := h1 .B; have hc' := h1 .C; have hd' := h1 .D
  norm_num [delayed, minimal, precedes]
  repeat' first | apply And.intro | intro
  all_goals linarith

/-- Positive collector delays strictly below the smaller sender margin keep
both concrete collectors valid, even though initial receipt is on a boundary. -/
theorem minimal_collector_delay (d : ℚ) (h0 : 0 ≤ d) (h1 : d < 1/20) :
    (∀ r ∈ ({minimal .B,minimal .C,minimal .D} : Finset Event),
      lightFuture r ⟨39/20+d,1⟩) ∧ ¬ lightFuture (minimal .A) ⟨39/20+d,1⟩ ∧
    (∀ r ∈ ({minimal .A,minimal .B,minimal .C} : Finset Event),
      lightFuture r ⟨39/20+d,-1⟩) ∧ ¬ lightFuture (minimal .D) ⟨39/20+d,-1⟩ := by
  norm_num [minimal, lightFuture]
  repeat' first | apply And.intro | intro
  all_goals linarith

/-- Outcome durations also preserve usable collection: move the two
collectors later by the maximal duration, still below both sender margins. -/
theorem minimal_duration_collectible (dt : Party → ℚ)
    (h0 : ∀ p, 0 ≤ dt p) (h1 : ∀ p, dt p ≤ 1/100) :
    BothCollectible (durationLayout minimal dt) := by
  have ha := h0 .A; have hb := h0 .B; have hc := h0 .C; have hd := h0 .D
  have ha' := h1 .A; have hb' := h1 .B; have hc' := h1 .C; have hd' := h1 .D
  constructor
  · refine ⟨by simp, ⟨39/20+1/100,1⟩, ?_, ?_⟩
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;>
        norm_num [durationLayout,delayed,minimal,lightFuture] <;> linarith
    · norm_num [durationLayout,delayed,minimal,lightFuture]
      linarith
  · refine ⟨by simp, ⟨39/20+1/100,-1⟩, ?_, ?_⟩
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;>
        norm_num [durationLayout,delayed,minimal,lightFuture] <;> linarith
    · norm_num [durationLayout,delayed,minimal,lightFuture]
      linarith

/-- Rational coordinates proportional to a Lorentz boost by beta. -/
def boost (β : ℚ) (p : Event) : Event := ⟨p.t - β*p.x, p.x - β*p.t⟩

theorem boost_lightFuture (β : ℚ) (hβ : |β| < 1) (p q : Event) :
    lightFuture (boost β p) (boost β q) ↔ lightFuture p q := by
  rw [lightFuture_iff, lightFuture_iff]
  have hb := abs_lt.mp hβ
  unfold plus minus boost
  dsimp only
  constructor
  · rintro ⟨hp,hm⟩
    constructor <;> nlinarith
  · rintro ⟨hp,hm⟩
    constructor <;> nlinarith

theorem boost_collectible (β : ℚ) (hβ : |β| < 1) {s : Event} {R : Finset Event}
    (h : Collectible s R) : Collectible (boost β s) (R.image (boost β)) := by
  obtain ⟨hne,q,hq,hs⟩ := h
  refine ⟨hne.image _, boost β q, ?_, ?_⟩
  · intro r hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    exact (boost_lightFuture β hβ a q).mpr (hq a ha)
  · exact fun h => hs ((boost_lightFuture β hβ s q).mp h)

theorem restoration_boost_collectible (β : ℚ) (hβ : |β| < 1) :
    BothCollectible (fun p => boost β (restoration p)) := by
  constructor
  · simpa using boost_collectible β hβ restoration_A_collectible
  · simpa using boost_collectible β hβ restoration_D_collectible

private theorem boost_precedes_iff (β v : ℚ) (p q : Event) :
    precedes v (boost β p) (boost β q) ↔
      0 < (q.t-p.t)-β*(q.x-p.x) ∧
      |(q.x-p.x)-β*(q.t-p.t)| < v*((q.t-p.t)-β*(q.x-p.x)) := by
  unfold precedes boost
  dsimp only
  rw [← sub_pos]
  rw [show (q.t-β*q.x)-(p.t-β*p.x) = (q.t-p.t)-β*(q.x-p.x) by ring]
  rw [show (q.x-β*q.t)-(p.x-β*p.t) = (q.x-p.x)-β*(q.t-p.t) by ring]

/-- An explicit semialgebraic description of the exact candidate-frame set.
The four positive edges have positive time differences as well as open-cone
inequalities. The last two tests include the hidden-cone boundary. -/
def restorationFrameTests (β v : ℚ) : Prop :=
  let τ := lightSpeed/10000000
  1 < v ∧
  (0 < 2*τ-1000*β ∧ |1000-2*τ*β| < v*(2*τ-1000*β)) ∧
  (0 < 2*τ-11000*β ∧ |11000-2*τ*β| < v*(2*τ-11000*β)) ∧
  (0 < τ+11000*β ∧ |-11000-τ*β| < v*(τ+11000*β)) ∧
  (0 < τ+1000*β ∧ |-1000-τ*β| < v*(τ+1000*β)) ∧
  ¬ (0 < -10000*β ∧ 10000 < v*(-10000*β)) ∧
  ¬ (0 < 10000*β ∧ 10000 < v*(10000*β))

/-- For |beta|<1 collectibility imposes no further restriction; these exact
inequalities describe every speed/frame pair with the required blind layout. -/
theorem restoration_frame_iff (β v : ℚ) (hβ : |β| < 1) :
    (LC4Layout (fun p => boost β (restoration p)) v ∧
      BothCollectible (fun p => boost β (restoration p))) ↔ restorationFrameTests β v := by
  have hc := restoration_boost_collectible β hβ
  have he : LC4Layout (fun p => boost β (restoration p)) v ↔ restorationFrameTests β v := by
    have unpack : LC4Layout (fun p => boost β (restoration p)) v ↔
        1 < v ∧
        precedes v (boost β (restoration .A)) (boost β (restoration .B)) ∧
        precedes v (boost β (restoration .A)) (boost β (restoration .C)) ∧
        precedes v (boost β (restoration .D)) (boost β (restoration .B)) ∧
        precedes v (boost β (restoration .D)) (boost β (restoration .C)) ∧
        ¬ precedes v (boost β (restoration .B)) (boost β (restoration .C)) ∧
        ¬ precedes v (boost β (restoration .C)) (boost β (restoration .B)) :=
      ⟨fun h => ⟨h.speed,h.ab,h.ac,h.db,h.dc,h.bc,h.cb⟩,
       fun ⟨hs,hab,hac,hdb,hdc,hbc,hcb⟩ => ⟨hs,hab,hac,hdb,hdc,hbc,hcb⟩⟩
    rw [unpack]
    simp only [boost_precedes_iff]
    norm_num [restorationFrameTests, restoration, lightSpeed, mul_comm]
  exact ⟨fun h => he.mp h.1, fun h => ⟨he.mpr h,hc⟩⟩

/-- Exact additional condition for retaining A-before-D in a candidate frame. -/
theorem restoration_frame_order_iff (β v : ℚ) :
    GeometryOrder (fun p => boost β (restoration p)) v .aFirst ↔
      (0 < lightSpeed/10000000-12000*β ∧
       |12000-(lightSpeed/10000000)*β| < v*(lightSpeed/10000000-12000*β)) := by
  unfold GeometryOrder
  rw [boost_precedes_iff]
  norm_num [restoration, lightSpeed, mul_comm]

/-- For these fixed laboratory B/C events, a candidate boost retains the
blind pair exactly in this speed-dependent window. Early A-to-D inclusion
alone does not establish this condition. The hidden-cone boundary is included. -/
theorem restoration_blind_iff (β v : ℚ) (hv : 0 ≤ v) :
    (¬ precedes v (boost β (restoration .B)) (boost β (restoration .C)) ∧
     ¬ precedes v (boost β (restoration .C)) (boost β (restoration .B))) ↔
      v * |β| ≤ 1 := by
  simp only [boost_precedes_iff]
  norm_num [restoration, lightSpeed]
  by_cases hb : 0 ≤ β
  · rw [abs_of_nonneg hb]
    constructor
    · rintro ⟨hbc,hcb⟩
      by_contra h
      have hp : 0 < β := by nlinarith
      exact hcb ⟨by linarith, by nlinarith⟩
    · intro h
      constructor <;> rintro ⟨ht,hs⟩ <;> nlinarith
  · rw [abs_of_neg (lt_of_not_ge hb)]
    constructor
    · rintro ⟨hbc,hcb⟩
      by_contra h
      exact hbc ⟨by linarith, by nlinarith⟩
    · intro h
      constructor <;> rintro ⟨ht,hs⟩ <;> nlinarith

end OntologySeparation.ForcedSignalingGeometryRobustness
