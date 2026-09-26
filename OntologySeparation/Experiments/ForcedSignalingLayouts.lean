import OntologySeparation.Operational.Collectibility
import OntologySeparation.Operational.VCausal

namespace OntologySeparation.ForcedSignalingLayouts
open VCausal

def minimal : Layout
  | .A => ⟨0,-1⟩
  | .D => ⟨11/20,1⟩
  | .B => ⟨17/20,-1/10⟩
  | .C => ⟨17/20,1/10⟩

theorem minimal_lc4 : LC4Layout minimal 4 := by
  constructor <;> norm_num [precedes, minimal]

theorem minimal_order : GeometryOrder minimal 4 .aFirst := by
  norm_num [GeometryOrder, precedes, minimal]

theorem minimal_A_collectible : Collectible (minimal .A)
    {minimal .B, minimal .C, minimal .D} := by
  refine ⟨by simp, ⟨39/20,1⟩, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [lightFuture, minimal]
  · norm_num [lightFuture, minimal]

theorem minimal_D_collectible : Collectible (minimal .D)
    {minimal .A, minimal .B, minimal .C} := by
  refine ⟨by simp, ⟨39/20,-1⟩, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [lightFuture, minimal]
  · norm_num [lightFuture, minimal]

theorem minimal_margins :
    (minimal .A).t + |(1 : ℚ) - (minimal .A).x| - 39/20 = 1/20 ∧
    (minimal .D).t + |(-1 : ℚ) - (minimal .D).x| - 39/20 = 3/5 := by
  norm_num [minimal]

/-- Exact SI c. Times are converted to ct in metres, so hidden speed is v/c. -/
def lightSpeed : ℚ := 299792458

def restoration : Layout
  | .A => ⟨0,-6000⟩
  | .D => ⟨lightSpeed/10000000,6000⟩
  | .B => ⟨lightSpeed/5000000,-5000⟩
  | .C => ⟨lightSpeed/5000000,5000⟩

theorem restoration_lc4 : LC4Layout restoration 10000 := by
  constructor <;> norm_num [precedes, restoration, lightSpeed]

theorem restoration_order : GeometryOrder restoration 10000 .aFirst := by
  norm_num [GeometryOrder, precedes, restoration, lightSpeed]

theorem restoration_A_collectible : Collectible (restoration .A)
    {restoration .B, restoration .C, restoration .D} := by
  refine ⟨by simp, ⟨lightSpeed/5000000 + 11000,6000⟩, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [lightFuture, restoration, lightSpeed]
  · norm_num [lightFuture, restoration, lightSpeed]

theorem restoration_D_collectible : Collectible (restoration .D)
    {restoration .A, restoration .B, restoration .C} := by
  refine ⟨by simp, ⟨lightSpeed/5000000 + 11000,-6000⟩, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [lightFuture, restoration, lightSpeed]
  · norm_num [lightFuture, restoration, lightSpeed]

/-- The printed 400.28 is a rounded threshold, not an exact equality. -/
theorem restoration_threshold_rounding :
    (400275 : ℚ)/1000 < 12000 / (lightSpeed/10000000) ∧
    12000 / (lightSpeed/10000000) < (400285 : ℚ)/1000 := by
  norm_num [lightSpeed]

end OntologySeparation.ForcedSignalingLayouts
