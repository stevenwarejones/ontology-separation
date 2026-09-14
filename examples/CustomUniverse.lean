import OntologySeparation
open OntologySeparation

/-! A minimal adoption example: choose new dynamics and reuse a parametric proof.
No custom axiom, catalog edit, or global typeclass instance is required. -/
def quarterNoise : Memory.Model := ⟨1/4, by norm_num, by norm_num⟩

example : Memory.probability quarterNoise Memory.echo = 7/8 := by
  rw [Memory.echo_probability]
  norm_num [quarterNoise]

example : Memory.probability quarterNoise Memory.leakedEcho = 1/2 :=
  Memory.leakedEcho_probability quarterNoise

example : ∀ d : Bool → Rat, Research.oneBitRecovery d = 1/2 :=
  Research.restricted_recovery

example (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (6 < RealQuantum.genuineLF
      (DephasedSinglet.behavior RealQuantum.lfAlice RealQuantum.lfBob p h0 h1)) ↔
    p < 65453/238464 := DephasedSinglet.LF_noise_threshold p h0 h1
