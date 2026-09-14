import OntologySeparation

open OntologySeparation

example : ¬ LF.theory RealQuantum.lfBehavior := LF.quantumSeparation.excludes
example (m : Memory.Model) :
    Memory.probability m Memory.echo = 1 - m.strength / 2 := Memory.echo_probability m

def settingIndependent {E : Interface} : Theory E := fun p =>
  ∀ s t o, p.prob s o = p.prob t o

def quarterDephasing : Memory.Model := ⟨1/4, by norm_num, by norm_num⟩
example : Memory.probability quarterDephasing Memory.echo = 7/8 := by
  rw [Memory.echo_probability]
  norm_num [quarterDephasing]
