import OntologySeparation.Operational.HiddenInfluence

namespace OntologySeparation.HiddenInfluence
open scoped BigOperators

noncomputable def atomWeights {Ω : Type} [Fintype Ω] (atoms : Ω → Atom) (p : Ω → ℝ) (j : Atom) : ℝ :=
  ∑ k, if atoms k = j then p k else 0

theorem atomWeights_sum {Ω : Type} [Fintype Ω] (atoms : Ω → Atom) (p : Ω → ℝ) (f : Atom → ℝ) :
    (∑ j, f j * atomWeights atoms p j) = ∑ k, f (atoms k) * p k := by
  simp only [atomWeights, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_ite]

/-- Build a physical finite response mixture. Normalization is per early setting. -/
noncomputable def Model.ofAtoms {Ω : Type} [Fintype Ω] (atoms : Ω → Atom) (p : Ω → ℝ)
    (nonneg : ∀ k, 0 ≤ p k)
    (total : ∀ e, (∑ k, if early (atoms k) = e then p k else 0) = 1) : Model where
  weight := atomWeights atoms p
  nonnegative j := Finset.sum_nonneg fun k _ => by split <;> simp [nonneg]
  normalized e := by
    have h := atomWeights_sum atoms p (fun j => if early j = e then 1 else 0)
    simpa [ite_mul, total] using h

theorem ofAtoms_score {Ω : Type} [Fintype Ω] (a : Ω → Atom) (p : Ω → ℝ) (h0 h1) :
    score (Model.ofAtoms a p h0 h1).behavior = ∑ k, (scoreCoeff (a k) : ℝ) * p k := by
  rw [score_eq]
  exact atomWeights_sum a p _

theorem ofAtoms_difference {Ω : Type} [Fintype Ω] (a : Ω → Atom) (p : Ω → ℝ) (h0 h1) (c o) :
    difference (Model.ofAtoms a p h0 h1).behavior c o =
      ∑ k, (differenceCoeff c o (a k) : ℝ) * p k := by
  rw [difference_eq]
  exact atomWeights_sum a p _

/-- A deterministic causal response table with named physical outputs.
`false` and `true` correspond to +1 and -1 in correlations.
Boolean fields reject out-of-range numeric entries instead of wrapping modulo two. -/
structure Strategy where
  a : Bool
  d : Bool
  b0 : Bool
  b1 : Bool
  c0 : Bool
  c1 : Bool
  deriving DecidableEq, Fintype

def strategyAtom (e : Early) (s : Strategy) : Atom :=
  ⟨64*e.val + 32*s.a.toNat + 16*s.d.toNat + 4*(s.b0.toNat+2*s.b1.toNat) +
    s.c0.toNat + 2*s.c1.toNat, by
      have := Bool.toNat_le s.a; have := Bool.toNat_le s.d
      have := Bool.toNat_le s.b0; have := Bool.toNat_le s.b1
      have := Bool.toNat_le s.c0; have := Bool.toNat_le s.c1
      omega⟩

theorem strategy_early (e : Early) (s : Strategy) : early (strategyAtom e s) = e := by
  apply Fin.ext
  dsimp [early, strategyAtom]
  have := Bool.toNat_le s.a; have := Bool.toNat_le s.d
  have := Bool.toNat_le s.b0; have := Bool.toNat_le s.b1
  have := Bool.toNat_le s.c0; have := Bool.toNat_le s.c1
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Named fields mean exactly the four outputs used by the operational behavior.
This finite identity also checks the B/C setting and tensor ordering. -/
theorem strategy_output : ∀ (e : Early) (s : Strategy) (y z : Bool),
    (output (strategyAtom e s) ⟨2*y.toNat+z.toNat, by
      have := Bool.toNat_le y; have := Bool.toNat_le z; omega⟩).val =
      8*s.a.toNat + 4*(if y then s.b1 else s.b0).toNat +
        2*(if z then s.c1 else s.c0).toNat + s.d.toNat := by decide

/-- Supply four ordinary finite distributions over named response strategies.
No packed atom indices or LP constraints appear in this constructor's inputs. -/
noncomputable def Model.fromStrategies (q : Early → FiniteDistribution Strategy) : Model :=
  Model.ofAtoms (fun k : Early × Strategy => strategyAtom k.1 k.2)
    (fun k => (q k.1).mass k.2) (fun k => (q k.1).nonneg k.2)
    (fun e => by
      simp only [strategy_early, Fintype.sum_prod_type]
      simp [Finset.sum_ite_irrel, (q e).total])

end OntologySeparation.HiddenInfluence
