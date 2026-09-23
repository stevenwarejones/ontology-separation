import OntologySeparation.Core.AdversarySearch
import OntologySeparation.Experiments.Research

/-! A locality-free friend benchmark that collapses to contextual gluing.

Three contexts are allowed to carry separate joint fact distributions.  Two laws
are tested independently:

* sharedFacts: the context-specific latent distributions are one common joint fact;
* faithfulContexts: each selected edge reproduces the observed perfect
  anticorrelation table.

No spatial locality assumption appears.  The conjunction is inconsistent, while
deleting either law has an explicit countermodel in the same model language. -/

namespace OntologySeparation.LocalityFreeFriendliness
noncomputable section

open AdversarySearch
open Research

def ABMatches (d : FiniteDistribution Triple) : Prop :=
  ∀ a b, (∑ c : Bool, d.mass (a,b,c)) = (pairwise a b : ℝ)

def BCMatches (d : FiniteDistribution Triple) : Prop :=
  ∀ b c, (∑ a : Bool, d.mass (a,b,c)) = (pairwise b c : ℝ)

def ACMatches (d : FiniteDistribution Triple) : Prop :=
  ∀ a c, (∑ b : Bool, d.mass (a,b,c)) = (pairwise a c : ℝ)

structure Model where
  abFacts : FiniteDistribution Triple
  bcFacts : FiniteDistribution Triple
  acFacts : FiniteDistribution Triple

inductive Law where
  | sharedFacts
  | faithfulContexts
  deriving DecidableEq, Repr

def Holds : Law → Model → Prop
  | .sharedFacts, m => m.abFacts = m.bcFacts ∧ m.bcFacts = m.acFacts
  | .faithfulContexts, m =>
      ABMatches m.abFacts ∧ BCMatches m.bcFacts ∧ ACMatches m.acFacts

/-- The target simply asks whether the proposed ontology is internally realizable.
The two-law core excludes every model. -/
def Target (_ : Model) : Prop := True

def core : Finset Law := {.sharedFacts, .faithfulContexts}

def antiAB : FiniteDistribution Triple where
  mass v :=
    if v = (false,true,false) ∨ v = (true,false,false) then 1/2 else 0
  nonneg v := by
    split <;> norm_num
  total := by
    norm_num [Fintype.sum_prod_type]

def antiBC : FiniteDistribution Triple where
  mass v :=
    if v = (false,false,true) ∨ v = (false,true,false) then 1/2 else 0
  nonneg v := by
    split <;> norm_num
  total := by
    norm_num [Fintype.sum_prod_type]

def antiAC : FiniteDistribution Triple where
  mass v :=
    if v = (false,false,true) ∨ v = (true,false,false) then 1/2 else 0
  nonneg v := by
    split <;> norm_num
  total := by
    norm_num [Fintype.sum_prod_type]

theorem antiAB_matches : ABMatches antiAB := by
  intro a b
  cases a <;> cases b <;> norm_num [ABMatches, antiAB, pairwise]

theorem antiBC_matches : BCMatches antiBC := by
  intro b c
  cases b <;> cases c <;> norm_num [BCMatches, antiBC, pairwise]

theorem antiAC_matches : ACMatches antiAC := by
  intro a c
  cases a <;> cases c <;> norm_num [ACMatches, antiAC, pairwise]

def contextualAdversary : Model where
  abFacts := antiAB
  bcFacts := antiBC
  acFacts := antiAC

theorem contextualAdversary_faithful :
    Holds .faithfulContexts contextualAdversary :=
  ⟨antiAB_matches, antiBC_matches, antiAC_matches⟩

def sharedAdversary : Model where
  abFacts := antiAB
  bcFacts := antiAB
  acFacts := antiAB

theorem sharedAdversary_shared :
    Holds .sharedFacts sharedAdversary := by
  exact ⟨rfl, rfl⟩

/-- Shared facts plus faithful readout would give a single gluing distribution,
contradicting the checked triangle marginal obstruction. -/
theorem shared_and_faithful_impossible (m : Model)
    (hs : Holds .sharedFacts m) (hf : Holds .faithfulContexts m) : False := by
  rcases hs with ⟨hab, hbc⟩
  rcases hf with ⟨hAB, hBC, hAC⟩
  rw [← hab] at hBC
  rw [← hbc, ← hab] at hAC
  have hglue : GluesPairwise m.abFacts := by
    exact ⟨hAB, hBC, hAC⟩
  exact Research.no_pairwise_gluing ⟨m.abFacts, hglue⟩

/-- The locality-free two-premise core is deletion-minimal. -/
def certificate : MinimalCore Holds Target core where
  excludes := by
    intro m hm _
    exact shared_and_faithful_impossible m
      (hm .sharedFacts (by simp [core]))
      (hm .faithfulContexts (by simp [core]))
  deletionAdversary := by
    intro law hlaw
    cases law with
    | sharedFacts =>
        refine ⟨contextualAdversary, ?_, trivial⟩
        intro kept hkept
        cases kept with
        | sharedFacts => simp [core] at hkept
        | faithfulContexts => exact contextualAdversary_faithful
    | faithfulContexts =>
        refine ⟨sharedAdversary, ?_, trivial⟩
        intro kept hkept
        cases kept with
        | sharedFacts => exact sharedAdversary_shared
        | faithfulContexts => simp [core] at hkept

theorem locality_free_core_minimal :
    (∀ m, Satisfies Holds core m → ¬ Target m) ∧
    (∃ m, Satisfies Holds (core.erase .sharedFacts) m ∧ Target m) ∧
    (∃ m, Satisfies Holds (core.erase .faithfulContexts) m ∧ Target m) := by
  refine ⟨certificate.excludes, ?_, ?_⟩
  · exact certificate.deletionAdversary .sharedFacts (by simp [core])
  · exact certificate.deletionAdversary .faithfulContexts (by simp [core])

end
end OntologySeparation.LocalityFreeFriendliness
