import OntologySeparation.Core.ExactFinite
import Mathlib.Tactic

/-! Executable exact comparison over an explicitly supplied finite grid.

The scanner only inspects rational probabilities. Proof fields connect its result
back to the common ExperimentAccess semantics. A grid must prove both access and
coverage before an all-equal scan can become FamilyAgreement. -/
namespace OntologySeparation.ExactFinite

open ExperimentAccess
open Comparison

variable {P M : Type} {E : Interface} {predict : Predictions M P E}

structure Entry (P : Type) (E : Interface) where
  protocol : P
  setting : E.Setting
  outcome : E.Outcome

structure Grid (P : Type) (E : Interface) (family : P → Prop) where
  entries : List (Entry P E)
  protocol : P
  included : family protocol
  accessible : ∀ x, x ∈ entries → family x.protocol
  covers : ∀ p, family p → ∀ s o, Entry.mk p s o ∈ entries

inductive EntryComparison (backend : Backend predict) (a b : M) (x : Entry P E)
  | equal (proof : backend.probability a x.protocol x.setting x.outcome =
      backend.probability b x.protocol x.setting x.outcome)
  | ab (proof : backend.probability b x.protocol x.setting x.outcome <
      backend.probability a x.protocol x.setting x.outcome)
  | ba (proof : backend.probability a x.protocol x.setting x.outcome <
      backend.probability b x.protocol x.setting x.outcome)

def compareEntry (backend : Backend predict) (a b : M) (x : Entry P E) :
    EntryComparison backend a b x := by
  let pa := backend.probability a x.protocol x.setting x.outcome
  let pb := backend.probability b x.protocol x.setting x.outcome
  if h : pa = pb then
    exact .equal h
  else if hba : pb < pa then
    exact .ab hba
  else
    have hle : pa ≤ pb := le_of_not_gt hba
    have hlt : pa < pb := lt_of_le_of_ne hle h
    exact .ba hlt

inductive ScanResult (backend : Backend predict) (a b : M) :
    List (Entry P E) → Type
  | agreement {entries}
      (proof : ∀ x, x ∈ entries →
        backend.probability a x.protocol x.setting x.outcome =
          backend.probability b x.protocol x.setting x.outcome) :
      ScanResult backend a b entries
  | separatesAB {entries} (entry : Entry P E) (member : entry ∈ entries)
      (proof : backend.probability b entry.protocol entry.setting entry.outcome <
        backend.probability a entry.protocol entry.setting entry.outcome) :
      ScanResult backend a b entries
  | separatesBA {entries} (entry : Entry P E) (member : entry ∈ entries)
      (proof : backend.probability a entry.protocol entry.setting entry.outcome <
        backend.probability b entry.protocol entry.setting entry.outcome) :
      ScanResult backend a b entries

def scan (backend : Backend predict) (a b : M) :
    (entries : List (Entry P E)) → ScanResult backend a b entries
  | [] => .agreement (by intro x hx; simp at hx)
  | x :: xs =>
      match compareEntry backend a b x with
      | .ab h => .separatesAB x (List.mem_cons_self) h
      | .ba h => .separatesBA x (List.mem_cons_self) h
      | .equal hx =>
          match scan backend a b xs with
          | .separatesAB y hy h => .separatesAB y (List.mem_cons_of_mem x hy) h
          | .separatesBA y hy h => .separatesBA y (List.mem_cons_of_mem x hy) h
          | .agreement hxs =>
              .agreement (by
                intro y hy
                simp only [List.mem_cons] at hy
                rcases hy with rfl | hy
                · exact hx
                · exact hxs y hy)

inductive CheckedResult (backend : Backend predict) (family : P → Prop) (a b : M)
  | agreement (certificate : FamilyAgreement predict family a b)
  | separatesAB (certificate : Separator predict family a b)
  | separatesBA (certificate : Separator predict family b a)

/-- Convert every automatic result into the repository's existing audited claim
vocabulary. Reverse-orientation separators preserve the model order they prove. -/
def CheckedResult.claim {backend : Backend predict} {family : P → Prop} {a b : M} :
    CheckedResult backend family a b → Claim
  | .agreement certificate =>
      .agreement predict family a b certificate.proof
  | .separatesAB certificate =>
      .separation predict family a b certificate
  | .separatesBA certificate =>
      .separation predict family b a certificate

theorem CheckedResult.sound {backend : Backend predict} {family : P → Prop} {a b : M}
    (result : CheckedResult backend family a b) : result.claim.statement :=
  result.claim.sound

def certify (backend : Backend predict) (family : P → Prop)
    (grid : Grid P E family) (a b : M) :
    CheckedResult backend family a b :=
  match scan backend a b grid.entries with
  | .agreement h =>
      .agreement {
        proof := by
          intro p hp s o
          have he := h (Entry.mk p s o) (grid.covers p hp s o)
          rw [backend.correct, backend.correct]
          exact_mod_cast he
        protocol := grid.protocol
        included := grid.included }
  | .separatesAB x hx hlt =>
      .separatesAB {
        protocol := x.protocol
        accessible := grid.accessible x hx
        setting := x.setting
        outcome := x.outcome
        gap := ((backend.probability a x.protocol x.setting x.outcome -
          backend.probability b x.protocol x.setting x.outcome : ℚ) : ℝ)
        positive := by exact_mod_cast sub_pos.mpr hlt
        difference := by
          rw [backend.correct, backend.correct]
          push_cast
          rfl }
  | .separatesBA x hx hlt =>
      .separatesBA {
        protocol := x.protocol
        accessible := grid.accessible x hx
        setting := x.setting
        outcome := x.outcome
        gap := ((backend.probability b x.protocol x.setting x.outcome -
          backend.probability a x.protocol x.setting x.outcome : ℚ) : ℝ)
        positive := by exact_mod_cast sub_pos.mpr hlt
        difference := by
          rw [backend.correct, backend.correct]
          push_cast
          rfl }

end OntologySeparation.ExactFinite
