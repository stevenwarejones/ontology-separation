import OntologySeparation.Core.ExactFiniteChecker

/-! Automatic complete grids for explicitly supplied finite protocol families.

Coverage is derived from finite enumeration; it is never accepted as an
assumption. This layer is only for discrete Fintype-backed settings/outcomes. -/
namespace OntologySeparation.ExactFinite

variable {P : Type} {E : Interface}

/-- A nonempty finite protocol family. The represented access predicate is
exactly membership in this supplied list. -/
structure ProtocolFamily (P : Type) where
  head : P
  tail : List P

def ProtocolFamily.protocols (family : ProtocolFamily P) : List P :=
  family.head :: family.tail

def ProtocolFamily.allowed [DecidableEq P] (family : ProtocolFamily P) (p : P) : Prop :=
  p ∈ family.protocols

variable [DecidableEq P] [Fintype E.Setting] [DecidableEq E.Setting]
  [DecidableEq E.Outcome]

def entriesForProtocol (p : P) : List (Entry P E) :=
  (Finset.univ : Finset E.Setting).toList.flatMap fun s =>
    (Finset.univ : Finset E.Outcome).toList.map fun o => ⟨p, s, o⟩

def ProtocolFamily.entries (family : ProtocolFamily P) : List (Entry P E) :=
  family.protocols.flatMap entriesForProtocol

theorem mem_entriesForProtocol (p : P) (s : E.Setting) (o : E.Outcome) :
    Entry.mk p s o ∈ entriesForProtocol (E := E) p := by
  simp [entriesForProtocol]

theorem entry_protocol_mem {family : ProtocolFamily P} {x : Entry P E}
    (hx : x ∈ family.entries) : x.protocol ∈ family.protocols := by
  simp only [ProtocolFamily.entries, List.mem_flatMap] at hx
  rcases hx with ⟨p, hp, hx⟩
  have hprotocol : x.protocol = p := by
    simp [entriesForProtocol] at hx
    rcases hx with ⟨s, _, o, _, rfl⟩
    rfl
  simpa [hprotocol] using hp

/-- Build the complete protocol × setting × outcome grid. The coverage proof is
derived from enumeration of both Fintype dimensions. -/
def ProtocolFamily.grid (family : ProtocolFamily P) :
    Grid P E family.allowed where
  entries := family.entries
  protocol := family.head
  included := by simp [ProtocolFamily.allowed, ProtocolFamily.protocols]
  accessible := by
    intro x hx
    exact entry_protocol_mem hx
  covers := by
    intro p hp s o
    simp only [ProtocolFamily.entries, List.mem_flatMap]
    exact ⟨p, hp, mem_entriesForProtocol p s o⟩

/-- One-call comparison for a nonempty supplied protocol list. No handwritten
coverage proof is accepted: `family.grid` discharges it by finite enumeration. -/
def certifyFamily {M : Type} {predict : ExperimentAccess.Predictions M P E}
    (backend : Backend predict) (family : ProtocolFamily P) (a b : M) :
    CheckedResult backend family.allowed a b :=
  certify backend family.allowed family.grid a b

end OntologySeparation.ExactFinite
