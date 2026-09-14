# Extending the framework

## Add a theory without changing the core

Choose a public `Interface`, then define a predicate on its normalized behaviors.
A theory is an explicit value, so different theories coexist without competing
Lean typeclass instances. A theory class need not predict a unique distribution.

```lean
import OntologySeparation
open OntologySeparation

-- A deliberately simple operational restriction for illustrating the API.
def settingIndependent {E : Interface} : Theory E := fun p =>
  ∀ s t o, p.prob s o = p.prob t o
```

A physical model should separately supply a `Witness`. An empty class can satisfy
any universal bound vacuously; the framework does not infer physical existence
from a predicate definition. An `AssumptionProfile` is also only a predicate
until you prove `Realizable` using your selected physical vocabulary.

## Add an experiment

1. Define its settings and public outcomes in an `Interface`.
2. Define the protocol and model interpretation. Internal records remain physical
   systems until the protocol makes them public. For a new dynamics family use
   `Interpreter Protocol E`; a proof of `supports` is required to interpret it.
3. Define an observable of the behavior and prove the prediction or bound.
4. Package universal bounds in `Bound`, realized alternatives in `Witness`, and
   distinguishing results in `Separation`. Its `.excludes` theorem is reusable.
5. Add user-facing operations and assumptions in a `ProtocolDescription`.
6. Optionally register the example in the catalog with a proof-bearing claim.
   The current catalog is a curated example application, not the generic API.

The ten speculative examples are `ProtocolDescription`s with explicit unresolved
obligations. They are not all executable Lean dynamics models. Adding a new
causal-order or gravitational interpreter is real mathematical work, not a
string flag or a new row of invented predictions.

## Add a dephasing universe in three lines

```lean
import OntologySeparation
open OntologySeparation

def quarterDephasing : Memory.Model := ⟨1/4, by norm_num, by norm_num⟩
example : Memory.probability quarterDephasing Memory.echo = 7/8 := by
  rw [Memory.echo_probability]
  norm_num [quarterDephasing]
```

The prediction follows from matrix operations. It is not supplied as an axiom.
`Memory.Model` is a restricted toy family, not a general collapse theory.

## Add an adapter

Keep state spaces, matrices, instruments and tensor choices inside the adapter.
Export a normalized `Behavior` and prove entrywise probability preservation.
Translate observables with equality theorems before importing bounds. Do not
silently equate inequivalent notions of locality or observer records. The
Lean-QIT adapter in `Adapters/Bell.lean` is a worked example.

## Configure foundational assumptions

`Vocabulary M` contains four user-selected predicates on your physical models:
realism, global truth, locality and measurement independence. `Stance.require`
means P; `Stance.reject` means not P; `Stance.unspecified` adds True. The sixteen
binary combinations are enumerable but are not necessarily consistent. Human
free will is not identified with a mathematical probability condition.

Changing a predicate changes the physical question. Record its meaning and
prove any implications before transferring results between vocabularies.

`profileTheory vocabulary profile predict` connects the law selections to your
experimental semantics. It contains exactly the behaviors `predict model` for
models satisfying the profile. `profileWitness` packages a constructed model and
its assumption proofs into the same `Witness` used by Bell and LF comparisons.
`profileTheory_empty` proves that an inconsistent profile cannot produce a member,
regardless of the predictor. This is a genuine connection to experiment comparison,
not merely sixteen checkboxes in the report.
