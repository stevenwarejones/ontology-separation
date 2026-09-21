# Build a two-qubit Bell experiment

Prepare an entangled pair, choose local measurements, and compare exact CHSH
predictions under different noise laws. Lean supplies the proofs for every
supported recipe. Start with the [one-time setup](START_HERE.md#1-set-up-once).

## Create and run

```sh
ontology-separation new-scenario BellStudy --backend two-qubit -o examples/BellStudy.lean
ontology-separation scenario-report examples/BellStudy.lean -o examples/bell-study.html
```

Open `examples/bell-study.html`: four laws × three preparations, **12 checked
scores**. [The checked-in example](../examples/two-qubit-comparison.html) uses the
same starter. The first two columns match: one prepares a singlet directly,
the other builds it with gates. The third prepares a product state.

## Read the experiment

```lean
open OntologySeparation.TwoQubit

def direct : Recipe := { singletRecipe with steps := [.expose .alice] }

def circuit : Recipe :=
  { direct with
    prepare := .product false false
    steps := [.h .alice, .cnot .alice, .x .bob, .z .alice, .expose .alice] }
```

- `singletRecipe` supplies the singlet and two settings for each party.
- `.product false false` means |00>. Amplitudes use order 00, 01, 10, 11.
- `H(Alice)` creates a superposition. `CNOT(Alice)` uses Alice as control and
  Bob as target, producing |Phi+>. X(Bob), then Z(Alice), produce the singlet.
- Operations execute left to right. They prepare the state **before** Alice and
  Bob choose their separated measurements. A CNOT is not a spacelike operation.
- `expose Alice` applies the selected law's noise to Alice. No exposure means no
  law-dependent noise. Fixed gates and measurements are the same in every row.

## Change the law

`Law.dephasing 1 0 8` means Alice p=1/8 and Bob p=0. The arguments are Alice's
numerator, Bob's numerator, and a shared positive denominator. Invalid rates or
zero denominators are rejected. `Law.ideal` gives p=0 on both wires.

The channel is **(1-p/2)ρ + (p/2)ZρZ** on the exposed wire. Thus p=1 means complete
Z dephasing, not a deterministic phase flip. Each exposure applies this channel
again. Two p=1/2 exposures give effective p=3/4; probabilities are not added.

For the starter's singlet and settings:

| Alice p | CHSH | Comparison to Bell-local ceiling 2 |
|---|---:|---|
| 0 | 1502/625 = 2.4032 | Above |
| 1/8 | 1358/625 = 2.1728 | Above |
| 1/4 | 1214/625 = 1.9424 | Below |
| 1 | 14/25 = 0.56 | Below |

A score at or below 2 does **not** establish locality. Above 2 excludes the
existing Bell-local class for this mathematical behavior. These are model
predictions, not new laboratory observations or a choice of which assumption fails.

## Change the measurements

Each party has `first` (setting 0) and `second` (setting 1). For example:

```lean
def differentMeasurements : Recipe :=
  { direct with alice := { first := .z, second := .x } }
```

`Basis.of c s` selects real orthogonal columns (c,s) and (-s,c), each normalized
by sqrt(c²+s²). Supply any nonzero rational pair; `(0,0)` is rejected. `.z` is
`(1,0)` and `.x` is `(1,1)`. Outcome `false` is the first column (+1), `true` the
second (-1). `(0,1)` reverses the Z outcome labels and changes the signed CHSH
score. The statistic is **E00 + E01 + E10 − E11**; it is not an absolute value.

For a custom pure state use `.custom (Pure.of 1 2 3 4)`. The four entries are
relative real amplitudes, normalized automatically. The all-zero vector is
rejected. Available gates are H, X, Z on either wire, directed CNOT, and SWAP.
For fixed noise independent of the law use
`.dephase .alice (OntologySeparation.Recipes.Rate.fraction 1 2)`.

## Optional assertions and access to probabilities

```lean
example : chsh Law.ideal singletRecipe = 1502/625 := by two_qubit_check

example : ¬ OntologySeparation.Bell.localTheory (interpret Law.ideal singletRecipe) := by
  apply excludes_local
  two_qubit_check
```

`probability law recipe (x,y) (a,b)` returns an exact rational joint probability.
`interpret law recipe` exposes the normalized real-valued behavior.
`chsh_correct` connects the evaluator to the existing Bell observable.
`no_signaling_alice` and `no_signaling_bob` hold for all supported recipes,
not merely the starter. Labels are generated from the same evaluated inputs.

## Scope

This backend supports **two qubits, real amplitudes, rational input directions,
local projective measurements, and convex noise mixtures**. It does not support
arbitrary complex gates, additional wires, adaptive measurements, postselection,
or full Local Friendliness friend records. Mixture trees grow with noise steps;
keep experiments small. Lean verifies the model and its predictions; judging
whether that model describes the intended physics remains scientific work.

[Design and extension boundary](design/TWO_QUBIT_RECIPES.md) ·
[General law-package interface](ADD_A_SCENARIO.md)
