# Can a remote intervention change a locally available record?

The checked development isolates a modest causal claim: a normalized sender
operation, independent preparation and a receiver with no setting input give
zero unconditional influence. It also checks a separate quantum algebra identity,
counterexamples, spacetime uncertainty arithmetic and calibration/interval
transport. These are formal verifications of established reasoning, not new
physics or an experimental exclusion of hidden trajectories.

Read the [generated theorem report](../examples/spacetime-influence.html) or
run the [editable source](../examples/SpacetimeInfluenceStudy.lean). The detailed
[prospective optical study](https://github.com/stevenwarejones/path-reality-tests/tree/d52f46faac61913cc4595fd471f0046d703f1193/studies/spacetime-causal-influence)
contains the protocol comparison, literature record, statistical derivation,
synthetic power calculations and unresolved apparatus requirements. This immutable
commit link survives branch deletion; neither repository needs the other to build.

## Definitions and mathematical result

For settings x∈{0,1} and complete receiver outcomes b,

\[
\Delta=\tfrac12\sum_b|P(b\mid do(x=1))-P(b\mid do(x=0))|.
\]

The finite `Model Λ A B` has a setting-independent preparation distribution μ,
arbitrary normalized sender channels Kₓ, and fixed receiver channel R. Its
normalized joint behavior is ∑λ μ(λ)Kₓ(a|λ)R(b|λ). `Model.marginal_formula`
sums over all a and cancels Kₓ by normalization. `Model.no_influence` derives
Δ=0. Loss, invalid outcomes and missing detection must be represented in the
complete response; dropping a setting-dependent subset changes the theorem.

The theorem is a sufficient classical causal structure. It is not a complete
characterization of every quantum joint distribution. Separately,
`local_operation_fixes_effect` proves in any star ring that

\[
\sum_j K_j^\dagger K_j=I,\quad [E,K_j]=0\quad\Longrightarrow\quad
\sum_j K_j^\dagger E K_j=E.
\]

This is the nonselective quantum-operation identity, valid before any state
expectation and therefore not restricted to uncorrelated states. Its use for a
physical channel requires the usual positivity/state assumptions; its use for
a spacelike operation additionally requires physical localization and
commutation. Lean does not derive continuum QFT microcausality here.
[Tjoa, arXiv:2206.02316v4](https://arxiv.org/html/2206.02316v4) gives a
nonperturbative detector/QFT treatment; [Martín-Martínez,
arXiv:1509.07864v2](https://arxiv.org/abs/1509.07864v2) analyzes localization,
cutoff and rotating-wave hazards. These results do not calibrate an actual lab.

`influence` has exactly two settings; an extension to more settings would need
a specified pair or maximum over setting pairs. `binary_influence` identifies binary TV with the absolute selected-outcome gap.
The normalized `alternative g` has probabilities (1±g)/2 and influence exactly
g for 0≤g≤1. `alternative_excluded` excludes every finite `Model` at g>0,
including the explicit `sharedBit` witness. It is an operational alternative
table, not a relativistic field theory. Boundary g=0 and g=1 are checked.

## Assumptions exposed by examples

`sharedBit_correlated` has perfectly correlated sender/receiver bits but Δ=0.
`receiver_access_equivalent` proves that receiver-only access cannot distinguish
that model from the specified model with an independent sender bit. This toy
equivalence does not extend to all hidden-path interpretations.

Three separate structures relax one premise at a time. Their field types retain
normalization, and `countermodel_fields` checks the unchanged concrete fields:

| Model | Relaxed premise | Fields retained | Checked gap |
|---|---|---|---|
| `dependentPreparation : PreparationDependentModel` | Preparation may depend on x | Original normalized sender and fixed receiver; complete summation | `dependentPreparation_gap = 1` |
| `dependentReceiver : ReceiverDependentModel` | Receiver may read x | Original fair preparation and normalized sender; complete summation | `dependentReceiver_gap = 1` |
| `selectedSharedBit : SelectedModel` | Sender-dependent discarding permitted | Entire underlying `sharedBit` causal model unchanged | `postselection_counterexample`: unconditional influence 0, selected influence 1 |

The selection event is explicitly `a=x`. `SelectedModel.weight` sums the
accepted joint probabilities, and `acceptance` is their total. A strictly
positive acceptance premise gives a normalized conditional `observed` behavior.
`selectedSharedBit_acceptance` proves acceptance 1/2 for **each** setting; the
postselection theorem proves fair unconditional receiver marginals and computes
the selected TV using `influence`. No selected probability is supplied by hand.
The g-family remains a normalized operational table, not a premise-isolating
model or a dynamical theory. The empirical
guide adds explicit wire, timestamp, predictable-setting and overwritten-record
countermodels. Observational conditioning is identified with do-interventions
only under the randomized-assignment and consistency premises.

## Geometry and probability allowances

For uncertain time supports A=[a₀,a₁], B=[b₀,b₁] and conservative spatial
separation d_min, `spacelike_of_budget` proves every event pair is spacelike if
c max(b₁−a₀,a₁−b₀)<d_min. Euclidean support radii and survey errors supply
d_min externally. The earliest possible RNG/driver leakage belongs in A.
Vacuum c, not fiber delay or group velocity, is the relevant speed. The theorem
checks the implication for supplied bounds, not that those bounds are true.
`earlier_record` separately checks strict record-before-choice interval order.

`coupling_gap` bounds a binary probability discrepancy by record-mismatch
probability. `three_event_bound` bounds any covered failure by the sum of
timing/leakage/record failure probabilities without independence. Two calibrated
couplings around one ideal null law yield |p₁−p₀|≤e₀+e₁ by `calibrated_gap`.
The sharper max(e₀,e₁) in `contamination_gap` requires the same *conditional
good distribution* in both settings; a mere bad-trial fraction is insufficient.
Neither a timing error in seconds nor a Gaussian amplitude tail is automatically
a probability allowance. A detector/coupling calibration is still needed.

## Finite statistics: what is and is not checked

`difference_interval`, `absolute_interval_upper` and `strict_interval_exclusion`
transport simultaneous probability intervals into rejection and an absolute
upper limit. `rejection_risk` proves the finite union bound for confidence and
calibration failures. `fair_score_mean` and `biased_score_mean` check the
randomized-score expectation arithmetic. These and `calibrated_gap` are small
algebraic helper lemmas, not independent scientific results; exported-claim counts
are a coverage inventory, not a measure of novelty. All new roots are in
[Tests/Audit.lean](../Tests/Audit.lean).

The empirical study derives a fixed-horizon conditional Hoeffding score interval
that allows device memory and a separate IID Clopper–Pearson difference interval.
For the memory analysis, calibration must bound the conditional-history
allowances or their realized average; pooled IID controls alone do not do so.
Those exponential/binomial coverage derivations are **not formalized in Lean**.
The score estimates average signed conditional influence; binary TV needs a
constant effect. A null upper limit does not exclude effects whose signs cancel
over histories. No optional stopping or general multinomial-TV upper bound is
asserted. Coarsening a complete multi-category record to a bit retains trials
but can hide differences between the merged categories.

The closest reviewed operational statistical comparison is [Albanese (2026)](https://doi.org/10.3390/physics8020052),
with a binary channel and corrected difference interval. This development uses
explicit finite-channel/algebraic proofs, uncertainty/coupling budgets and a
fixed-horizon memory analysis. It does not claim those statistical techniques
are new or that the optical protocol improves any published measured bound.

## Verification and limitations

Sources are [SpacetimeInfluence](../OntologySeparation/Experiments/SpacetimeInfluence.lean)
and [SpacetimeInfluenceBounds](../OntologySeparation/Experiments/SpacetimeInfluenceBounds.lean);
[tests](../Tests/SpacetimeInfluence.lean) include nonzero, zero, maximal-gap,
strict-boundary and geometry examples. Boundary regressions apply the actual
`strict_interval_exclusion` and `spacelike_of_budget` results; the explicit
lightlike endpoint also disproves a non-strict replacement of the geometry condition. Run `sh scripts/check.sh` to rebuild
the complete library, tests, axiom snapshot and HTML from source. Only the usual
`propext`, `Classical.choice` and `Quot.sound` axioms are accepted.

No apparatus measurements enter these files. There is no bridge from a hidden
finite-speed influence parameter elsewhere in the repository to this operational
effect, and no changes to that work are required. Apparatus calibration and the
continuum-to-real-device bridge remain external requirements, recorded in the
companion question register.
