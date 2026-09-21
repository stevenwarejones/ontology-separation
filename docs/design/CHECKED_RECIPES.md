# Checked experiment recipes

## Adoption contract

For the supported real-qubit fragment, adopters supply physical exposure rates and
explicit recipes (preparation, ordered operations, readout). They do not supply a
second prediction formula or a reconciliation proof. A general Lean theorem connects
an exact rational evaluator to the existing normalized real-qubit semantics for every
supported recipe and law. Numeric evaluation never replaces that theorem.

Recipes are data independent of models. Only the exposure operation consults the
model's dephasing rate. Preparation, fixed gates, fixed dephasing, and readout cannot
silently change between model rows. This restriction belongs to this backend; the
existing general Scenario API remains an explicit advanced escape hatch.

## Mistakes to prevent

- Invalid physical rates: constructors require kernel-checked [0,1] bounds, with
  default proof automation for concrete rational values.
- Swapped operations: lists execute in written order; order-sensitive tests cover
  Hadamard, phase flip, and dephasing.
- Stale labels: physical labels are generated from the rate and complete recipe.
- Wrong predictions: comparison construction supplies the evaluator's universal
  correctness proof; adopters cannot accidentally attach a handwritten table.
- Empty or ambiguous tables: nonempty selections are checked, duplicate generated
  labels are rejected before publication, and no cells silently disappear.
- Stale compiled imports: report commands use `lake lean`, which rebuilds imports,
  in the source file's nearest Lake project.
- Failed output: source files cannot be overwritten by reports; writes are atomic;
  failed checking leaves prior output intact and identifies it as potentially stale.

## Scope

This is a restricted rational real-qubit backend with exact arithmetic. It is not a
new no-go theorem, general quantum circuit language, or automatic interpretation of
ontology names. Physical adequacy of a chosen law and experiment remains a scientific
judgment. The report is an editable snapshot of checked source, not an authenticated
proof artifact or a statistical analysis of measured data.

## Adoption review decisions

This change also introduces `RealizedProfileBound`, which adds a satisfying model
to a conditional bound. It does not change `ProfileBound`: universal results over
possibly empty classes remain useful. Profile tables label their lack of a
per-row existence certificate rather than inferring one from a bound. The classical
Bell example supplies a real witness for its own screening-off profile.

Profiles gain explicit `select`, `requireAll`, and `unconstrained` constructors.
We retain named, vocabulary-specific Bell and friend-record profiles instead of
introducing a generic “Bell-local” constructor whose physical meaning would depend
on unrelated vocabulary slots. A glossary and equation checklist make this boundary
visible during extension work.

A hosted development environment is a separate infrastructure task, requiring a
clean-machine test of cache downloads, resource use and toolchain pinning. A larger
redesign of the four vocabulary slots is also deferred: it needs a migration plan
for existing Bell/LF models. Neither is necessary to use the recipe API.
