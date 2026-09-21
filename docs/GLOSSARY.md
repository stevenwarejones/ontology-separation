# Vocabulary for physicists

| Library term | Physical reading |
|---|---|
| Model / law | Mathematical specification of a possible system, including parameters and dynamics. |
| Recipe / protocol | Preparation, ordered interventions, and measurement performed on that system. |
| Behavior | A normalized finite probability table for the available settings and outcomes. |
| Observable / score | A number extracted from that table, such as a probability or CHSH score. |
| Scenario | The interface that connects models and protocols to actual behaviors and a score. |
| Interpreter | The function that turns a model and protocol into their predicted behavior. |
| Prediction | A value with a proof that it equals the score of that behavior. |
| Theory | A class of allowed behaviors, specified by a predicate. |
| Vocabulary | The exact physical predicates assigned to the four assumption slots. |
| Stance | Require a predicate, reject it (require its negation), or leave it unconstrained. |
| Profile | Four stances interpreted in one particular vocabulary. |
| Bridge | A proof that models satisfying that profile produce behaviors in a target theory. |
| Bound | A proved ceiling for every behavior in a class; possibly vacuous if the class is empty. |
| Witness | An actual mathematical member of the specified class; proves nonemptiness. |
| Realized profile bound | A bound plus a model and proof that it satisfies the same profile. Does not imply saturation. |
| Separation | A bound for one class and a witness that violates it. |
| Adapter | A mapping between representations with proofs preserving the relevant probabilities. |

## Unspecified is not false

**`.unspecified` ≠ `.reject`. Omitting a field imposes no constraint.**

For a law P, `.require` means P, `.reject` means ¬P, and `.unspecified` means True.
Use `AssumptionProfile.select` to choose all four stances explicitly, or
`AssumptionProfile.requireAll` / `.unconstrained` when that is your intent.
None of these constructors proves the resulting profile is realizable.

For physics, prefer vocabulary-specific packages such as
`OperationalBell.screeningOffProfile`, `OperationalBell.jointProfile`, and
`FriendRecords.profile`. A generic constructor called “Bell local” would be
misleading when applied to a vocabulary with different predicates.

## Review a new vocabulary

Before applying a theorem to a new set of assumptions:

1. State the equation or predicate for each slot, including all conditioning variables.
2. Check the field assignment against that equation, not the philosophical label.
3. Identify which variables an intervention may change and which remain fixed.
4. Prove the bridge for that vocabulary and predictor.
5. If claiming a possible world, supply a satisfying model; if claiming an exclusion,
   state which conjunction of assumptions is excluded and by what evidence.

Lean can check the bridge you wrote. It cannot determine whether you accidentally
called parameter independence “realism” or omitted a relevant experimental effect.
