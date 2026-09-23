# Timelike Friendliness: operational minimal core in 2222

This increment asks a narrower, adversarial question than the paper-level theorem:

> Which operational consequences of the timelike assumptions are actually needed
> to force the CHSH bound in the binary 2222 scenario?

The common model class allows:

- a setting-dependent finite distribution over a two-state pseudo-event variable;
- Alice's conditional binary expectation to depend on both settings;
- Bob's conditional binary expectation to depend on both settings.

Three laws are then imposed:

1. **stable pseudo-events** — the hidden/pseudo-event distribution is independent
   of the settings;
2. **Alice screening** — Alice's response is independent of Bob's setting;
3. **Bob screening** — Bob's response is independent of Alice's setting.

Together they imply CHSH <= 2.

The key structured-adversary result is stronger than that bound: each law is
individually necessary **inside this exact model class**.  Removing any one while
keeping the other two admits an explicit score-4 countermodel.

- Without stable pseudo-events, the setting can select different local hidden
  strategies.
- Without Alice screening, Alice can encode the exceptional (1,1) context.
- Without Bob screening, Bob can do the mirror image.

Thus the three operational consequences form a deletion-minimal core for
excluding the algebraic CHSH target in this model.

## Relation to Mukherjee--Hance

This does **not** identify these three laws one-to-one with AOE, ATS, NRC and SPE.
The paper derives closely related stability and screening statements from those
assumptions. The next semantic bridge must prove exactly which combinations of
AOE/ATS/NRC/SPE imply each operational law.

That distinction is important: the paper already shows full AOE can be weakened,
and it highlights the absoluteness of pseudo-events as crucial. We therefore use
the operational minimal core as the target of the paper-to-code bridge rather
than assuming the four named premises are themselves minimal.

## Research consequence

The 2222 search is now structurally exhausted at this level: if all three
operational laws hold, CHSH is classical; remove any one and the algebraic maximum
is possible.  A genuinely new result therefore needs either:

- a weaker operational premise that still restores a nontrivial bound, or
- a scenario beyond 2222 where the timelike constraints differ from ordinary
  generalized-noncontextuality constraints.
