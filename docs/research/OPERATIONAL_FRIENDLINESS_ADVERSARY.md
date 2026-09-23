# Operational Friendliness adversary benchmark

This increment validates the structured-adversary workflow against the logical
shape used by the 2025 Operational/Noncontextual Friendliness result.

The full paper uses an extended Wigner-friend prepare-and-measure experiment.
This benchmark isolates its CHSH/Fine-style hinge:

- **absolute-event table**: the latent observed events admit one global
  Fine/CHSH-compatible table;
- **operational-agency lift**: the public operational table is the same table;
- **target**: the exact rational singlet behavior already checked by this repo.

The two assumptions exclude the target. Deleting either one has an explicit
target-realizing model:

1. without the absolute-event table, the latent table can itself be the
   nonlocal singlet table while the operational lift remains exact;
2. without the lift, a perfectly local latent table can coexist with the
   public singlet table.

This is a **reproduction-level benchmark**, not a formalization of every premise
or circuit in Walleghem--Catani. Its purpose is to prove that the adversary API
can distinguish "both assumptions are used" from "both assumptions are actually
premise-by-premise necessary" before applying the workflow to candidate new
friend scenarios.
