# Baumann–Brukner Sec. 3: formalized reproduction

This is a formalized reproduction of Baumann & Brukner, *Quantum* **8**, 1481
(2024), Sec. 3. It carries no novelty claim and has not been reviewed by a human
domain expert.

## Physical scope

The logical friend/system branch and Bob are two qubits. The source is
`(|0,1⟩ + |1,0⟩)/√2`. Bob chooses between explicit computational and rotated
projective measurements. Wigner's unread measurement acts by projective
pinching on the conditional friend blocks. The model does not represent
conscious awareness or an experimental implementation.

## Proof chain

- [BaumannBruknerQITSource.lean](../../OntologySeparation/Experiments/BaumannBruknerQITSource.lean)
  derives `computational_conditional`, `rotated_conditional`,
  `computational_branch_data`, and `rotated_branch_data` from the source and
  Bob's projectors.
- [BaumannBruknerQITWigner.lean](../../OntologySeparation/Experiments/BaumannBruknerQITWigner.lean)
  derives `computational_after_qit` and `rotated_after_qit` using the QIT
  `ProjectiveMeasurement.pinchingMap`.
- [BaumannBruknerProtocol.lean](../../OntologySeparation/Experiments/BaumannBruknerProtocol.lean)
  proves `exact_setting_dependence` and `flip_rates_differ` for the reconstructed
  flip rates `1/4` and `1/4 + √2/2`.
- [MemoryAwareness.lean](../../OntologySeparation/Experiments/MemoryAwareness.lean)
  separately states the logical incompatibility of remote-dependent memory
  change, faithful awareness, and no-signaling awareness, with deletion
  countermodels. The physical protocol supplies a setting-dependent example;
  identification of these mathematical quantities with awareness is an
  interpretive assumption.

The transcribed Appendix-B formula module `MemoryAwarenessWitness.lean` is not
part of this reproduction. The checked tables arise from the explicit source
and measurement dynamics above. See [the axiom audit](../AXIOM_AUDIT.txt) for
proof dependencies and run `sh scripts/check.sh` for the complete check.
