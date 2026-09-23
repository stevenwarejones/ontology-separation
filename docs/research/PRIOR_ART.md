# Prior art and reuse decisions

Assessment date: 2026-09-22. This is a bounded source review, not a priority
certificate or an independent audit of other projects' proofs.

## Sources checked

| Primary source | What it establishes for planning |
|---|---|
| [Zhao and Yu, Formalizing CHSH Rigidity in Lean 4](https://arxiv.org/abs/2604.03884) | The paper reports a Lean rigidity formalization and a gap found in a prior argument. Bell/CHSH formalization is established territory; we do not claim a first. |
| [Echenim and Mhalla, Quantum projective measurements and the CHSH inequality in Isabelle/HOL](https://arxiv.org/abs/2103.08535) | Prior machine-checked CHSH work also exists outside Lean, including arbitrary probability spaces. |
| [QuAIR/Lean-QIT](https://github.com/QuAIR/Lean-QIT) | This is this repository's actual dependency, pinned at `c1d59b133b56e3d79efb11ee46a728d290f761f5`. Upstream quantum infrastructure should be reused before extending local machinery. |
| [A Formalization of the Generalized Quantum Stein's Lemma in Lean](https://arxiv.org/html/2510.08672v1) | The paper describes Lean-QuantumInfo alongside a substantial quantum theorem formalization. Do not conflate this name with QuAIR/Lean-QIT or infer API compatibility. |
| [Principia](https://github.com/AshishKumar4/Principia) | Its README describes an AI physics workflow, explicit assumptions, non-vacuity checks, axiom audits, and experimental evidence. Honest output contracts and physics agents cannot be claimed as exclusive to our project. These are project descriptions, not independently verified implementation results. |
| [Bong et al., A strong no-go theorem on the Wigner's friend paradox](https://arxiv.org/html/1907.05607v4) | The scientific target must be identified by exact assumptions, setting scenario, inequality and quantum construction; an internal interface equivalence alone is not a full paper formalization. |

The supplied Lean-Quantum paper (arXiv:2607.05492) and AxQM paper
(arXiv:2609.05157) remain leads to verify: their pages were not retrievable in
this review. Retrieval failure says nothing about whether those works exist.
The program already includes verified precedents in quantum autoformalization
(MerLean), automated experiment design (Melvin), and Bell statistics.

## Consequences for the program

1. Treat Bell and known LF inequalities as reproductions. A formalization can
   still be valuable without a first-in-the-world claim. Reuse compatible prior
   proofs rather than duplicate them; reuse is not a logical prerequisite for
   priority, and compatibility must be assessed at the pinned versions.
2. Keep LF as a promising flagship, but do not advertise a first complete LF
   formalization. The sources inspected here do not establish the absence of
   other work. Before any priority claim, search theorem names and variants
   (Local Friendliness, Bong, Wigner's friend), code repositories and proof
   assistant archives; specify exactly what our proof covers and record the date.
   External maintainer and foundations-expert feedback would help, but cannot
   prove absence either. No outreach has been sent or authorized by this plan.
3. Compare competing systems by tested capabilities before claiming a distinctive
   advantage. Our intended contribution is an accessible, proof-bearing workflow
   for access-dependent distinctions between operational physical assumptions,
   with precise scope, constructive witnesses and experimental consequences.
4. Make a dependency-reuse review a gate for infrastructure changes, as specified
   in [the program](PROGRAM.md). Neither a paper abstract nor a library name is
   evidence that a needed declaration exists, compiles with our dependencies, or
   has the required assumptions.
5. Continue the concrete LF paper-to-code correspondence now. Priority research
   and external validation run alongside useful verification work; they do not
   justify delaying the known baseline or promising a novel physics result.
