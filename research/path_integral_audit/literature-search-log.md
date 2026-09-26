# Literature and source checks

Run date: 2026-09-26 UTC / 2026-09-25 America/New_York. This records a focused audit, not an exhaustive systematic review of quantum foundations. Primary papers and author data determine technical claims. Search snippets and press coverage were discovery aids, not evidence of literal paths.

## Checkpoint 1 — identity, versions and access

Questions: Which paper and data version are being audited? Can all claimed inputs be obtained?

Queries: `"aeh1011" arxiv supplement`; `"Direct experimental test of Feynman" propagator criticism`; `"Direct experimental test of Feynman" "supplementary"`. Both available search engines were used after sparse/irrelevant results. Direct primary retrieval then resolved the paper and supplement.

Read: Wen 2026 main text (PMC HTML and Europe PMC XML), Dryad landing README, dataset/version/file APIs. Cross-check: DOI 10.1126/sciadv.aeh1011; Dryad DOI 10.5061/dryad.x0k6djj14, version 3 / 450489, 19 listed files. Main paper published August 2026; Dryad publication date June 30, 2026. These dates are not evidence of a problem.

Access record: publisher supplement returned 403; PMC binary returned an HTML challenge; NCBI OA service returned 404. The Europe PMC public supplementaryFiles API returned a valid ZIP with a 20-page supplement. All Dryad API file downloads returned 401; all public individual file links returned 403; the page's public archive-information endpoint also returned 403. No credentials or access-control workarounds used. Q01 remains blocked; Q02 resolved.

## Checkpoint 2 — measurement derivation and predecessors

Queries: `"Measuring the quantum propagator" "least action" photon`; `"Demonstration of the quantum principle of least action with single photons"` (publisher-targeted); `"Weak values from path integrals" Matzkin`.

Primary sources:

- Wen et al., Nature Photonics 17, 717–722 (2023), [DOI](https://doi.org/10.1038/s41566-023-01212-1), [author manuscript](https://arxiv.org/html/2305.19815v1). Read measurement derivation and paraxial identification around Eqs.1–3. It supplies the experimental lineage of propagator inference, not independent evidence that all inferred histories are actual trajectories.
- A. Matzkin, Physical Review Research 2, 032048(R) (2020), [DOI](https://doi.org/10.1103/PhysRevResearch.2.032048), [manuscript](https://arxiv.org/abs/2002.00832). Read primary abstract and method description: propagators can be inferred through weak measurement relations. Do not equate inferred complex quantities with ordinary per-photon path probabilities.
- Wen 2026 Supplement Sections 6–8, read fully for signal differences, product reconstruction and simulated noise.

Consequences: retain an explicit measurement-model boundary; inspect conditioning and reference factors; do not dismiss the independent endpoint comparison as wholly circular. Questions Q03/Q08/Q15.

## Checkpoint 3 — data sufficiency, noise and numerical sensitivities

Queries: `"Wen" "propagator" "0.0518"`; `"aeh1011" "data" "code"`; `site.datadryad.org "x0k6djj14" download`; `site.zenodo.org "Direct experimental test" "Feynman"`. These yielded no additional usable public raw-tensor/code source. This is a search outcome, not proof that none exists.

Read: Dryad complete rendered README and supplementary captions S1–S4. Supplement Section 7 fixes noise magnitudes σα=0.0518 and σβ=0.0459π but does not specify an exact seed or empirical covariance matrix. Main Results identifies the 4.45% comparison and path-space fidelity definitions. Inspected MathML m136 and m203 to avoid plain-text fraction/square-root errors.

Consequences: full path enumeration uses shared K entries; resample at acquisition level. Synthetic tests check transfer/path algebra, coordinate sensitivity, omitted action-range tails and noise scale. They remain separate from observed data. Q05/Q06/Q09–Q12/Q15/Q18 updated. Missing spreadsheets prevent the empirical checkpoint from closing.

## Checkpoint 4 — alternatives and scope of ontological claims

Queries: `"Space-Time Approach to Non-Relativistic Quantum Mechanics"`; `"Anomalous Weak Values Are Proofs of Contextuality"`; `"Anomalous weak values and contextuality" "operational constraints"`; targeted search for Wen propagators/classical alternatives. The latter returned mostly irrelevant listings, not a decisive critique.

Primary sources:

- R. P. Feynman, Reviews of Modern Physics 20, 367 (1948), [DOI](https://doi.org/10.1103/RevModPhys.20.367), [Caltech record](https://authors.library.caltech.edu/records/9h858-5hv71). Primary abstract explicitly identifies mathematical equivalence to the familiar formulation. Our finite composition identity is derived independently in the audit.
- M. F. Pusey, Physical Review Letters 113, 200401 (2014), [manuscript](https://arxiv.org/abs/1409.1535). Read theorem scope from primary abstract: sufficiently weak anomalous values can witness contextuality under required conditions. This is not a theorem that every anomalous-looking trajectory is a real superluminal history.
- R. Kunjwal, M. Lostaglio, M. F. Pusey, Physical Review A 100, 042116 (2019), [DOI](https://doi.org/10.1103/PhysRevA.100.042116), [manuscript](https://arxiv.org/abs/1812.06940). Read abstract and primary repository description for noise robustness and indispensable operational constraints. Detailed inequality implementation belongs to work package 2; it has not been applied to Wen data here.

Consequences: explicit incoherent class plus a matching enlarged response class; no claim of excluding every definite-history interpretation. Lean encodes access-relative distinctions. A future contextuality experiment must measure disturbance/operational constraints and account for finite noise rather than merely display a reconstructed phase or unusual weak value.

## Checkpoint 5 — corrections, adverse evidence and delivery review

Queries: `"aeh1011" "correction"` (365-day filter); `"aeh1011" correction comment`; `Wen Tian Wang Feynman path integral aeh1011 correction erratum comment` restricted to publisher/arXiv/PubMed and the last 60 days. Search engine 1 sometimes rewrote these into generic queries; irrelevant results were rejected. Search engine 2 also failed to provide a substantive correction record.

Direct primary metadata: [Crossref record](https://api.crossref.org/works/10.1126/sciadv.aeh1011) retrieved and preserved locally. `relation` is empty and no `update-to`/`updated-by` fields were supplied. This does not establish that no correction or criticism exists. Publisher access remains limited; refresh before any strong empirical conclusion.

Adverse checks: retained the 94.9/94.4 discrepancy, fidelity normalization question, finite-window bridge, phase-bin convention and incomplete raw-data evidence. Rejected the apparent missing trace-distance square root after checking MathML. A separate analytical full-Gaussian calculation raises a question about the numerical bound under that domain assumption (Q19); it was cross-checked by Gaussian quadrature rather than presented as an established author error. Verified that the formal countermodel is a context-dependent response table, not a complete trajectory theory. No evidence found here supports an FTL or backward-time intervention claim.

## Checkpoint 6 — physical correspondence and a concrete follow-up

Questions: Does the finite window implement the same propagation as the observed endpoint experiment? What is a useful intervention with an explicit null class? Which contextuality theorem is appropriate for a finite pointer?

Searches performed: `"propagator" "tomography" "finite aperture" photons`; the titles of the Lundeen direct-wavefunction and Magaña-Loaiza looped-trajectory papers; `single photon path interference local phase shift weak measurement phase shifter contextuality experiment`; `Kunjwal Lostaglio Pusey anomalous weak values contextuality noise 2019 operational equivalences`; `"single photon" "phase" Grangier Roger Aspect 1986 interference experiment`; `"Experimental demonstration" "contextuality" "anomalous weak values" Piacentini`. Both engines were used. Some results were unrelated names or secondary summaries; these were not technical evidence. Search coverage does not justify an exhaustive novelty claim.

Primary review deepened beyond the earlier abstract pass: downloaded Matzkin v2 and Lundeen author PDFs, Kunjwal full HTML and the looped-trajectory paper's primary XML. Read Matzkin's main weak-probe derivation/discussion; Lundeen's main reconstruction/ensemble description; the looped paper's theory/results/methods; Kunjwal Sections II.3–II.6, III.2 and IV. `literature-comparison.md` records review depth, exact identifiers and remaining full-proof/supplement obligations. Downloaded originals are hashed in provenance, not redistributed.

Consequences: derive a projection-window error bound and a leave-and-return counterexample; specify a phase intervention without changing the selected aperture; retain loss and joint probabilities; identify the finite-pointer contextuality theorem and its missing equivalences for package 2. Do not mistake the older experimental contextuality claim for verification of all later theorem assumptions. Q18/Q20 updated; Q21–Q24 track design, calibration, stronger witness and novelty/power dependencies. `intervention_checks.py` checks the independent density-matrix expansion and loss/window counterexamples, not observed data.

The Grangier and Piacentini searches identified useful precedents but were not full experimental-paper reviews in this checkpoint. Their full protocols and supplements should be assessed if selected as the apparatus/witness baseline. This is an explicit review boundary, not a closed question about all existing experiments.

## Refresh triggers

Repeat targeted searches and source-version checks when raw files arrive, an author clarification/correction appears, a physical model changes, or work package 2 proposes a concrete inequality. Record the actual new evidence and revisit every dependent numerical/proof/prose claim. Do not interpret repeated empty searches as closure of a scientific question.
