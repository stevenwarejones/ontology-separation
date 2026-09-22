# Exact separator search

This layer changes the workflow from "check the experiment I already chose" to
"search this explicit finite candidate family for an experiment that separates
the models."

An adopter supplies:

- two exact models;
- a nonempty base protocol family;
- a nonempty candidate protocol family.

The framework first certifies the base family. If the models already separate
there, search reports that fact rather than pretending an additional capability
was necessary.

Only after base agreement is proved does it scan the candidate family. The
result is one of:

- an A-over-B separator;
- a B-over-A separator;
- checked agreement across the entire supplied candidate family.

Every branch carries the existing proof-bearing agreement/separator objects.
Candidate traversal order chooses which valid separator is returned first. It
does not change the mathematical conclusion.

## Scope

A no-candidate result means **no separator in the supplied, completely covered
finite candidate family**. It is not a theorem that no experiment exists.

This is also not yet a minimality theorem. Finding one separator does not prove
that its access requirements are weaker than every alternative. The next stage
can place candidate access families in an explicit finite order and certify
minimality by checking all weaker families.

The search remains an exact finite engine. Continuous parameter regions continue
to use the symbolic theorem path demonstrated by the partial-leakage study.


## Public report workflow

`SearchResult.report` converts every search branch into proof-linked structured
comparison reports. The base result is always present. Candidate evidence is
present only when the candidate family was actually scanned. A found result
therefore publishes both the checked base agreement and the checked candidate
separator, including reverse orientation.

`examples/SeparatorSearchStudy.lean` uses only the public
`OntologySeparation.Study` import. Its candidate list is intentionally
multi-element: calibration is visited first and agrees; the later coherence
protocol separates. The downstream adoption gate requires that later witness
and its exact `1/4` gap to survive export and HTML rendering.

The `#export_search` command audits the report dependencies with the same axiom
policy as the existing claim/comparison exporters.
