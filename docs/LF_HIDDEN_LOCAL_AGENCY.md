# Unread friend records as a relaxation of Local Agency

## Status

This PR is a **documented negative result**.

Finite-speed hidden influences motivated the question, but the quantity studied
here is more cleanly described as a relaxation of **Local Agency** in the
standard Local Friendliness (LF) experiment.  It should not be presented as a
new finite-speed theorem or as an LF analogue of Bancal et al.

The trusted Lean result is deliberately modest:

- AOE is represented by one joint table over Charlie, Debbie, Alice and Bob.
- Exact friend readout and setting-independent records are explicit.
- Conditional locality at fixed friend records is the existing
  `LFJoint.Local` law.
- The public quantum LF target is exactly no-signaling.
- The target nevertheless has no joint extension satisfying the full LF law.

The extra LP work asks what changes when the friend records remain absolute but
are **unread / reversible** from the public late-party perspective.

## Main finding: unread records weaken the Bancal-style constraints

This is the central result of the exploratory line.

Using the same forced-signaling score LP, compare two treatments of the early
variables:

| treatment of early variables | zero-TV score ceiling | minimum TV at score 8 |
| --- | ---: | ---: |
| early outcomes operationally observed | 6 | 1/4 |
| absolute friend records, unread after reversal, exact readout enforced | 22/3 | 1/8 |

So unread friend records make the hidden-influence constraints **strictly
weaker**:

```
zero-signal score:  6   -> 22/3
score-8 TV cost:    1/4 -> 1/8
```

If exact friend readout is removed as well, score 8 is achievable at zero TV.
Therefore the residual `1/8` comes from the combination of unread records and
friend/readout consistency; it is not produced merely by marginalizing the
early variables.

This explains why the original Bancal intuition does not transfer directly to
the standard LF geometry.  In Bancal's ordinary four-party setup the early
outcomes remain part of the operational recipient distributions.  In LF, the
friends' outcomes can be absolute while later being coherently reversed and
unread.  Marginalizing those records removes constraints that were essential to
the stronger `1/4` tradeoff.

These LP values are reproducible from
`research/lf_hidden_local_agency.py`.  They remain exploratory numerical
results rather than Lean theorems.

## Full LF table: the rational-angle value is not the headline

Matching all 36 public probabilities of the repository's current rational
`RealQuantum.lfBehavior` gives a record-revealed TV value

```
63/625 = 0.1008.
```

That number is **not fundamental**.  It is an artifact of the repository's
convenient rational test angles and should not be promoted to a theorem.

Scanning the measurement angles instead gives a much stronger value.  A simple
pi/8-grid choice,

```
Alice: [0, -pi/4,  pi/4]
Bob:   [-3pi/8, pi/4, -pi/8]
```

gives

```
delta = (sqrt(2) - 1)/2
      ~= 0.2071067812.
```

The script reproduces this value numerically.  A broader angle search also
returns approximately the same optimum.

There are now three carefully separated statements:

1. **Explicit-angle theorem — Lean-certified.**  For the stated pi/8-grid
   singlet measurements, every AOE joint extension with exact readout and
   setting-independent friend records has at least one of the two certified
   record-revealed TVs at least `(sqrt(2)-1)/2`.
2. **Anchored-witness angle optimum — Lean-certified.**  The public part of the
   exact LP certificate is a CHSH-type witness
   `(E00 - E0y + Ex0 + Exy - 2)/4`.  An elementary Tsirelson proof in Lean
   shows that no real projective qubit measurement angles can make this witness
   exceed `(sqrt(2)-1)/2`, and the pi/8-grid bases attain equality.
3. **Global optimum of the full multi-comparison LP — numerical only.**  The
   exploratory angle search over the complete LP returns the same value, but the
   theorem in this follow-up does not identify every facet of that larger
   piecewise-linear optimization problem.

The arbitrary rational-angle value `63/625` is therefore not promoted to a
theorem.

## What the Lean code certifies

`OntologySeparation.Experiments.LFAgencyRelaxationDiagnostics` defines the
record-revealed quantities used above without assigning them any candidate
optimum:

- joint mass of the friend-record pair with Alice's late outcome;
- the analogous Bob quantity;
- total-variation distance under a remote-setting change;
- a uniform `RecordRevealedWithin` budget.

Lean proves these quantities are nonnegative and that exact conditional locality
forces every such TV to zero.

That is the correct trusted boundary for this PR.  The exploratory optimizer is
a discovery/reproducibility tool, not part of the kernel proof.

## Relation to earlier LF relaxation work

This study belongs with **relaxations of LF assumptions**, not with a new
finite-speed theorem.

Repository PR #29 already proves a sharp **readout-error** relaxation,

```
S <= 6 + 4 (delta_A + delta_B),
```

and explicitly notes the related prior-art bound in:

- George Moreno, Ranieri Nery, Cristhiano Duarte, and Rafael Chaves,
  *Events in quantum mechanics are maximally non-absolute*,
  Quantum 6, 785 (2022), arXiv:2112.11223.

Moreno et al. relax **Absoluteness of Observed Events** rather than the exact
record-revealed Local-Agency quantity studied here, so it is related but not
identical.

Cavalcanti and Wiseman,
*Implications of Local Friendliness violation for quantum causality*,
Entropy 23, 925 (2021), explicitly discuss the option of giving up or relaxing
Local Agency.

A focused literature search was then run specifically for relaxations of
Local Agency / parameter independence in extended Wigner-friend scenarios,
including searches combining those terms with total variation.

The closest matches found were:

- Moreno et al. quantify relaxations of **AOE** while retaining parameter
  independence; their Eq. (3) is the same fixed-record conditional-independence
  structure that this repository calls conditional Local Agency, but the
  relaxed quantity in that paper is disagreement with the friend records, not
  total-variation violation of parameter independence.
- Cavalcanti and Wiseman explicitly identify the relevant LF locality principle
  with parameter independence / Local Agency and discuss the conceptual option
  of giving it up, but do not introduce the record-revealed TV optimization used
  here.
- Later Wigner-friend/objectivity work located in the search likewise relaxes
  objectivity/readout assumptions rather than this exact TV measure of Local
  Agency.

No paper matching the exact optimization in this PR was found in that focused
search.  This is **not** a novelty claim: the search is finite and terminology
varies across the causal-inference and Wigner-friend literature.

The follow-up proof now kernel-checks the explicit-angle
`(sqrt(2)-1)/2` lower bound with exact radical arithmetic and separately proves
global optimality of the associated readout-anchored CHSH witness.  It does not
turn the broader numerical full-LP angle search into a theorem; that stronger
claim would require a complete characterization of the other active LP facets.

## Why this does not yield operational superluminal signaling

The public quantum LF behavior is no-signaling.

The positive TV discussed here appears only after retaining/revealing the
absolute friend records together with the receiving outcome.  Those records are
precisely the variables that may be erased or inaccessible in the Wigner
measurement branch.

Therefore a positive record-revealed TV is a quantitative failure of the
conditional Local-Agency law, **not** by itself an operational faster-than-light
signal.

That distinction is the reason this line does not reproduce Bancal's conclusion
inside the standard LF experiment.

## Track retired

The next step is **not** to add extra parties or engineer a larger Bancal-style
spacetime construction in this repository.

The exploratory question was whether the standard LF structure, together with
absolute-but-reversible friend records, naturally upgrades the forced-signaling
result.  It does not.  Unread records weaken the decisive constraints:

```
6 -> 22/3
1/4 -> 1/8
```

and the full public LF table remains exactly no-signaling.

That is enough to close this branch as a useful negative result.

The explicit-angle radical result and its anchored-witness angle optimum are
now formalized.  No additional Local-Agency branch is proposed here; the
remaining full-LP angle search is retained as exploratory evidence, and the
research program returns to forced-signaling.

## Reproducibility

Install the research extras and run the benchmark checker:

```bash
python -m pip install -e ".[research]"
python research/lf_hidden_local_agency.py --check
```

The main GitHub `verify` job runs this same `--check` command, so changes that
move any documented benchmark beyond tolerance fail CI.

It reproduces:

- observed outcomes: zero-TV ceiling `6`, score-8 TV `1/4`;
- unread reversible records with exact readout: zero-TV ceiling `22/3`,
  score-8 TV `1/8`;
- repository rational-angle full-table value `63/625`;
- explicit pi/8-grid angle value `(sqrt(2)-1)/2`.

Use `--search` for the additional numerical angle search.  That search is
evidence only; it is not a proof of global angle optimality.
