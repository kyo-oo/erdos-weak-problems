# GST × CM abelian geometry × NM: number-theoretic forcing research

**Date:** 2026-10-15
**Branch:** `mathbox/bd23-single-operator-charge-wedge`
**Attribution:** contributor remains anonymous; do not add a personal name.
**Primary target:** the authentic rational Hodge conjecture for arbitrary
smooth projective complex varieties, WITHOUT an Hodge-surjectivity, abstract
matrix unit, supplied basis preimage or full geometric cyclicity premise.

## Locked interpretation of the three proposed GST equations

The contributor's own clarification is that Equation (3), using the
zeta function together with CM on abelian geometry, is intended to work
with Number Manipulation (NM) to CONSTRUCT complex geometry. NM is not
just a real-variable simplification trick. The intended program is

```
complex multiplication in genuine abelian geometry
  + CM conjugate number field / character eigenvalue calculations
  + NM transformation of indexed zeta-style expressions
  + genuine nonzero arithmetic period and rational descent
  + actual cup / pullback / Gysin / pushforward correspondences
  => constructed native algebraic Hodge classes
  => cycle-class span in every rational Hodge direction.
```

A complete proof must establish EACH geometric and cohomological map
along this chain. A nonzero scalar/determinant for an arbitrary
matrix is not an algebraic-cycle realization.

The scalar part of corrected Equation (3) has
`x^n - y^(n+1)` in the denominator (n>=1).
When applying CM, `x,y` should be allowed to take values in a
quadratic imaginary number field, not restricted to REAL values.
The meaning of `n -> R`, `H × Q`, and a canonical s-dependent
geometric period remain untyped in the original formula. This
report does not fabricate them.

## Whole-branch inventory and exact import-graph audit

The existing repository script `scripts/audit_lean_dependency_graph.py`
has been executed by GitHub Actions with no local Lean installation.

**PASS: GitHub run 38677173614**
- 642 Lean files inspected programmatically at the expanded CM-NM revision (earlier baseline: 640).
- 600 active registered / entry roots; 601 root-reachable files.
- 0 missing local imports and 0 import cycles.
- 29 CM / zeta / NM / OpenAI / Hodge seed modules selected for graph
  analysis, with a 325-module import dependency closure.
- Full JSON provenance and CM closure available as workflow artifact
  `gst-full-source-dependency-report`.

This is a WHOLE-SOURCE IMPORT/DECLARATION NAVIGATION AUDIT, not a
claim that a human-like reviewer independently verified all 640
proof bodies. Proof semantics have been read closely for the
CM coefficient descent, CM surface transfers, four-factor switches,
theta extraction, cup/Gysin, realization algebra, rank-two
transversality and Hodge noncircularity modules. Mathematical
dependency tracing, not file naming, controls theorem reuse.

## Route 1: true Gaussian rational complex coefficient arithmetic

New Lean source: `GSTCMNumberManipulationTrace.lean`.

Models Gaussian-rational `Q(i)` CM parameters as `Q × Q`,
with explicit `cmMul`, `cmPow`, conjugation and inverse.
The corrected Equation (3) denominator is
`cmPow x (m+1) - cmPow y (m+2)`.

An exact rational field-trace identity is:
```
Tr_{Q(i)/Q}(1/(a+i b)) = 2a/(a^2+b^2), (a,b)!=(0,0).
```
It is invariant under conjugating both CM parameters,
even at arbitrary corrected index m. This produces a
CANONICAL RATIONAL coefficient from complex number theory,
unlike the earlier arbitrary real zeta coefficient.

Independent Wolfram Language verification returned exact zero
for the difference of the two sides. Concrete CM values
`x=1+i, y=i, n=1` give denominator `2+i`, reciprocal
`2/5-i/5` and rational conjugate trace `4/5`.

**Lean CI: 38677338320 — SUCCESS**.

## Route 2: two-channel NM avoids losing imaginary CM geometry

New Lean source: `GSTCMNumberManipulationDualDetector.lean`.

The real trace alone can vanish on a nonzero complex number:
`1/i=-i` has real trace zero. Rather than pretending its
vanishing means no CM geometry, retain both real and imaginary
rational channels simultaneously.

For every legal corrected index, the rational Gaussian inverse
is nonzero and at least ONE readout is nonzero. Multiplying both
channels by the FIXED rational `zeta(0)=-1/2` preserves this
disjunction. This is an exact arithmetic detection statement,
NOT yet a claim that those arithmetic channels are periods
of independent algebraic cycles on every variety.

**Lean CI: 38677498829 — SUCCESS**.

## Route 3: CM imaginary quadratic polynomial forces rank-two movement

New source: `GSTCMQuadraticNativeRankForcing.lean`.

Let an ACTUAL realized finite-closed Hodge-compatible
correspondence R act on a rational Hodge fiber by T and obey

```
T² - 2a*T + (a²+b²)*Id = 0,    a,b in Q, b != 0.
```

The CM eigenvalue polynomial has discriminant **-4 b²**.
If `T(z)=c*z` for rational c and nonzero z, then

```
((c-a)²+b²)*z = 0,
```

a contradiction over the rationals. Thus arithmetic
FORCES a transverse ACTUAL native cycle-class direction
from any nonzero native spine class; it is not separately
assumed. Existing genuine closed-correspondence naturality
ensures the moved direction is the class of a constructed
native algebraic cycle. For rational Hodge rank EXACTLY TWO,
the two native directions span the whole fiber. A fixed
CM-NM measured period may independently certify a nonzero
native seed, provided its comparison with the actual Hodge
readout has been proved.

**Lean CI: 38677771902 — SUCCESS**, further integrated genuine scheme-graph and dual-period version **38678461251 — SUCCESS**.
**Wolfram:** discriminant -4b²; eigenvalues of the concrete
CM rotation `[[3,-2],[2,3]]` are `3±2i`.

The CM polynomial relation is a substantive, independently
geometric object that must be proved for a genuine abelian
CM endomorphism's action, rather than assumed for arbitrary
Hodge fibers. On abelian varieties CM naturally acts on
degree-one cohomology; its induced action on rational (p,p)
tensors may have entirely different eigenvalues.
The rank-two implication is not a universal Hodge proof.

## Existing CM paper/GST resources actually relevant

- `GSTClassicalHodgeCMFourFactorSwitch.lean`: balanced CM sign
  combinatorics; algebraicity is NOT implied by the switches alone.
- `GSTClassicalHodgeCMThetaPeriodExtraction.lean`: a nonzero
  mixed period selects a term; it does NOT independently construct
  the surface period.
- `GSTClassicalHodgeCMSurfaceTensorContraction.lean`: surface
  integration produces a rank-one period contraction; genuine
  kernel and nonzero period inputs remain mathematical tasks.
- `GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler.lean`: actual
  product pullback/cup/Gysin is expressed from supplied structural
  product cohomology, finite point incidence and source packet.
- `GSTClassicalHodgeCMNativeRationalDescent.lean`: a genuine
  rational native cycle is built from a FINITE extension-field
  linear combination of genuinely native classes, PROVIDED the
  target equality in extended Betti coordinates is proved.
- `GSTClassicalHodgeOpenAIGeometryNoncircularityAudit.lean`:
  generic period certificates are equivalent to an algebraic
  Hodge basis witness; naming certificates does not resolve Hodge.
- `docs/OPENAI_2026_GEOMETRY_GST_ATLAS.md` is a literature
  INVENTORY plus partly specialized interpretations. It does
  not establish that every OpenAI manuscript has been
  verified, fully imported or integrated into HC-PROOF.

## Exact open geometric implications

1. Explicitly construct an actual source CM abelian variety
   and actual abelian endomorphisms whose action is represented
   by the relevant CM number field; check polarizations and
   rational coefficient embeddings.
2. Build canonical Betti period identities from that source's
   complex multiplication and theta forms; connect the
   corrected CM NM kernel channels to these periods via an
   actual theorem, not a free equality.
3. Prove the nonzero source period AND a full family of
   independent geometric cup/Gysin correspondence images;
   a single CM scalar/field trace cannot generate an arbitrary
   rank Hodge fiber.
4. Prove a functorial cross-carrier transfer from CM abelian
   sources to arbitrary projective targets (or use a second
   mechanism for varieties not generated by such transfers).
5. Descend algebraic extension coefficients to Q and verify
   that all targeted cohomological Hodge (p,p) classes
   are represented by actual rational algebraic cycles.

This is the original completion contract. Passing Lean on a
conditional implication does not complete it. Additional
number-theoretic theorem production should be judged by
whether it discharges one of these geometric comparison links.

---
All personal author names intentionally omitted from new files.

## Latest proof integration and source-audit correction

The final source `GSTCMQuadraticNativeRankForcing.lean`
also contains:
- `actualCMGraphOfEndomorphism`: obtains an actually realized
  finite-closed correspondence from a real projective scheme
  endomorphism graph, using the repository's naturality theorem;
- `CM_NM_period_graph_rank_two_hodge`: fixed rational CM trace
  readout + geometric graph + CM polynomial yields native rank-two
  Hodge realization;
- `CM_NM_dual_period_graph_rank_two_hodge`: both rational real and
  imaginary channels prove source nonzero without assuming the real
  trace itself is nonzero. The full corrected-source and CM graph
  proof chain is verified in **38678461251 (SUCCESS)**, including
  `#print axioms` and a no-`sorryAx` source gate.

These new modules were imported into the public
`HodgeConjecture.lean` and registered in `lakefile.toml` at
commit `048b1476ef84876376255f407ae0b931b7ec7219`.
The separate complete-root GitHub CI run **38678384513** is
NOT to be described as successful until its own final status is
observed. The focused proof gate was already successful.

An additional all-source declaration scanner
`scripts/gst_theorem_declaration_catalogue.py` reads every
file and records declaration names, line numbers and imports.
Its FIRST revision counted a word `axiom` inside a documentation
comment, so it was corrected to lex nested Lean comments before
declaration counting. The corrected comprehensive scanner passed
in **38678305657**, yielding 642 files and **8,587 source
declarations (6,002 actual theorem declarations)**. This
supersedes the earlier unfiltered 8,655/6,014 totals.
No explicit Lean `axiom` declarations were found by the corrected
declaration scanner. This is an index, not a transitive Lean
kernel trust proof of every theorem.

**Unresolved universal geometry:** Prove that a canonical
period comparison and adequate actual abelian CM-derived
correspondence tensor images exist for arbitrary rational Hodge
directions on arbitrary smooth projective varieties. The
rank-two conditional implication is machine verified but
does not establish those existence facts. For rank>2 and
CM fields beyond Q(i), further genuine geometric generation
and CM character descent are required.
