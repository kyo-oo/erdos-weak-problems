# GST extension-sensitive spatial folds: exact equations and pairing graphs

Date: 3 November 2026, Asia/Calcutta. Base checkpoint:
`6191cdc6bb5a3f94d422da4a39ccaa7f6e2008d7`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.
Review: mathematical self-review; independently implemented Python and
actual Wolfram calculations. Lean compilation remains with the owner.

The owner's request was reread as a whole-space question: dimensions emerge
from GST; manipulate the realized space, retain N-cohomology and causal
structure, and derive equations that preserve or break Hodge type. The
requested provisional assumption of universal Hodge algebraicity is kept
separate from an independent proof. This update derives both behaviors in
actual folded realizations over every original X. It does **not** prove or
refute the universal Hodge conjecture.

## What the re-read changed

The dimensionless root contains no metric or dimension field. Scheme
dimension is an observation of local rings. An N-hole index is a multiplicity
coordinate, and a higher-causal index is a coherence degree; neither becomes
the geometric dimension by a change of name. The actual definitions in
`GSTGeneralSpace.lean`, `GSTGeneralSpaceSchemeDimensionObservation.lean`,
`GSTGraphV2GeneralSpaceRealization.lean`, `waves/GSTNCohomologyV3.lean`, the
spatial-fold files, and the relevant derivations were inspected.

The existing signed purity spectrum already permits positive-gap births
and balanced open/nodal signatures. The four-generator monoid of Round 50
has no such positive generator; its isolation result remains restricted to
that monoid. The advance here is an exact **extension/period equation** for
actual smooth projective nearby handles. A pure graded address, balanced
signature, or monodromy-fixed vector need not pass that equation.

Two earlier interpretations must remain excluded: a nonalgebraic rational
Hodge class is still a Hodge class, and a projection onto the full canonical
Chow image is not an available algorithm merely because its abstract linear
existence has been written down. A rational class leaving (p,p) type is not
an HC counterexample. Universal address coverage does not prove coverage
of every vector in a Hodge fiber. The prior rational-saturation correction
also remains in force.

## Executed mathematics

The [complete derivation](../derivations/GST_extension_sensitive_causal_folds_2026_11_03.tex)
was written before the new Lean modules.

1. **Exact two-handle period law.** On the actual elliptic product, write
   `v=A a1 a2+B a1 b2+C b1 a2+D b1 b2`. Its rational cross class is (1,1)
   exactly when `A tau1 tau2-B tau1-C tau2+D=0`. The proof computes the
   exterior wedge and conjugate, retaining every coefficient.
2. **Monodromy and extension are separated.** For `tau_i=n_i z+u_i`,
   the full-family equation is `A=0`, `n1 B+n2 C=0`, `D=B u1+C u2`.
   A nonzero rational solution exists exactly when `n2 u1-n1 u2` is
   rational. Monodromy alone supplies only the first two conditions.
   The graded low/high pieces have gaps -1/+1; their compensation loses
   the extension data unless the last equation is retained.
3. **Successful folds have actual graph cycles.** If that rational condition
   holds, an explicit lattice inclusion gives an algebraic isogeny.
   Its graph minus the two factor divisors gives the exact cross class,
   with intersection `-2 n1 n2`. These are constructed Chow divisors,
   not Hodge-to-Chow witnesses assumed as fields.
4. **A decisive actual break control.** At `(tau1,tau2)=(i,i+sqrt(2))`,
   the rational cross Hodge space is zero. The balanced vector
   `a1 b2-b1 a2` is monodromy fixed in the corresponding family but has
   nonzero period defect `sqrt(2)`. The surface itself has its usual pure
   Hodge structure; it is the marked vector that is not of type (1,1).
5. **All-arity three-test equation.** For synchronized elliptic handles,
   the tensor charge operators at `tau=i,2i,1+i` span the full sl2 charge
   algebra. Their common kernel is exactly the rational tensor space
   that is Hodge throughout the family, for every finite arity. At
   `m=2r` it has Catalan dimension and an actual noncrossing-pairing cycle
   basis; at odd arity it is zero. This is a theorem about the full
   synchronized tensor block, not a rank-one address collapse or the full
   Hodge space of a single CM fiber. Invariant-theory overlap is disclosed.
6. **Graph and N-cohomology upgrades.** Pairing amplitudes transform by
   `det(T)^(number of edges)`, so simultaneous SL2 causal recoordination
   preserves them. Plucker identities are typed as tensor-coordinate
   equations; actual exterior graph products retain their Koszul signs.
   N-cohomology now checks the rank-one minor equations, exhibits a
   two-channel vector that cannot be one separated tensor, and reconstructs
   every full fiber by an explicit finite sum retaining all indices.
7. **Prescribed original-X attempt and canonical coupling.** For every
   original `(X,p,alpha)`, the successful fold produces the nonzero Hodge
   class `beta=alpha external-product w` on the actual projective space
   `X x E x E` when alpha is nonzero. Cup with the actual graph divisor
   and proper push return `-2 alpha`. For r pairs the return coefficient
   is the product of the corresponding `-2 n_i n_j`. Algebraicity of beta
   is equivalent to algebraicity of alpha by this actual cycle return.
   Thus this source attempt computes its entire canonical coupling but
   does not independently construct a cycle for alpha. The irrational
   fold instead gives a non-Hodge marked product for every nonzero alpha.

The punctured-disk parameter families are analytic; each fiber is an actual
projective algebraic variety. No finite-type algebraic model of the full
period base is smuggled in. Sources and canonical Chow/Betti comparison are
hand-level here, not instantiated scheme proofs in Lean.

## Source attribution and audit

Checked primary sources: Sutherland, MIT 18.783 Lecture 17 (12 April 2017),
Theorem 17.4, for converting the explicit lattice map to an algebraic
isogeny; Kraft--Procesi, *Classical Invariant Theory*, July 1996 preliminary
version, Section 8.4, printed p.90, for SL2 determinant generation, restricted
to multilinear degree one in each handle. The dimension and noncrossing
independence arguments are given in the derivation. Bloch--de Jong--Sertoz,
*Heights on curves and limits of Hodge structures* (2023), Section 3.2,
corroborates dependence on smoothing data; the rank-two filtration used
here is computed directly. URLs and exact translations are in the LaTeX.
The Speyer note failed acquisition and is not an authenticated proof leaf.
No global novelty claim or OpenAI attribution is made for classical facts.

Self-review verdicts: the period, extension, graph-covariance and
normalization statements have explicit proofs in their stated domains;
finite computational assertions pass in the stated ranges; universal
original-X source existence is incomplete. This is self-review, not a fresh
agent audit or a Lean kernel receipt.

## Files and evidence

| Lean file | Added theorem drafts | Exact scope |
| --- | ---: | --- |
| `GSTFoldPeriodDescent.lean` | 13 | Period expansion, monodromy, extension and three-charge equations |
| `GSTCausalPairingGraphs.lean` | 11 | Bracket covariance, graph products, Plucker and return normalization |
| `waves/GSTNCohomologyV3.lean` | 4 | Separated tensor minors, entangled control and full-fiber sum |

`GSTSpatialFoldResearch.lean` imports/checks the additions; both new modules
are registered in the existing `GSTSpatialFoldUpgrade` library. Owner
compilation command: `lake build GSTSpatialFoldUpgrade waves.GSTNCohomologyV3`.
No Lean installation, build, CI dispatch or axiom-print execution was done.

Reproduction:

```sh
python research/experiments/gst_extension_fold_run.py
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_extension_fold_20261103.manifest.json --root .
```

Observed: **7,551 Python checks**, **7,469 actual Wolfram assertions**;
all four normalized result tables/controls agree after raw-output parsing.
Wolfram `15.0.1 for Linux x86 (64-bit) (July 2, 2026)`, observed runtime
3.845118 seconds. Remote process exit status is not exposed and is null.
Local runner exit 0; Mathbox v2 evidence validation passes.

Bounds: all 81 coefficient quadruples in [-1,1]^4 for each of 36 declared
slope/offset pairs; three period values; all 625 quadruples in [-2,2]^4
for the exact irrational control; all tensor arities 0..8, including the
vacuum and every recursively enumerated noncrossing matching; all 625
2x2 matrices with entries [-2,2] on the two stated test vectors. Python
uses sparse Fraction elimination, its own Q(i,sqrt(2)) field and signed
exterior products; Wolfram uses KroneckerProduct/NullSpace, RootReduce,
determinants and permutation signatures. These finite checks do not prove
the all-arity or arbitrary-X statements; their hand proofs are separate.

The remote unary tensor-lift bug was isolated and corrected: Wolfram's
KroneckerProduct requires two or more arguments, so arity one needs its
actual matrix as a separate case. The failed run is preserved in the raw
evidence. A later successful warning-bearing run was repeated after local
symbol renaming; the final run is clean. Failed diagnostics are not counted
as positive evidence.

The source check inventories all **751 Lean and 108 LaTeX** files by bytes,
parses an acyclic **748-node** local import graph, and confirms the three
pre-existing malformed-comment files are byte-identical to the base.
Changed files have no proof escapes; LaTeX environment balance and whitespace
checks pass. This is **not** a line-by-line semantic audit of 751 proofs.
No LaTeX typesetting is claimed.

[Manifest](../computations/gst_extension_fold_20261103.manifest.json),
[independent results](../computations/gst_extension_fold_20261103.independent.output.json),
[raw Wolfram output and diagnostics](../computations/gst_extension_fold_wolfram_20261103.output.json).

## Continuation handoff

The extension-sensitive fold question now has actual preserving and breaking
equations, full-vector graph generators, and an exact original-X coupling.
The synchronized auxiliary-handle recipe is closed as an independent
universal source mechanism: its return preserves the original source defect.
The genuinely different selected-incidence/excess-component route from the
preceding checkpoint stays open. Resumption requires an actual selected
component or nongeneric excess source with a computed alpha-dependent
canonical class, or a genuine deformation of X with independently controlled
source geometry; repeating auxiliary tensor stabilization, balanced grades,
full-incidence traces or an assumed universal Hodge selector is excluded.
