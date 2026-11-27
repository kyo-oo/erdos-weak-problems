# GST selected-cluster sources, global incidence return, and rational fibers

Date: 3 November 2026, Asia/Calcutta. Base checkpoint:
`b403d3aadd6ed79b2822037941e4503ca1788ec3`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.
Review provenance: implementing assistant's adversarial self-review, with
independently implemented Python/Wolfram finite computations. No agent review
or Lean compilation is claimed for these changes.

The original all-X rational Hodge target has not been proved. This update
executes the owner's topology-first selected-source construction and computes
its actual global Chow return, repairs two rational-coefficient errors in
Round 51, and strengthens existing Lean modules in place with **21 theorem
drafts**. It adds no new Lean wrapper module.

## What changed mathematically

The fixed input is arbitrary smooth projective original `(X,p,alpha)` and
the output sought remains a genuine rational cycle on X with canonical Betti
class alpha. The owner's idea was reread from its verbatim quotation in the
Round 51 derivation: start in dimensionless General Space, let geometry and
Hodge structure emerge through causal topology, then test the complete fold
process. An address or a locally chosen sheet cannot replace that process's
cycle-bearing output.

### 1. Rational scale and genuine missing direction are different

Round 51 called the odd multiples outside `2 Z u` a rational
"transcendental break". Every one is rationally represented by `(t/2)(2u)`.
The exact universal law for any Q-linear cycle map is

`m alpha in range(cl) iff alpha in range(cl)` for `m != 0`,

with explicit cycle `m^-1 Z` when `cl Z=m alpha`.
The integral parity/scale theorem remains valid in its stated integer type.
It supplies no rational Hodge defect by itself.

The repaired certificate uses rational span throughout its rational census
and separates the integer-index control from a proper rational missing
direction: `Q^2` against `Q e1`. On the 121 integer control vectors in
`[-5,5]^2`, precisely 110 have nonzero second coordinate and are missing;
all remain missing under every nonzero rational scale. This is a linear
detector control, not a smooth-projective counterexample.

Changing to rational membership exposed a second defect: the old planted
vector `(0,0,1,1,0,0)` is already in the Gr25 model's rational source span.
Its explicit witness in the declared source columns is
`(10 G0 + 9 G1 - 4 G2)/37`.
It is now explicitly accepted as a negative control, with a checked
off-span replacement. These named census models remain abstract receipt
data; their labels do not construct the named algebraic geometries.

The source experiment and the original theorem are corrected in place.
The historical Round 51 record and audit receive a clearly marked subsequent
correction; their prior prose, outputs, PDF and review provenance are retained
as history and are not represented as current validation.

### 2. Actual alpha-dependent selected eigencluster geometry

Use the [prior alpha-dependent polynomial near-projector construction](2026-10-24-mathbox-alpha-selected-polynomial-spectral-cover-nonlinear-source.md) on the affine
Jouanolou geometry `J -> X`, preserving the locally selected topological
character on its detecting compact core. A sufficiently small general
constant matrix perturbation preserves that gap and ensures a nonempty
regular spectral open U. It does not force a claimed monodromy group.

Over U construct the genuine finite etale selector `T_r -> U` of r-element
root subsets and its actual rank-r eigenbundle F, with complement Q. On the
ordered-root torsor, the eigenlines split the trivial ambient bundle.
Tracing any positive-degree universal Chern polynomial of F and Q over
**all** selections is a symmetric polynomial in those eigenline Chern
roots, hence zero in actual rational Chow. This includes mixed Chern
monomials, not only a single additive eigenline character.

A selected connected component corresponds to an actual monodromy orbit
on root subsets. Full symmetric monodromy makes each selector connected.
Alternating monodromy does too for n>=3, and also for ordered partial flags
with a block of size at least two. Fully ordered eigenlines under alternating
monodromy retain a possible orientation invariant, whose first degree is
`n(n-1)/2`. Its formal existence does not prove a nonzero geometric class.

### 3. Stronger global result: the complete incidence source is neutral

The construction was then continued across the discriminant rather than
stopping at open-set localization. On `J x Gr(r,n)` define the genuine
zero scheme

`Z_a={(u,F): a(u)F subset F}`.

It is the zero locus of the matrix-induced section of `Hom(F,Q)=T Gr`.
Its map to J is proper, and it contains the analytic selected-cluster
section wherever that cluster remains separated, including internal
eigenvalue collisions.

For an arbitrarily small general constant perturbation this is a smooth
regular zero locus of dimension dim J, with no component wholly over the
discriminant. The proof constructs the universal smooth incidence family;
generic smoothness and the dimension of its discriminant divisor give the
claimed parameter open. No generic full-monodromy assertion is needed.

Projection formula and the actual regular zero-locus Chow identity give

`f_* P(c(F),c(Q)) = 0` for every homogeneous positive-degree P,

`f_*[Z_a] = binomial(n,r)[J]`.

Indeed its class in `J x Gr` is `c_top(T Gr)`, pulled from the fixed
Grassmannian. Multiplying by a positive-degree tautological class exceeds
the Grassmannian's dimension. A constant regular diagonal matrix counts
the degree-zero term by its reduced coordinate-subspace zeros. The proof
extends to every ordered partial flag type.

If the regular-region monodromy is transitive on that flag type, the smooth
incidence is irreducible, so choosing its whole component does not evade
the global vanishing. The affine-bundle Chow return to original X is then
exactly zero for this complete regular incidence recipe.

This is stronger than the open-set calculation: the actual discriminant
fibers of this complete incidence source are included. Separate components
under reduced monodromy, nongeneric excess cycles, independent correlated
matrix sources, nontrivial ambient bundles, and other boundary-supported
classes are outside this vanishing theorem. In the nonregular case a
top-Chern virtual cycle is not automatically the cycle of an excess
component. The target-specific source class cannot be inferred from the
existence of the local contour section.

### 4. Full-fiber branching with the cycle retained

`nativeCycleCombination` constructs a finite rational sum of actual
transported seed cycles at independently specified depths. Its canonical
class equation is derived from linearity and existing edge naturality.
If its computed sum equals a prescribed alpha, the actual constructed
cycle has that class. No universal coverage premise is manufactured.

The address-versus-vector distinction is also checked on actual
`P1 x P1`: both ruling classes have address `(2,1,1)`, while the single
ample seed `h1+h2` misses the nonzero primitive vector `h1-h2`, whose
intersection square is -2. Actual algebraic ruling projectors recover
both components, yielding the cycle `a[ruling1]+b[ruling2]` for every
prescribed `a h1+b h2`. This tests and corrects a universal single-address
inference; it does not substitute a surface problem for the original target.

## Files and verification boundary

The [new complete derivation](../derivations/GST_selected_cluster_transfer_and_rational_fiber_2026_11_03.tex)
was written before its Lean implementation; the global incidence proof was
added while continuing the same executed source attempt.

| Existing Lean file | New theorem drafts | Scope |
| --- | ---: | --- |
| `GSTCausalFoldDefect.lean` | 4 | Explicit finite cycle sums, normalization and rational saturation |
| `GSTLawStackRound51.lean` | 7 | Constructed branching, two-ruling source reconstruction, rational deficiency control |
| `GSTSpectralBoundaryDefect.lean` | 10 | Rank-three complete-cluster and cyclic/orientation identities |
| `GSTSpatialFoldResearch.lean` | 0 | Imports/checks for the strengthened entry point |

The arbitrary-rank schemes, monodromy descent, generic perturbation,
zero-section intersection, canonical Chow/Betti comparison and original-X
return are hand proofs, not scheme instances in these Lean drafts. The
formal finite-combination API requires an actual compatible realization;
the equality of its output with a target is checked input, not a theorem
about every target. Owner verification remains `lake build GSTSpatialFoldUpgrade`.
No local Lean installation, compilation, CI dispatch or kernel axiom receipt
is claimed. No global novelty claim is made.

## Exact evidence

Command:

```sh
python research/experiments/gst_cluster_rational_run.py
```

Observed completed run: local exit 0, **2,740 Python checks** and
**2,193 Wolfram assertions**. Every one of the five normalized result tables
agrees after reparsing the raw Wolfram output, including 327 selector Chern
polynomials (72 degree-count rows), 18 group Hilbert tables, and 18
Grassmann tangent top-Chern degree rows. The corrected Round 51 suite runs
as part of the local check: **75 passed, zero failed, exit 0**.

Wolfram kernel: `15.0.1 for Linux x86 (64-bit) (July 2, 2026)`;
observed kernel runtime **0.398287 seconds**. Remote process exit status is
not exposed and is recorded as null. Python uses integer sparse polynomials,
its own monic triangular coinvariant division, explicit permutation
enumeration, and Fraction arithmetic. Wolfram uses SymmetricReduction,
GroebnerBasis, symbolic series and conjugacy-class cycle-index summation.

Bounds: selectors n=2..5, every r=0..n, every two-block Chern monomial
of weighted degree 1..4; S_n/A_n/cyclic invariant Hilbert tables n=2..7
through degree n(n-1)/2; all 18 Grassmann degrees n=2..5; 121 rational
target pairs and five signed nonzero rational scales. The rank-three
orientation has nonzero formal normal form `-6*x1*x2^2`, while its square
is zero. This proves the stated finite ideal assertions, not geometric
nonvanishing or the universal conjecture.

The changed-Lean escape scan, 746-node parsed local import acyclicity,
LaTeX environment balance and whitespace checks pass. Three pre-existing
lexical anomalies are byte-identical to the base and remain untouched.
The Mathbox v2 manifest validator passes with current input/output hashes:

```sh
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_cluster_rational_20261103.manifest.json --root .
```

[Manifest](../computations/gst_cluster_rational_20261103.manifest.json),
[independent output](../computations/gst_cluster_rational_20261103.independent.output.json),
[raw Wolfram evidence](../computations/gst_cluster_rational_wolfram_20261103.output.json).
Historical manifests still refer to their original source revisions.

## Proof audit and continuation checkpoint

Self-review verdicts: rational saturation and the ruling diagnostic are
proved as written; the complete-selector and regular-incidence theorems
have hand proofs in their explicit scopes; formal orientation candidates
are not promoted to geometric cycles; universal original-X source existence
remains open. Smallest unsupported implication: a target-dependent global
selection or excess component with computed canonical class alpha, beyond
the complete-incidence cancellation proved here.

The complete generic incidence route is closed as a source-birth mechanism
in that scope. The reduced/correlated-monodromy and nongeneric excess routes
remain open, not exhausted. A resumption must construct the actual selected
component or excess class and compute its original-X period; repeating the
full-selector trace, an integer-index break, or an address orbit is excluded.
