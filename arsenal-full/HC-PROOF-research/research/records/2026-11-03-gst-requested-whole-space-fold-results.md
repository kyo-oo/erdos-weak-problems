# The requested whole-space experiment: constructed folds and exact outcomes

Date: 3 November 2026, Asia/Calcutta. Base checkpoint:
`ef1a452d5a91e5e8c8a740fbda5761faf4cb9e0a`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

The owner explicitly corrected the previous response: execute the visual
whole-space experiment, using the custom GST modules, instead of returning
to the selected-cycle source program. This update follows that instruction.
It constructs the spaces, the dimensional fold, the whole cohomology model
and the preserving/breaking equations. It adds **25 theorem drafts directly
to six existing Lean files**, including the integration entry point.
No new Lean wrapper file is added. Lean compilation stays with the owner.

The [mathematical derivation](../derivations/GST_whole_space_central_causal_fold_2026_11_03.tex)
was written before the Lean changes. It contains the construction and proofs,
not a list of proposed research steps.

## The result of the experiment

For every original smooth projective X and every finite integer curvature
matrix K of size r by m, construct the actual compact complex world
`W_K(X)=X x Z_K` from a central causal cocycle. Its observed complex dimension
is `dim(X)+m+r`. There is no upper bound on m or r.

For a chronological fold history, use the actual shared-base quotient
fusion. Its endpoint has total curvature `K_total=sum K_edge`. The exact
decision equation is

`missing canonical Hodge modes in H1 = rank(K_total)`.

Equivalently, in this constructed family,

`the whole canonical Hodge structure survives iff K_total=0`.

This proves both branches. Zero curvature gives the projective world
`X x E_i^(m+r)` and its full Hodge polynomial
`H_X(u,v)(1+u)^(m+r)(1+v)^(m+r)`.
Nonzero curvature gives a compact complex world whose actual degree-one
Hodge filtration fails opposedness by exactly `rank(K_total)` dimensions.
The failure can occur with even b1, so it is stronger than the earlier
odd-Betti Hopf diagnostic.
For **every output dimension N >= dim(X)+2**, choosing `r=1`,
`m=N-dim(X)-1` and either `K=0` or `K=(1,0,...,0)` constructs the two
outcomes in the same observed dimension. Their first Betti numbers differ.

The actual fusion is

`Z_K star Z_L = (Z_K x_(E_i^m) Z_L)/E_i^r = Z_(K+L)`.

The middle fiber product has complex dimension `m+2r`; the quotient has
dimension `m+r`. Its central transition functions and integer lattices are
computed, so this is a fold of the space itself. It does not keep an old
variety fixed and merely re-label a cohomology class.

**Independent dimensions and fused dimensions give different outcomes.**

| Operation | Actual space | Missing first-Hodge modes |
| --- | --- | ---: |
| Independent opposite folds | `Z_K x Z_(-K)` | `2 rank K` |
| Shared-base quotient fusion | `Z_K star Z_(-K)=E_i^(m+r)` | 0 |
| A general fused history | `Z_(sum K_edge)` | `rank(sum K_edge)` |

For one base and one central handle, the independent product has complex
dimension four, b1=6, dim F1=2 and defect two. Fusion produces a complex
two-dimensional projective torus, b1=4, dim F1=2 and defect zero.
The history `(K,-K)` therefore has a broken intermediate world and a fully
restored endpoint. Restoration is of the entire endpoint Hodge structure.

## The owner's idea, line by line

| Requested part | Actual formalization / outcome |
| --- | --- |
| Start behind geometry in General Space | The existing `GeneralSpace` root has only points and typed composable paths; the new `causalWordSpace` is an actual instance retaining the whole history |
| Dimensions emerge from realizations | `Z_K` is built from its cocycle and lattice; `m+r` is then observed as its complex dimension; the original scheme dimension observer stays intact |
| Retain all N-cohomology | Every exterior channel in every degree is retained; differential, kernel and boundary image are computed |
| Link dimensionality with causality | Matrix entries are actual central commutators; the bilinear cocycle proves associativity and supplies higher coherence |
| Fold the topology into unusual structures | The integer lattice quotient is a compact complex central-torus bundle; nonzero curvature changes its topology and canonical filtration |
| Actually manipulate dimensions | Fiber product followed by antidiagonal quotient changes `m+2r` to `m+r` |
| Test multiple equations | Full exterior differential, opposedness quotient, fusion sum, prefix test, independent-product law and all-degree Betti polynomial are derived |
| Preserve the entire Hodge structure or break it | Exact criterion `rank K_total=0` versus positive rank, with the full zero-curvature spectrum and a degree-one obstruction to whole purity |
| Assume universal HC true during the experiment | The premise is retained for all projective endpoints; the nonzero-curvature worlds leave that category |

The original smooth projective X remains a factor. It does not itself
become non-Hodge while retaining its old projective complex structure.
The newly realized whole world is the changed object. This experiment
therefore does not produce a smooth-projective counterexample to the
provisional hypothesis or deduce that hypothesis unconditionally.

## How the actual custom modules are used and upgraded

| Existing file | Existing input actually used | Implemented extension |
| --- | --- | --- |
| `GSTGraphV2UnboundedHigherCausality.lean` | `causalTwoBoundary_zero`, finite cycle/relation quotient | Explicit central bilinear cocycle, associative multiplication and commutator readout |
| `GSTGraphV2GeneralSpaceRealization.lean` | Actual `GeneralSpace` construction and path composition | A separate spatial word sector, curvature observation, composition and inverse-fusion endpoint/prefix laws |
| `waves/GSTNCohomologyV3.lean` | Independent delta basis, reconstruction and multiworld product indices | Full vector curvature boundary, basis-column detection, exact zero-curvature criterion and complex scalar extension |
| `GSTCausalFoldDefect.lean` | Causal composition defect and endpoint/prefix distinction | Explicit pure-part construction and the iff criterion for a closed channel to split into two pure types |
| `GSTGradedWorldAlgebra.lean` | Charge/purity readouts and the scoped balanced-signature law | Full opposedness-defect arithmetic, even-b1 break, independent-product defect and fusion dimension law |
| `GSTSpatialFoldResearch.lean` | Existing integration entry point | Imports/checks and a theorem instantiating the split law on the actual N-channel curvature matrix |

The unchanged ontology and dimension-observer definitions were read too.
The relevant existing proofs and definitions were inspected, not inferred
from filenames. The arithmetic SevenAxes `ForwardEdge` is not called a
complex-geometric edge; the spatial sector has its own actual construction.
No claim that every Lean body in the branch was semantically audited is made.

The earlier `balancedCausalFold_purity` remains valid for its graded cell.
It is not applied to assign a pure cell to a world before that decomposition
has been proved. The new missing-mode quotient supplies this whole-space
test. Likewise, a zero scalar total is not a zero channel vector: opposite
nonzero channel defects are retained in N-cohomology.

## The actual geometric calculation

The group law is
`(x,y,s,t)(x',y',s',t')=(x+x',y+y',s+s'+B_K(x,y'),t+t')`,
where `B_K(x,y')_a=sum_j K_aj x_j y'_j`.
The integer lattice gives a compact quotient. The invariant one-forms are
`X_j=dx_j`, `Y_j=dy_j`, `U_a=ds_a-sum K_aj x_j dy_j`, `V_a=dt_a`.
The full finite exterior complex has

`d U_a=-sum K_aj X_j wedge Y_j`, all other generator differentials zero.

The proof compares this complex with all de Rham cohomology by averaging
along the compact central torus and a bounded filtered-complex comparison
on the base torus. Whole-quotient symmetrization preserves complex type and
computes the actual filtration on cohomology. It does not claim a complete
Dolbeault-page comparison without proving one.

For `rho=rank K`,

`b1(Z_K)=2m+2r-rho`, `dim F1=m+r-rho`,
`H1/(F1+conjugate F1) = image(K transpose)`.

The kernel of this missing-mode map has a constructed pure decomposition:
for closed vertical coefficients `(c,d)`, its two parts are
`(c-i d)/2` and `(c+i d)/2`. They are both closed precisely when the
missing mode `K transpose d` vanishes. This exact sequence proves the
defect equation, including its sufficiency at K=0.

In every degree k, the rational Betti dimension is
`C(2m+2r,k)-rank D_k-rank D_(k-1)`.
The complex model computes the full cup algebra; rational Betti structure
comes from the actual manifold. No bare address is promoted to a canonical
period-lattice comparison. For one central handle, a closed all-dimensional
Betti polynomial is proved by symplectic wedge/contraction.

Two rows `(1,0)` and `(1,1)` have the same first-degree defect one but give
complete Betti lists `(1,5,11,14,11,5,1)` and `(1,5,9,10,9,5,1)`.
Thus the full N-cohomology calculation sees topology that a single defect
rank would miss. For K=I2, the even-b1 example has b1=6, dim F1=2 and
defect two.

## Proof audit and computation

Primary audit verdict: **proved as written for the specified family of
realized central folds**. This is mathematical self-review, not an
independent reviewer or a Lean-kernel receipt. The original requested
experiment is executed in this family for every X and unbounded finite
m,r. It is not claimed to classify every possible GST realization.

The reviewed obligations include: associativity and integer lattice;
compactness; explicit complex charts; actual Hodge filtration rather than
assigned labels; full differential and higher relations; quotient lattice
and fusion associativity; nullary cases; even-b1 control; independent versus
fused folds; preservation of every original-X cohomology factor; and visible
use of the provisional HC premise only on projective worlds.

The central-extension and torus-bundle mechanisms are established
mathematics. They are not claimed as newly invented GST discoveries. The
work here constructs their specific GST realization, derives its full
equations, and implements them in the custom modules. No public internet
search or historical-novelty claim was made for this update.

Command: `python research/experiments/gst_central_fold_run.py`.
Observed exact evidence: **13,840 Python checks**, **170 Wolfram assertions**,
all **22** declared full spectral tables and the small-matrix rank histogram
match. The 22 rows include a repeated nullary vertical-torus control, not
22 claimed distinct geometries. Bounds: one handle m=0..4 and every active
rank; the declared coupled two-handle fixtures up to real dimension 10;
all 81 two-by-two integer curvature matrices with entries -1,0,1; and all
64 triples of four declared points per matrix. The matrix-rank histogram
is `(1,32,48)` for ranks 0,1,2.

Python uses bit-mask exterior signs and exact Fraction sparse elimination;
Wolfram uses signed index lists, Signature, SparseArray and MatrixRank.
All boundary squares, duality tests and formula comparisons pass in their
declared ranges. These tests support the finite assertions; the uniform
theorems have the hand proofs above.

The first remote evaluation returned a tool internal error and supplied no
mathematical result. Its source and response are retained. After a successful
exact kernel probe, sparse rule construction replaced dense repeated boundary
evaluation; the complete remote run passed. Kernel version: 15.0.1 for Linux
x86 (64-bit), July 2, 2026. Remote process exit status and kernel runtime
were not exposed and are recorded as null.

Changed-source escape scans, 748-node parsed import acyclicity, LaTeX
environment balance, whitespace and the current-hash Mathbox v2 manifest
checks pass. Three preexisting lexical anomalies are byte-identical to base.
No Lean build, installation, CI dispatch or theorem-kernel validation is claimed.

[Manifest](../computations/gst_central_fold_20261103.manifest.json),
[independent output](../computations/gst_central_fold_20261103.independent.output.json),
[raw Wolfram evidence](../computations/gst_central_fold_wolfram_20261103.output.json).
