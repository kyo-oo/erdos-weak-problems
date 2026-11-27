# Nonlinear relative GST folds: classification, full ring and secondary memory

Date: 3 November 2026, Asia/Calcutta. Starting checkpoint:
`2e0324f1328409d68c25d85897435187d0a380b0`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

This continuation removes the preceding theorem's restriction to linear
changes of the handle generators. It proves a complete classification of
the finite **pure paired models over their marked original Hodge base**
even when arbitrary nonlinear relative quasi-isomorphisms are allowed.
It also determines the one-curvature cohomology algebra, executes a genuine
nonlinear fold on every basis state, and constructs a nonzero secondary
operation. The actual universal original-X Chow-cycle problem is not
claimed solved by these topological results.

[Hand derivation](../derivations/GST_nonlinear_relative_fold_classification_2026_11_03.tex)
was written before the Lean changes. The preceding finite normal-form proof
is reused at its stated strength, not promoted into an algebraic source.

## Exact completed structural results

Fix arbitrary connected original smooth projective X. Set
`A = direct sum_q Hdg^q(X)_Q`, with cohomological degrees `2q`, and
`m = A_{>0}`. For a finite list `a_i` of weights `p_i >= 1`, use

`B(a) = A tensor exterior(u_i,v_i), du_i=a_i, dv_i=0`,
`degree u_i = degree v_i = 2p_i-1`.

All relative maps fix the original A pointwise.

1. **The entire marked-base kernel is computed.**
   `ker(A -> H*(B(a))) = I(a) = (a_i)`.
   Thus `A/I(a)` is precisely the image subalgebra of the original base.
   The proof takes the exterior-length-zero part of a boundary; only its
   one-letter inputs can contribute. Conversely every ideal element has
   an explicit one-letter primitive. No regular sequence is required.
2. **The invariant survives nonlinear maps and quasi-isomorphism zigzags.**
   A relative quasi-isomorphism induces an isomorphism on cohomology
   commuting with A. Hence the base kernel is unchanged. This statement
   permits intermediate differentials containing products of handles.
   A target admitting a chain retraction onto `(A,0)` must have zero kernel.
3. **The classification is complete for pure paired presentations.**
   Two such finite models are equivalent by an arbitrary relative DGA
   quasi-isomorphism zigzag if and only if their graded ideals I agree
   and all handle-pair counts `r_q` agree. Under those conditions a
   homogeneous A-linear paired coordinate isomorphism already exists.
   The ideal comes from the base kernel; the counts come from the graded
   indecomposables of the derived fiber
   `Q tensor_A^L B = (exterior_Q(u_i,v_i),0)`.
   Finite semifreeness justifies this derived calculation. The old graded
   local reduction constructs the converse isomorphism and proves that
   the sharp active minimum `dim_Q(I/mI)_q` also holds in this larger class.
4. **All original cohomology is retained.** For
   `R=H*(X,Q)`, the full model has kernel `I R`. Its rational Hodge
   contraction is exactly I. The proof uses a rational Hodge splitting
   of the multiplication map, obtained from the polarizing orthogonal
   complement of its kernel. It does not assume that complex Hodge
   projection is rational or discard off-diagonal/odd base classes.
5. **The whole one-curvature cohomology ring is computed.**
   For `du=a,dv=0`, it is
   `(A/(a) semidirect Ann_A(a)*u) tensor exterior(v)`.
   The u summand is square-zero and the quotient action is well-defined.
   This specifies multiplication, rather than only a Betti polynomial.
6. **The ring does not erase higher operations.** For the actual rational
   torsor over `P1 x P1` with `du=xy`, the triple Massey product
   `<[x],[y],[y]>` is represented by `[-uy]`, modulo the complete
   indeterminacy `span([xv],[yv])`. It does not contain zero. This gives
   actual secondary cochain memory and prevents replacing the DGA by its
   zero-differential cohomology algebra.

The classification fixes the original base and concerns pure paired
endpoints. It does not classify all nonlinear-differential DGAs, all
unmarked spaces or all filtrations. The constructed converse isomorphism
does preserve the specified model filtration. Historical novelty is not
asserted; no new literature search was used for these elementary arguments.

## Executed nonlinear fold

On `P1 x P1`, take curvatures `(x,0,xy)` and handle pairs
`(u,v),(z,t),(w,s)`, with degrees `(1,1),(1,1),(3,3)`.
For every rational lambda the actual graded algebra substitution

`W = w - y*u + lambda*u*v*z`

has inverse `w = W + y*u - lambda*u*v*z`. Its full transported differential
is `dW = lambda*x*v*z`. Therefore W is not closed for nonzero lambda,
even though its differential has no handle-free term. The actual closed
coordinate is `W-lambda*u*v*z`. The invariant kernel remains the ideal
`(x)`, with dimensions one in weights one and two.

This is an executed arbitrary nonlinear coordinate operation, not the old
linear shear relabeled. It illustrates precisely why all cochain terms
and signs must be transported. The general base-kernel proof, rather than
the special family, establishes its arbitrary-X implication.

The base marking also has a hostile control: curvatures x and y on this
same base give equal absolute Betti spectra and isomorphic unmarked
models by swapping x,y, but different marked ideals `(x)` and `(y)`.
Equal dimensions do not identify a prescribed original-base class.

## Original prescribed-alpha construction and outcome

For arbitrary original `(X,p,alpha)`, construct the actual rational
homotopy-fiber torsor of its classifying map and the flat companion, as in
the preceding checkpoint. Add any finite chosen cup births of alpha and
perform the full reduction. Its exact base kernel is
`(alpha) H*(X,Q)`, with rational Hodge contraction `(alpha)`. Nonzero alpha
therefore survives as a nonzero base-kernel invariant under every relative
nonlinear quasi-isomorphism. The pair counts and sharp minimum are now
classified beyond the original linear operation category.

This closes the nonlinear-coordinate loophole in that specific erasure
recipe. It neither refutes Hodge algebraicity nor rules out new geometric
sources. The actual constructed objects here are rational topology with
the stated filtered model, not universal rational Chow witnesses. The
unconditional canonical original-X cycle constructor remains unproved.

## Adversarial proof audit

Primary verdict: **proved as written**, for the stated marked-relative
model classification and the ring/secondary-operation assertions, by
author self-review. No independent human or agent review is claimed.

| Obligation | Result |
| --- | --- |
| Arbitrary original X and prescribed alpha | Passed: base-kernel derivation and torsor construction have those inputs |
| Entire boundary image, rather than only projected image | Passed: actual image/base intersection; ideal elements have genuine primitives |
| Nonlinear equivalences | Passed: cohomology kernel commutes with marked base; no handle-linear hypothesis |
| Zigzags and derived fiber | Passed by the stated semifree replacement/lifting argument, not by tensoring arbitrary modules |
| Pair multiplicity recovered in every absolute degree | Passed: degree `2q-1` indecomposables have dimension `2r_q` |
| Same invariants give an actual isomorphism | Passed using prior finite triangular graded normal form |
| Odd/off-diagonal original cohomology | Passed: full R retained; rational Hodge contraction separately justified |
| Kernel ideal equals whole cohomology | Refuted in general: annihilator and exterior summands remain |
| Vanishing base part of dW means W closed | Refuted for every nonzero lambda in the executed nonlinear family |
| Complete Massey indeterminacy | Passed: H3 is exactly Q*v, so the two indicated products exhaust it |
| Classification of arbitrary nonlinear differentials | Out of scope; only the kernel invariant is asserted for arbitrary intermediate DGAs |
| Universal original-X Chow constructor | Not established; no such output is asserted |

The critical derived-fiber step is a hand homological-algebra proof and
does not receive a universal proof certificate from the finite computations.
The ring formula concerns even A; the full R kernel has its own graded-sign
argument. This distinction is retained in the derivation and formal drafts.

## Lean changes and exact evidence

Two existing modules are edited. `GSTGradedWorldAlgebra.lean` gains
**13 theorem drafts**: the base-boundary submodule, relative-chain-map
monotonicity, full-module equivalence invariance, chain-retraction test,
exact first-coefficient/range computation, its composition law, and concrete
one/two-curvature kernel and annihilator results.
`GSTSpatialFoldResearch.lean` gains integration checks. There is no new
wrapper, proof escape, custom axiom or false source-surjectivity definition.
These additions do not pretend to formalize derived categories, the entire
classification, or Massey products. Compilation remains with the owner;
no Lean execution or CI dispatch was performed.

Reproduction:

```sh
python research/experiments/gst_nonlinear_relative_run.py
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_nonlinear_relative_20261103.manifest.json --root .
```

Observed: **7,204 exact Python assertions**, exit zero, and **1,318 Wolfram
assertions**. Shared nonlinear tables and secondary-coset ranks agree.

- Nine explicit pure presentations have their full boundary-image/base
  intersections compared with their ideal spans, using sparse column
  elimination and independent dense rational row reduction.
- For every lambda in `{-2,-1,0,1,2}`, all **256** basis states of the
  six-handle nonlinear model pass both inverse orders, the complete chain
  equation, differential square and absolute-degree checks. Its actual
  base kernel is recomputed after transport. These are 1,280 basis states
  across five parameter instances, not a finite proof for all rational lambda.
- Five one-handle rings have complete independent cohomology bases, all
  representatives checked closed, independence modulo all boundaries, full
  cohomology dimensions, and all **304** ordered products checked against
  the square-zero/quotient-action formula, with exterior signs.
- The secondary coset has indeterminacy rank **2**, increasing to **3**
  upon adjoining its representative; the entire degree-three domain is
  inspected. Thus the nonzero conclusion is not based on a chosen smaller
  indeterminacy.
- Wolfram uses ordered exterior words and exact dense matrices, while
  Python uses bit masks, sparse dictionaries and independent dense-rank
  controls. Wolfram checks both full 256-by-256 inverse matrices, the full
  chain equation and differential square for each parameter.

Kernel: `15.0.1 for Linux x86 (64-bit) (July 2, 2026)`. The final kernel
reports 1.81711 seconds for the five nonlinear cases. Remote process exit
status is not exposed and is recorded null. The first evaluation returned
passing tables with an unused-symbol wrapper warning. That wrapper was
removed and the entire source rerun; the final pinned raw response is clean.
Both responses and their input hashes are preserved. The context lookup
is not a source for a theorem in this record.

The current 748-node parsed import graph is acyclic. Three preexisting
lexical anomalies are unchanged from the base checkpoint. Changed-source
proof-escape scans, LaTeX environment balance and whitespace checks pass.
This is not a 748-module semantic proof review, Lean build or typeset-PDF
claim. Historical manifests remain historical for the source revisions
they pinned; the new manifest records this update's current input hashes.

[Exact output](../computations/gst_nonlinear_relative_20261103.output.json),
[raw Wolfram evidence](../computations/gst_nonlinear_relative_wolfram_20261103.output.json),
[current-hash manifest](../computations/gst_nonlinear_relative_20261103.manifest.json).

## Disposition

The pure-model classification under nonlinear relative quasi-isomorphisms,
the sharp active minimum in that enlarged category, the full one-curvature
ring and the displayed secondary operation are completed at hand-proof
level. A marked-relative coordinate change cannot create a new original-X
cycle source; the base-kernel theorem closes that proposed escape without
closing different source-geometry routes. Those routes remain governed by
the original exact canonical cycle target, rather than another fold plan.
