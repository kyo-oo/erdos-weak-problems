# Curvature established; divisorial extraction completed at its exact scope

Date: 3 November 2026, Asia/Calcutta. Starting revision:
`e40e328b80d3ede78202234054891b1e56edf0b3`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

**The central-fold curvature theorem is established at hand-proof level:**
the actual degree-one opposedness defect is the rank of total curvature.
This continuation supplies its full explicit missing-mode short exact sequence
in the existing custom Lean module. It also executes the outstanding
divisorial boundary construction, which the preceding top-support audit did
not cover for higher codimension.

[Full derivation](../derivations/GST_curvature_exact_sequence_divisorial_completion_2026_11_03.tex)
was written before the Lean changes. All mathematical review here is
author self-review. Lean compilation remains with the owner.

## Exact results and limits

| Claim | Status and required input |
| --- | --- |
| Central-fold curvature/opposedness theorem | Hand proof established for the stated lattice-defined family; exact sequence now implemented as algebraic Lean drafts |
| Zero curvature implies projectivity for arbitrary torsors | Not asserted; the separate torsion-gluing requirement remains |
| Kernel of restriction to an SNC divisor complement | Hand proof: exactly the sum of component Gysin images in every degree |
| Rational Hodge preimage in those Gysin sources | Constructed using the rational polarized complement of the Gysin kernel |
| Codimension-two source from an actual nullifying algebraic open | Completed: boundary line bundles and a proper original-X Chow formula |
| General higher-p source from that open | Conditional on actual codimension-(p-1) cycles for the constructed boundary Hodge classes |
| Smooth ample-divisor construction for arbitrary prescribed input | Executed; kills precisely the Lefschetz-multiple summand, with the primitive residual computed |
| Singular-boundary primitive return | Actual resolved tangent-quadric boundary line returns the difference of ruling planes |
| Universal prescribed-alpha algebraic open/cycle constructor | Unresolved; none is assumed or claimed |

## Curvature exact sequence

For the actual total curvature transpose `L`, let
`E_L = {(u,v) : L u = 0}`. The map `(u,v) -> L v` is onto `image L`.
Its kernel is exactly

`{(a+b, i(a-b)) : L a = L b = 0}`.

The inverse decomposition is `a=(u-i v)/2`, `b=(u+i v)/2`.
Thus the quotient has dimension `rank L`. The existing geometric cochain
and filtration comparison identifies it with the actual opposedness quotient.
In the stated central-lattice family zero total matrix constructs the
projective product, so all cohomological degrees regain the pure structure.
This is the curvature theorem's exact scope, without a source-surjectivity
premise or a silent extension to arbitrary compact complex spaces.

## The divisorial subconstruction

For an actual smooth-projective surjection `f:Y -> X`, retain the previous
positive generic degree `d` and actual return `f_*(h^r * -)/d`.
Let `U=Y minus D` for an actual simple-normal-crossings divisor.
The logarithmic weight sequence has

`E1^{-s,t}=H^{t-2s}(D^(s),Q)(-s)`.

Its incoming first differential to `H^{2p}(Y)` is the sum of component
Gysin maps. Pure weights force all later differentials to vanish, so
the kernel of restriction to U is exactly that image. Boundary intersections
contribute relations, without creating an additional incoming edge source.

A rational `(p,p)` class in that image has a **rational** Hodge preimage:
take the inverse of Gysin on the polarization-orthogonal complement of
its kernel. Merely taking a complex type component of a rational lift
would not justify rationality. This distinction is included in the audit.

In codimension two the resulting boundary classes are rational `(1,1)`.
Clear one common denominator N, then the exponential sequence and GAGA
construct actual algebraic lines `L_i` on the smooth boundary components.
The completed original-X cycle is

\[
Z_\alpha=\frac1{dN}f_*\left(h^r\cdot
                 \sum_i(i_i)_*c_1^{CH}(L_i)\right),
\qquad cl_X^{can}(Z_\alpha)=\alpha.
\]

Embedded resolution includes singular divisors. A dominant smooth
quasi-projective nullifying source can be compactified by graph closure
and resolved relative to its open. These operations start with an actual
algebraic source; a rational topological homotopy fiber is not such a source.
For higher p the exact rational Hodge lift is complete, while constructing
its lower-codimension Chow representatives is a separate obligation.

## Execute the prescribed-input open attempt

For every arbitrary original `(X,p,alpha)`, choose an actual smooth ample
divisor and its actual affine complement U. Its kernel is exactly

`ker(H^{2p}(X) -> H^{2p}(U)) = h cup H^{2p-2}(X)`.

Weak Lefschetz proves this in the low/middle range; hard Lefschetz proves
surjectivity in the upper range. The nonzero degree of the chosen ample
multiple does not change its rational image. Thus, in the central range,
the input's primitive Lefschetz component survives every such choice.
For p=2 the complementary `h beta` component has an actual divisor-product
source constructed from the prescribed rational `(1,1)` beta. This executes
the attempt and computes both the source and the residual; it does not
silently assume that residual is zero.

The smooth-boundary obstruction does not apply to all divisorial opens.
On a smooth quadric fourfold, a tangent hyperplane section is a cone over
`P1 x P1`. Blow up its vertex. Its strict transform and the exceptional
divisor form an actual SNC boundary. Pull back `O(1,-1)` from the quadric
surface to the resolved cone. Its actual divisor pushes to `A-B`, the
nonzero primitive difference of maximal-plane cycles. Every smooth ample
hyperplane complement retains that difference. The control demonstrates
exactly which additional singular-boundary geometry supplies the source;
these classical quadric cycles are not a universal-source claim.

## Source verification and review

[Source record](gst_divisorial_completion_sources_20261103.json) pins the
original published Deligne paper hosted by the author's IAS institution.
The residue construction, the weight sequence, pure weights and degeneration
were checked at sections 3.1--3.2, particularly 3.2.4, 3.2.8--3.2.10 and
3.2.13(iii); rational polarizability is at 2.2.6. The index translation
matters: the E1 weight sequence degenerates at E2, while its differently
indexed Leray sequence degenerates at E3. No full source text is copied.
The initial Numdam fetch timed out; the IAS scan was accessible.

The standard exponential/GAGA/(1,1), weak/hard Lefschetz and embedded
resolution inputs retain their classical hypotheses and attribution.
This work extends the branch's exact construction and review, with no
historical-novelty or independent-referee claim.

## Lean changes and computation evidence

`GSTCausalFoldDefect.lean` gains **10 theorem drafts** in two sections.
Five establish the explicit missing-mode surjection, zero criterion, pure
kernel and nonzero witnesses. Five retain rational type correction,
kernel ambiguity, boundary invariance, the two distinct denominators and
primitive survival. `GSTSpatialFoldResearch.lean` checks integration.
There is no new wrapper, assumed universal cycle selector or compilation claim.

```sh
python research/experiments/gst_divisorial_completion_run.py
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_divisorial_completion_20261103.manifest.json --root .
```

Python Fraction arithmetic and the actual Wolfram evaluator each pass
**41 exact assertions**; all six shared tables agree. Five rectangular
curvature matrices include zero, partial and full rank, with a separate
zero-handle control. The Hodge-lift fixture has a raw rational lift outside
the designated Hodge subspace, a rational corrected lift, a denominator
three and generic return degree six. Omitting either denominator fails
the expected equality. Five quadric-coordinate restriction controls and
the singular-boundary line-return coordinate test distinguish the two routes.
The zero-handle assertion checks its scalar dimension convention separately;
it is not claimed as an executed zero-width matrix computation.

The Wolfram kernel is 15.0.1 for Linux x86 (64-bit), July 2, 2026.
Its provider emitted undefined-global-symbol diagnostics despite Module-local
declarations; the complete retained JSON contains 41 passed TrueQ assertions
and no failed assertion. The context lookup returned an internal error.
Neither diagnostic is used as a mathematical premise. Remote runtime and
process exit status are not exposed and remain null. Raw output, source hash,
complete parsing and matching tables are preserved. Python observed exit zero.

The current-source v2 manifest validates. Changed Lean escape checks,
the 748-node parsed import graph, LaTeX environment balance and whitespace
checks pass. Three preexisting lexical anomalies remain unchanged.
These are lexical and finite checks, not Lean compilation, LaTeX typesetting,
or a repository-wide semantic proof audit. Earlier manifests are historical
after current Lean changes.

[Exact output](../computations/gst_divisorial_completion_20261103.output.json),
[raw remote evidence](../computations/gst_divisorial_completion_wolfram_20261103.output.json),
[current manifest](../computations/gst_divisorial_completion_20261103.manifest.json).

## Continuation

The curvature theorem is established; the codimension-two divisorial return
is completed for actual nullifying algebraic geometry. The direct smooth
ample-boundary recipe is closed for nonzero primitive residuals by its exact
kernel. The remaining universal task is constructing a suitable source for
that residual, not repeating this kernel calculation or assuming its support.
Selected/excess singular-boundary and other source geometries remain open;
this checkpoint neither exhausts those mechanisms nor claims their success.
