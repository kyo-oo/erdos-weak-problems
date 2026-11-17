# All-degree curvature, perfect duality and exact specialization memory

Date: 3 November 2026, Asia/Calcutta. Base revision:
`f96a12fe6c4617555a1495bd14c6ef2b06851c93`.
Branch: `research/gpt6-native-point-primitive-span-20261017`.

This continuation completes the **full cohomology calculation** of the
prescribed-input paired rational fold. It adds the perfect multiplicative
pairing, an exact all-degree loss polynomial and a parameter-dependent
construction that recovers the original curvature at first order. The
calculation retains odd base classes and arbitrary codimension.

[Full hand derivation](../derivations/GST_all_degree_curvature_duality_specialization_2026_11_03.tex)
was written before the Lean edits. Review provenance is author self-review.
Compilation stays with the owner; no build or CI was run.

## Exact input and completed theorem

Start with arbitrary original smooth projective connected X, codimension
1 <= p <= dim X and the prescribed rational Hodge alpha. Keep the entire
rational cup algebra A=H*(X,Q), its actual Poincare trace, d=2dim X and
s=2p-1. The existing rational homotopy-fiber construction supplies

`B_alpha = A tensor exterior(u,v), du=alpha, dv=0, |u|=|v|=s`.

This source is chosen from that alpha without assuming it is a Chow class.
For disconnected X apply the construction separately to each component.
The original owner remains an actual rational cycle on this same X with
canonical Betti class alpha. This record computes the rational fold, with
its geometric/cochain and algebraic-cycle types kept explicit.

The following all-degree statements have hand proofs:

1. The complete ring is `(A/(alpha) semidirect Ann(alpha)u) tensor exterior(v)`.
   The shifted annihilator ideal is square-zero. All odd-base signs are
   explicit, including moving a base coefficient past u and v.
2. The original Poincare trace gives a **perfect** pairing between
   `(A/(alpha))^i` and `Ann(alpha)^(d-i)`. Thus the one-curved-handle
   cohomology is the graded duality double of the surviving quotient.
   The paired model has Poincare dimension `d+2s`; this is a rational
   model dimension, not an asserted complex dimension.
3. If R_alpha(t) records the ranks of cup by alpha in every original-base
   degree, the exact polynomial is

   `P_B(t)=(1+t^s)((1+t^s)P_A(t)-(t^(s+1)+t^s)R_alpha(t))`.

   Its loss from the flat fold is exactly

   `t^s(1+t)(1+t^s)R_alpha(t)`.

   Total dimension is `4(dim A-rank L_alpha)` and the rank polynomial has
   its exact transpose symmetry. No finite table is used to infer this
   quantified formula.
4. For nonzero alpha, the first lost class is in degree **2p-1**, with loss
   exactly one. Every lower degree is unchanged. Therefore the degree-one
   curvature test alone cannot see any p>=2 target fold. This supplies the
   stronger higher-degree test with an explicit first detecting degree.

## New source-search route: switch curvature off while retaining its memory

Construct the actual free rational cochain family over T=Q[z]:

`mathcal B = A[z] tensor exterior(u,v), du=z alpha, dv=0`.

This is a DGA family, not an assumed projective family. Its full cohomology
is computed by the same explicit closed coefficients and boundaries.
Its z-torsion is **exactly**

`alpha A tensor T/(z) tensor exterior(v)`.

There is no higher z-power torsion. The total torsion dimension is twice
the full cup-operator rank. Degreewise universal coefficients give the
short exact specialization sequence with its adjacent Tor term. The
special world gains four times that rank over the generic world: half
comes from torsion and half from Tor. Consequently ordinary substitution
in generic cohomology misses actual special-fiber classes.

The first Bockstein is the derivation `u -> alpha, v -> 0, A -> 0`.
Its cohomology is H(B_alpha); later differentials vanish by the complete
free-plus-two-term block decomposition. The marked first jet determines
the **entire** cup operator, and evaluation on the unit handle recovers
the prescribed alpha itself. An arbitrary first-order correction cannot
cancel a nonzero value of this obstruction.

This executes the parameter-dependent construction and computes its exact
original-base coupling. It is distinct from repeating the earlier base-ideal
classification or a full-rank source equivalence. It does not create a Chow
representative: the source produced here is the specified rational cochain
family. The previous projective retraction theorem continues to prevent
calling a nonzero-alpha nullifier a compatible projective realization.

## Discriminating checks, rather than another handle count

On the actual P2 x P2 base compare the two degree-four inputs x^2 and xy.
Both have one active curvature handle, codimension two and unchanged b1.
Their full multiplication ranks are 3 and 4. The paired Betti dimensions
are therefore **24 and 20**, with formal dimension 14 in both cases.
This distinguishes the all-degree theorem from the old handle-rank test.
These algebraic test classes validate that prediction; the main theorem
has arbitrary-X quantifiers and is not specialized to this base.

The full exact fixtures also include zero curvature, the point and
hyperplane classes on P1/P2, rational mixed coefficients, exterior odd
cohomology of elliptic curves, P1 x E and E x E. The odd fixtures check
signs that the preceding even-base ring statement did not cover.

## Lean implementation

Two existing files change; no new wrapper module is introduced.
`GSTGradedWorldAlgebra.lean` gains **19 theorem drafts**:

- Actual closed-packet criterion, boundary criterion and square-zero differential.
- Surjective quotient/annihilator readout whose zero fiber is exactly boundaries.
- Nonzero annihilator-coordinate survival and exact finite dimension identities.
- Self-adjoint trace orthogonality and independence of quotient representatives.
- First-jet differential, square-zero law, correction obstruction, recovery and
  faithfulness of the full marked cup operator.
- Exact flat polynomial, all-degree loss identity and total-dimension evaluation.

`GSTSpatialFoldResearch.lean` checks integration with the existing fold work.
The complete graded duality-double theorem, geometric cochain comparison and
PID specialization argument remain hand proofs. The draft linear carrier
forgets degree only for its total dimension calculation; the hand proof and
experiments retain every absolute degree. No degree-one operator is silently
used as an all-degree Hodge charge.

## Reproducibility and evidence

```sh
python research/experiments/gst_all_degree_curvature_run.py
python /workspace/scratch/5d57a06b0962/gst_validate_manifest.py research/computations/gst_all_degree_curvature_20261103.manifest.json --root .
```

Python passes **16,261 exact assertions**, including the complete basis
multiplication/Leibniz tables, degree-by-degree cycle representatives and
Poincare trace ranks. Actual Wolfram passes **487 exact assertions**, using
its separate exponent-vector construction, NullSpace and MatrixRank.
All **13 complete result tables** agree, including every Betti number,
cup rank, pairing rank and specialization count. Both implementations
construct the actual first-jet matrices. The maximum cochain dimension is
64 and maximum first-jet dimension 128; p is 1 or 2 in these fixtures.
They verify those finite implementations, not the quantified hand theorem.

The Wolfram kernel reports version 15.0.1 for Linux x86 (64-bit),
July 2, 2026. Its complete compact JSON string is retained, reparsed and
compared without truncation. Remote runtime and process exit status are
not exposed and remain null. The local runner observes exit zero.
No random inputs, web-source inference or floating-point tolerance is used.

The v2 current-source manifest validates. Nineteen added declarations have
no proof-escape keyword; the parsed 748-node Lean import graph is acyclic.
LaTeX environments balance and whitespace checks pass. Three preexisting
lexical anomalies are unchanged against the starting revision. These checks
are lexical, not Lean compilation or a semantic audit of the entire repository.
Earlier manifests retain their historical meaning after these source edits.

[Exact local result](../computations/gst_all_degree_curvature_20261103.output.json),
[raw Wolfram evidence](../computations/gst_all_degree_curvature_wolfram_20261103.output.json),
[current manifest](../computations/gst_all_degree_curvature_20261103.manifest.json).

## Focused self-audit and continuation

| Obligation | Verdict and evidence |
| --- | --- |
| Full odd-base signs | Passed in the hand derivation and complete finite Leibniz tables |
| Perfect quotient/annihilator pairing | Passed by exact adjointness and finite-dimensional Poincare duality |
| All-degree rank formula and first defect | Passed by graded kernel/image dimensions, including alpha=0 |
| Ordinary cohomology base change | Replaced by the correct tensor/Tor exact sequence; false shortcut rejected |
| Higher parameter torsion/Bocksteins | Passed by explicit constant-rank splitting into free and z blocks |
| All-degree Hodge opposedness index | Out of scope without the required filtered realization; only Betti dimensions are claimed |
| New algebraic source from the rational family | Not supplied; no formal cochain is called a Chow class |

The all-degree cohomology and specialization subproblem is completed at
hand-proof level. The parameter family retains the exact alpha in its first
jet even when b1 is blind. Geometric selected/excess constructions and genuine
algebraization continue under the unchanged original-X target; this record
neither closes those routes nor replaces them with an equivalent existence
assumption. Lean compilation remains owner-run.
